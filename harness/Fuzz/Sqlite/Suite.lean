import LeanSwe.Sqlite.Interface
import LeanSwe.Sqlite.Raw.Interface
import LeanSwe.Sqlite.Model
import Fuzz.Common.Rng
import Fuzz.Common.Shrink
import Fuzz.Common.Coverage
import Fuzz.Common.Suite
import Fuzz.Sqlite.Trace
import Fuzz.Sqlite.Gen

namespace Fuzz.Sqlite

open Fuzz.Common
open LeanSwe.Sqlite

private structure OracleBugConfig where
  dropWhereOnTable? : Option String := none
  deriving Repr, BEq

private def errKindTag : SqliteErrorKind → String
  | .notFound => "notFound"
  | .busy => "busy"
  | .constraint => "constraint"
  | .misuse => "misuse"
  | .invalidInput => "invalidInput"
  | .ioError => "ioError"

private def requiredBuckets : Array CoverageBucket := #[
  bucket "validateConfig" "ok",
  bucket "validateConfig" "err.invalidInput",
  bucket "withDb" "ok.memory",
  bucket "withDb" "ok.file",
  bucket "withDb" "err.invalidInput",
  bucket "withDb" "err.notFound",
  bucket "withDb" "err.busy",
  bucket "withDb" "err.ioError",
  bucket "withTransaction" "ok.commit",
  bucket "withTransaction" "err.callerRollback",
  bucket "withTransaction" "err.thrownRollback",
  bucket "withTransaction" "err.busy",
  bucket "withTransaction" "err.constraint",
  bucket "withTransaction" "err.misuse",
  bucket "withTransaction" "err.invalidInput",
  bucket "withTransaction" "err.ioError",
  bucket "withTransaction" "err.rollbackCleanupFail",
  bucket "exec" "ok.createTable",
  bucket "exec" "ok.insert",
  bucket "exec" "ok.update",
  bucket "exec" "ok.delete",
  bucket "exec" "ok.txControl",
  bucket "exec" "err.invalidInput",
  bucket "exec" "err.misuse.multiOrEmpty",
  bucket "exec" "err.misuse.closedHandle",
  bucket "exec" "err.constraint.pkOrUnique",
  bucket "exec" "err.constraint.notNull",
  bucket "exec" "err.constraint.foreignKey",
  bucket "exec" "err.constraint.strictDatatype",
  bucket "exec" "err.busy",
  bucket "exec" "err.ioError.readonly",
  bucket "exec" "err.ioError.schemaOrTx",
  bucket "exec" "err.ioError.mismatch",
  bucket "query" "ok.empty",
  bucket "query" "ok.nonEmpty",
  bucket "query" "err.invalidInput",
  bucket "query" "err.misuse",
  bucket "query" "err.constraint",
  bucket "query" "err.busy",
  bucket "query" "err.ioError",
  bucket "queryOne" "ok.none",
  bucket "queryOne" "ok.some",
  bucket "queryOne" "err.invalidInput",
  bucket "queryOne" "err.misuse",
  bucket "queryOne" "err.constraint",
  bucket "queryOne" "err.busy",
  bucket "queryOne" "err.ioError",
  bucket "raw" "open.ok",
  bucket "raw" "open.err",
  bucket "raw" "prepare.ok",
  bucket "raw" "prepare.err",
  bucket "raw" "bind.ok",
  bucket "raw" "bind.err",
  bucket "raw" "step.row",
  bucket "raw" "step.done",
  bucket "raw" "step.err",
  bucket "raw" "finalize.ok",
  bucket "raw" "finalize.err",
  bucket "raw" "useAfterFinalize",
  bucket "raw" "closeBusy"
]

private def recordMismatch (mismatchRef : IO.Ref (Option String)) (msg : String) : IO Unit := do
  let cur ← mismatchRef.get
  if cur.isNone then
    mismatchRef.set (some msg)

private def hasActiveMismatch (mismatchRef : IO.Ref (Option String)) : IO Bool := do
  return (← mismatchRef.get).isSome

private def execBucketForOk (sql : String) : String :=
  match Model.parseCuratedSqlNoCapRaw sql with
  | .ok (.createTable _ _ _ _, _) => "ok.createTable"
  | .ok (.insert _ _ _, _) => "ok.insert"
  | .ok (.update _ _ _, _) => "ok.update"
  | .ok (.delete _ _, _) => "ok.delete"
  | .ok (.begin _, _) | .ok (.commit, _) | .ok (.rollback, _) => "ok.txControl"
  | .ok (.select _ _ _ _ _, _) => "ok.select"
  | .error _ => "ok.other"

private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def shimErrmsgFidelityOk (eReal eModel : SqliteError) : Bool :=
  let constraintOk :=
    if eReal.kind != .constraint then true
    else
      match eReal.sqliteCode with
      | some 1555 | some 2067 => hasSubstr eReal.message "UNIQUE constraint failed"
      | some 1299 => hasSubstr eReal.message "NOT NULL constraint failed"
      | some 787 => hasSubstr eReal.message "FOREIGN KEY constraint failed"
      | some 3091 => hasSubstr eReal.message "cannot store"
      | _ => true
  let tableDiagOk :=
    if eReal.kind == .ioError && eReal.sqliteCode == some 1 &&
        eModel.message.startsWith "no such table: " then
      eReal.message != "SQL logic error"
    else
      true
  constraintOk && tableDiagOk

private def errorsMatch (eReal eModel : SqliteError) : Bool :=
  eReal.kind == eModel.kind &&
  !eReal.message.isEmpty &&
  eReal.sqliteCode == eModel.sqliteCode &&
  eReal.path == eModel.path &&
  shimErrmsgFidelityOk eReal eModel

private def stripDelims (s : String) : String :=
  String.ofList (s.toList.filter fun c => c != ',' && c != '}' && c != '{' && c != ')' && c != '(')

private def splitWsTokens (s : String) : List String :=
  let s1 := s.replace "\n" " "
  let s2 := s1.replace "\r" " "
  let s3 := s2.replace "\t" " "
  (s3.splitOn " ").filter (!·.isEmpty)

private def extractKindCodeTokens (words : List String) (acc : List String) : List String :=
  match words with
  | [] => acc.reverse
  | "kind" :: ":=" :: k :: rest =>
    extractKindCodeTokens rest (("kind=" ++ stripDelims k) :: acc)
  | "sqliteCode" :: ":=" :: c :: n :: rest =>
    let cs := stripDelims c
    if cs == "none" then
      extractKindCodeTokens (n :: rest) ("code=none" :: acc)
    else if cs == "some" then
      extractKindCodeTokens rest (("code=" ++ stripDelims n) :: acc)
    else
      extractKindCodeTokens (n :: rest) acc
  | "sqliteCode" :: ":=" :: c :: rest =>
    let cs := stripDelims c
    if cs == "none" then
      extractKindCodeTokens rest ("code=none" :: acc)
    else
      extractKindCodeTokens rest acc
  | w :: rest =>
    let s := stripDelims w
    if s.startsWith "real=Except.ok" || s.startsWith "real=.ok" then
      extractKindCodeTokens rest ("real=ok" :: acc)
    else if s.startsWith "real=Except.error" then
      extractKindCodeTokens rest ("real=err" :: acc)
    else if s.startsWith "model=Except.ok" || s.startsWith "model=.ok" then
      extractKindCodeTokens rest ("model=ok" :: acc)
    else if s.startsWith "model=Except.error" then
      extractKindCodeTokens rest ("model=err" :: acc)
    else if s == "real=none" then
      extractKindCodeTokens rest ("real=none" :: acc)
    else if s.startsWith "real=some" then
      extractKindCodeTokens rest ("real=some" :: acc)
    else if s == "model=none" then
      extractKindCodeTokens rest ("model=none" :: acc)
    else if s.startsWith "model=some" then
      extractKindCodeTokens rest ("model=some" :: acc)
    else if s.endsWith "StepResult.row" then
      extractKindCodeTokens rest ("step=row" :: acc)
    else if s.endsWith "StepResult.done" then
      extractKindCodeTokens rest ("step=done" :: acc)
    else
      extractKindCodeTokens rest acc
termination_by words.length

private def mismatchTag (msg : String) : String :=
  let words := splitWsTokens msg
  let head := words.headD msg
  let pins := extractKindCodeTokens words []
  String.intercalate "|" (head :: pins)

private def execBucketForErr (isClosedHandle : Bool) (eReal _eModel : SqliteError) : String :=
  if isClosedHandle && eReal.kind == .misuse then
    "err.misuse.closedHandle"
  else
    match eReal.kind with
    | .invalidInput => "err.invalidInput"
    | .misuse => "err.misuse.multiOrEmpty"
    | .busy => "err.busy"
    | .constraint =>
      match eReal.sqliteCode with
      | some 1299 => "err.constraint.notNull"
      | some 787 => "err.constraint.foreignKey"
      | some 3091 => "err.constraint.strictDatatype"
      | _ => "err.constraint.pkOrUnique"
    | .ioError =>
      match eReal.sqliteCode with
      | some 8 | some 26 => "err.ioError.readonly"
      | some 20 => "err.ioError.mismatch"
      | _ => "err.ioError.schemaOrTx"
    | .notFound => "err.notFound"

private def queryBucketForErr (e : SqliteError) : String :=
  s!"err.{errKindTag e.kind}"

private def checkSelectOrderAgnostic (oracleCfg : OracleBugConfig)
    (realRows : Array SqliteRow) (st : Model.SqliteWorldState)
    (modelDb : DbHandle) (sql : String) (params : Array SqliteValue)
    (foreignKeys : Bool) : Bool :=
  match Model.visibleCatalogForDb st modelDb with
  | none => false
  | some cat =>
    match oracleCfg.dropWhereOnTable? with
    | some badTbl =>
      match Model.parseCuratedSqlRaw sql with
      | .ok (.select _ (some tblName) (some _) _ _, _) =>
        if Model.asciiLower tblName == Model.asciiLower badTbl then
          Model.allowedSelectRows cat s!"SELECT id FROM {tblName}" #[] realRows foreignKeys
        else
          Model.allowedSelectRows cat sql params realRows foreignKeys
      | _ => Model.allowedSelectRows cat sql params realRows foreignKeys
    | none => Model.allowedSelectRows cat sql params realRows foreignKeys

private def checkQueryOneOrderAgnostic (oracleCfg : OracleBugConfig)
    (realOpt : Option SqliteRow) (st : Model.SqliteWorldState)
    (modelDb : DbHandle) (sql : String) (params : Array SqliteValue)
    (foreignKeys : Bool) : Bool :=
  match Model.visibleCatalogForDb st modelDb with
  | none => false
  | some cat =>
    match oracleCfg.dropWhereOnTable? with
    | some badTbl =>
      match Model.parseCuratedSqlRaw sql with
      | .ok (.select _ (some tblName) (some _) _ _, _) =>
        if Model.asciiLower tblName == Model.asciiLower badTbl then
          Model.allowedQueryOneRow cat s!"SELECT id FROM {tblName}" #[] realOpt foreignKeys
        else
          Model.allowedQueryOneRow cat sql params realOpt foreignKeys
      | _ => Model.allowedQueryOneRow cat sql params realOpt foreignKeys
    | none => Model.allowedQueryOneRow cat sql params realOpt foreignKeys

private def fetchInsertWitnessRows
    (realDb : DbHandle) (target? : Option (String × String)) :
    IO (Except String (Option (List SqliteRow))) := do
  match target? with
  | none => return .ok none
  | some (tblName, ipkCol) =>
    match ← LeanSwe.Sqlite.query realDb s!"SELECT * FROM {tblName} ORDER BY {ipkCol} ASC" #[] with
    | .ok rows => return .ok (some rows.toList)
    | .error e => return .error s!"SQLITE_WITNESS_QUERY_FAILED tbl={tblName} err={repr e}"

private def runWriteWitnessStep
    (realDb modelDb : DbHandle) (st0 : Model.SqliteWorldState)
    (isClosedHandle : Bool) (sql : String) (params : Array SqliteValue)
    (fallback : IO (Except SqliteError Unit × Model.SqliteWorldState)) :
    IO (Except String (Except SqliteError Unit × Model.SqliteWorldState)) := do
  let target? := if isClosedHandle then none else Model.insertIpkTarget? st0 modelDb sql
  match ← fetchInsertWitnessRows realDb target? with
  | .error msg => return .error msg
  | .ok none => return .ok (← fallback)
  | .ok (some actualRows) =>
    let (mRes, st1?) := Model.stepInsertRelational st0 modelDb sql params actualRows
    match mRes, st1? with
    | .ok (), some st1 => return .ok (.ok (), st1)
    | .error e, _ => return .ok (.error e, st0)
    | .ok (), none => return .error s!"SQLITE_INSERT_WITNESS_INVALID sql={repr sql}"

private def runLeafLockstep
    (oracleCfg : OracleBugConfig)
    (realDb modelDb : DbHandle)
    (foreignKeys : Bool)
    (isClosedHandle : Bool)
    (op : LeafSqlOp)
    (worldRef : IO.Ref Model.SqliteWorldState)
    (trackerRef : IO.Ref CoverageTracker)
    (opsCountRef : IO.Ref Nat)
    (mismatchRef : IO.Ref (Option String)) : IO Unit := do
  opsCountRef.modify (· + 1)
  let st0 ← worldRef.get
  match op with
  | .exec sql params =>
    let resReal ← LeanSwe.Sqlite.exec realDb sql params
    let stmtsAfter ← LeanSwe.Sqlite.activeStmtCount
    if stmtsAfter != 0 then
      recordMismatch mismatchRef s!"LEAK_STMT_AFTER_EXEC sql={repr sql} activeStmtCount={stmtsAfter}"
      return
    match resReal with
    | .ok () =>
      match ← runWriteWitnessStep realDb modelDb st0 isClosedHandle sql params
          (pure ((Model.modelApi.exec modelDb sql params).run st0)) with
      | .error msg => recordMismatch mismatchRef msg
      | .ok (resModel, stNext) =>
        worldRef.set stNext
        match resModel with
        | .ok () => trackerRef.modify (·.record "exec" (execBucketForOk sql))
        | .error eModel =>
          recordMismatch mismatchRef
            s!"EXEC_OUTCOME_MISMATCH sql={repr sql} params={repr params} real=.ok model={repr (.error eModel : Except SqliteError Unit)}"
    | .error eReal =>
      let (resModel, stNext) := (Model.modelApi.exec modelDb sql params).run st0
      worldRef.set stNext
      match resModel with
      | .error eModel =>
        if !errorsMatch eReal eModel then
          recordMismatch mismatchRef
            s!"EXEC_ERR_MISMATCH sql={repr sql} params={repr params} real={repr eReal} model={repr eModel}"
        else
          trackerRef.modify (·.record "exec" (execBucketForErr isClosedHandle eReal eModel))
      | .ok () =>
        recordMismatch mismatchRef
          s!"EXEC_OUTCOME_MISMATCH sql={repr sql} params={repr params} real={repr resReal} model={repr resModel}"
  | .query sql params =>
    let resReal ← LeanSwe.Sqlite.query realDb sql params
    let stmtsAfter ← LeanSwe.Sqlite.activeStmtCount
    if stmtsAfter != 0 then
      recordMismatch mismatchRef s!"LEAK_STMT_AFTER_QUERY sql={repr sql} activeStmtCount={stmtsAfter}"
      return
    match resReal with
    | .ok realRows =>
      let target? := if isClosedHandle then none else Model.insertIpkTarget? st0 modelDb sql
      match ← fetchInsertWitnessRows realDb target? with
      | .error msg => recordMismatch mismatchRef msg
      | .ok (some actualRows) =>
        let (resModel, stNext?) := Model.stepInsertRelational st0 modelDb sql params actualRows
        match resModel, stNext? with
        | .ok (), some stNext =>
          worldRef.set stNext
          if !checkSelectOrderAgnostic oracleCfg realRows stNext modelDb sql params foreignKeys then
            recordMismatch mismatchRef
              s!"QUERY_ROWS_MISMATCH sql={repr sql} params={repr params} real={repr realRows} model=.ok #[]"
          else
            let b := if realRows.isEmpty then "ok.empty" else "ok.nonEmpty"
            trackerRef.modify (·.record "query" b)
        | _, _ =>
          recordMismatch mismatchRef
            s!"QUERY_OUTCOME_MISMATCH sql={repr sql} params={repr params} real={repr resReal} model={repr resModel}"
      | .ok none =>
        let (resModel, stNext) := (Model.modelApi.query modelDb sql params).run st0
        worldRef.set stNext
        match resModel with
        | .ok modelRows =>
          if !checkSelectOrderAgnostic oracleCfg realRows stNext modelDb sql params foreignKeys then
            recordMismatch mismatchRef
              s!"QUERY_ROWS_MISMATCH sql={repr sql} params={repr params} real={repr realRows} model={repr resModel}"
          else if !checkSelectOrderAgnostic oracleCfg modelRows stNext modelDb sql params foreignKeys then
            recordMismatch mismatchRef
              s!"QUERY_MODEL_ROWS_MISMATCH sql={repr sql} params={repr params} real={repr realRows} model={repr modelRows}"
          else
            let b := if realRows.isEmpty then "ok.empty" else "ok.nonEmpty"
            trackerRef.modify (·.record "query" b)
        | .error eModel =>
          recordMismatch mismatchRef
            s!"QUERY_OUTCOME_MISMATCH sql={repr sql} params={repr params} real={repr resReal} model={repr (.error eModel : Except SqliteError (Array SqliteRow))}"
    | .error eReal =>
      let (resModel, stNext) := (Model.modelApi.query modelDb sql params).run st0
      worldRef.set stNext
      match resModel with
      | .error eModel =>
        if !errorsMatch eReal eModel then
          recordMismatch mismatchRef
            s!"QUERY_ERR_MISMATCH sql={repr sql} params={repr params} real={repr eReal} model={repr eModel}"
        else
          trackerRef.modify (·.record "query" (queryBucketForErr eReal))
      | .ok _ =>
        recordMismatch mismatchRef
          s!"QUERY_OUTCOME_MISMATCH sql={repr sql} params={repr params} real={repr resReal} model={repr resModel}"
  | .queryOne sql params =>
    let resReal ← LeanSwe.Sqlite.queryOne realDb sql params
    let stmtsAfter ← LeanSwe.Sqlite.activeStmtCount
    if stmtsAfter != 0 then
      recordMismatch mismatchRef s!"LEAK_STMT_AFTER_QUERYONE sql={repr sql} activeStmtCount={stmtsAfter}"
      return
    match resReal with
    | .ok realOpt =>
      let target? := if isClosedHandle then none else Model.insertIpkTarget? st0 modelDb sql
      match ← fetchInsertWitnessRows realDb target? with
      | .error msg => recordMismatch mismatchRef msg
      | .ok (some actualRows) =>
        let (resModel, stNext?) := Model.stepInsertRelational st0 modelDb sql params actualRows
        match resModel, stNext? with
        | .ok (), some stNext =>
          worldRef.set stNext
          let rowsOk :=
            match realOpt with
            | none => checkQueryOneOrderAgnostic oracleCfg none stNext modelDb sql params foreignKeys
            | some r => checkQueryOneOrderAgnostic oracleCfg (some r) stNext modelDb sql params foreignKeys
          if !rowsOk then
            recordMismatch mismatchRef
              s!"QUERYONE_ROW_MISMATCH sql={repr sql} params={repr params} real={repr realOpt} model=none"
          else
            let b := if realOpt.isSome then "ok.some" else "ok.none"
            trackerRef.modify (·.record "queryOne" b)
        | _, _ =>
          recordMismatch mismatchRef
            s!"QUERYONE_OUTCOME_MISMATCH sql={repr sql} params={repr params} real={repr resReal} model={repr resModel}"
      | .ok none =>
        let (resModel, stNext) := (Model.modelApi.queryOne modelDb sql params).run st0
        worldRef.set stNext
        match resModel with
        | .ok modelOpt =>
          let rowsOk :=
            match realOpt, modelOpt with
            | none, none => checkQueryOneOrderAgnostic oracleCfg none stNext modelDb sql params foreignKeys
            | some r, some mr =>
              checkQueryOneOrderAgnostic oracleCfg (some r) stNext modelDb sql params foreignKeys &&
              checkQueryOneOrderAgnostic oracleCfg (some mr) stNext modelDb sql params foreignKeys
            | _, _ => false
          if !rowsOk then
            recordMismatch mismatchRef
              s!"QUERYONE_ROW_MISMATCH sql={repr sql} params={repr params} real={repr realOpt} model={repr modelOpt}"
          else
            let b := if realOpt.isSome then "ok.some" else "ok.none"
            trackerRef.modify (·.record "queryOne" b)
        | .error eModel =>
          recordMismatch mismatchRef
            s!"QUERYONE_OUTCOME_MISMATCH sql={repr sql} params={repr params} real={repr resReal} model={repr (.error eModel : Except SqliteError (Option SqliteRow))}"
    | .error eReal =>
      let (resModel, stNext) := (Model.modelApi.queryOne modelDb sql params).run st0
      worldRef.set stNext
      match resModel with
      | .error eModel =>
        if !errorsMatch eReal eModel then
          recordMismatch mismatchRef
            s!"QUERYONE_ERR_MISMATCH sql={repr sql} params={repr params} real={repr eReal} model={repr eModel}"
        else
          trackerRef.modify (·.record "queryOne" (queryBucketForErr eReal))
      | .ok _ =>
        recordMismatch mismatchRef
          s!"QUERYONE_OUTCOME_MISMATCH sql={repr sql} params={repr params} real={repr resReal} model={repr resModel}"

private def runTxLockstep
    (oracleCfg : OracleBugConfig)
    (realDb modelDb : DbHandle)
    (foreignKeys : Bool)
    (txOps : Array LeafSqlOp)
    (exitMode : ExitMode)
    (worldRef : IO.Ref Model.SqliteWorldState)
    (trackerRef : IO.Ref CoverageTracker)
    (opsCountRef : IO.Ref Nat)
    (mismatchRef : IO.Ref (Option String)) : IO Unit := do
  opsCountRef.modify (· + 1)
  let enteredRef ← IO.mkRef false
  let threwMsgRef ← IO.mkRef (none : Option String)
  let txResReal ←
    try
      LeanSwe.Sqlite.withTransaction realDb fun txRealDb => do
        let st0 ← worldRef.get
        let (begRes, st1) := (Model.modelApi.exec modelDb "BEGIN IMMEDIATE" #[]).run st0
        match begRes with
        | .error eModel =>
          recordMismatch mismatchRef
            s!"WITH_TX_ENTERED_BUT_MODEL_BEGIN_ERR model={repr eModel}"
          return .error eModel
        | .ok () =>
          enteredRef.set true
          worldRef.set st1
          for op in txOps do
            if !(← hasActiveMismatch mismatchRef) then
              runLeafLockstep oracleCfg txRealDb modelDb foreignKeys false op worldRef trackerRef opsCountRef mismatchRef
          match exitMode with
          | .returnOk => return .ok ()
          | .returnCallerErr err => return .error err
          | .throwIoUserError msg => throw (IO.userError msg)
    catch e =>
      threwMsgRef.set (some (toString e))
      pure (.ok ())
  let entered ← enteredRef.get
  let threwMsg? ← threwMsgRef.get
  let stmtsAfter ← LeanSwe.Sqlite.activeStmtCount
  if stmtsAfter != 0 then
    recordMismatch mismatchRef s!"LEAK_STMT_AFTER_WITHTX activeStmtCount={stmtsAfter}"
    return
  if !entered then
    match threwMsg? with
    | some msg =>
      recordMismatch mismatchRef s!"WITH_TX_UNEXPECTED_THROW_BEFORE_BODY msg={msg}"
    | none =>
      let st0 ← worldRef.get
      let (begRes, st1) := (Model.modelApi.exec modelDb "BEGIN IMMEDIATE" #[]).run st0
      worldRef.set st1
      match txResReal, begRes with
      | .error eReal, .error eModel =>
        if !errorsMatch eReal eModel then
          recordMismatch mismatchRef
            s!"WITH_TX_BEGIN_ERR_MISMATCH real={repr eReal} model={repr eModel}"
        else
          trackerRef.modify (·.record "withTransaction" s!"err.{errKindTag eReal.kind}")
      | _, _ =>
        recordMismatch mismatchRef
          s!"WITH_TX_BEGIN_MISMATCH real={repr txResReal} model={repr begRes}"
  else
    match exitMode with
    | .returnOk =>
      match threwMsg? with
      | some msg =>
        let (_, stRb) := (Model.modelApi.exec modelDb "ROLLBACK" #[]).run (← worldRef.get)
        worldRef.set stRb
        recordMismatch mismatchRef s!"WITH_TX_RETURNOK_THREW msg={msg}"
      | none =>
        let stBeforeCommit ← worldRef.get
        let (comRes, stAfterCommit) := (Model.modelApi.exec modelDb "COMMIT" #[]).run stBeforeCommit
        match comRes with
        | .ok () =>
          worldRef.set stAfterCommit
          match txResReal with
          | .ok () => trackerRef.modify (·.record "withTransaction" "ok.commit")
          | .error eReal =>
            recordMismatch mismatchRef
              s!"WITH_TX_COMMIT_MISMATCH real={repr eReal} model=.ok"
        | .error eModel =>
          let (rbRes, stAfterRb) := (Model.modelApi.exec modelDb "ROLLBACK" #[]).run stAfterCommit
          worldRef.set stAfterRb
          match txResReal with
          | .error eReal =>
            if !errorsMatch eReal eModel then
              recordMismatch mismatchRef
                s!"WITH_TX_COMMIT_ERR_MISMATCH real={repr eReal} model={repr eModel}"
            else
              if rbRes.isOk then pure ()
              else trackerRef.modify (·.record "withTransaction" "err.rollbackCleanupFail")
              trackerRef.modify (·.record "withTransaction" s!"err.{errKindTag eReal.kind}")
          | .ok () =>
            recordMismatch mismatchRef
              s!"WITH_TX_COMMIT_ERR_MISMATCH real=.ok model={repr eModel}"
    | .returnCallerErr err =>
      let (rbRes, stAfterRb) := (Model.modelApi.exec modelDb "ROLLBACK" #[]).run (← worldRef.get)
      worldRef.set stAfterRb
      match threwMsg? with
      | some msg => recordMismatch mismatchRef s!"WITH_TX_CALLER_ERR_THREW msg={msg}"
      | none =>
        match txResReal with
        | .ok () =>
          recordMismatch mismatchRef
            s!"WITH_TX_CALLER_ERR_MISMATCH real=ok expected={repr err}"
        | .error eGot =>
          if eGot != err then
            recordMismatch mismatchRef
              s!"WITH_TX_CALLER_ERR_MISMATCH real={repr eGot} expected={repr err}"
          else
            if rbRes.isOk then
              trackerRef.modify (·.record "withTransaction" "err.callerRollback")
            else
              trackerRef.modify (·.record "withTransaction" "err.rollbackCleanupFail")
            trackerRef.modify (·.record "withTransaction" s!"err.{errKindTag err.kind}")
    | .throwIoUserError _ =>
      let (_, stAfterRb) := (Model.modelApi.exec modelDb "ROLLBACK" #[]).run (← worldRef.get)
      worldRef.set stAfterRb
      match threwMsg? with
      | none => recordMismatch mismatchRef s!"WITH_TX_THROW_DID_NOT_PROPAGATE res={repr txResReal}"
      | some _ => trackerRef.modify (·.record "withTransaction" "err.thrownRollback")

private def withDbLockstep
    (epDir : System.FilePath)
    (target : TargetSpec)
    (cfg : OpenConfig)
    (baseActiveDbs : Nat)
    (exitMode : ExitMode)
    (worldRef : IO.Ref Model.SqliteWorldState)
    (trackerRef : IO.Ref CoverageTracker)
    (opsCountRef : IO.Ref Nat)
    (mismatchRef : IO.Ref (Option String))
    (escapedRef : IO.Ref (Array DbHandle))
    (body : DbHandle → DbHandle → IO (Except SqliteError Unit)) : IO Unit := do
  opsCountRef.modify (· + 1)
  let resolvedPath := target.resolve epDir
  let valRes := Model.validateConfigWith Model.mapRawError cfg
  let enteredRef ← IO.mkRef false
  let modelDbRef ← IO.mkRef (none : Option DbHandle)
  let threwMsgRef ← IO.mkRef (none : Option String)
  let resReal ←
    try
      LeanSwe.Sqlite.withDb resolvedPath cfg fun realDb => do
        escapedRef.modify (·.push realDb)
        let st0 ← worldRef.get
        let (openRes, st1) := Model.modelRawOps.openDb resolvedPath cfg st0
        match openRes with
        | .error eModel =>
          recordMismatch mismatchRef
            s!"WITHDB_ENTERED_BUT_MODEL_OPEN_ERR path={repr resolvedPath} cfg={repr cfg} model={repr eModel}"
          return .error eModel
        | .ok modelDb =>
          enteredRef.set true
          modelDbRef.set (some modelDb)
          worldRef.set st1
          body realDb modelDb
    catch e =>
      threwMsgRef.set (some (toString e))
      pure (.ok ())
  let dbCountAfter ← LeanSwe.Sqlite.activeDbCount
  let stmtCountAfter ← LeanSwe.Sqlite.activeStmtCount
  if dbCountAfter != baseActiveDbs || stmtCountAfter != 0 then
    recordMismatch mismatchRef
      s!"HANDLE_LEAK_AFTER_WITHDB path={repr resolvedPath} dbCount={dbCountAfter} expectedDb={baseActiveDbs} stmtCount={stmtCountAfter}"
    return
  let entered ← enteredRef.get
  let threwMsg? ← threwMsgRef.get
  if !entered then
    match threwMsg? with
    | some msg =>
      recordMismatch mismatchRef s!"WITHDB_UNEXPECTED_THROW_BEFORE_BODY msg={msg}"
    | none =>
      match valRes with
      | .error eVal =>
        match resReal with
        | .error eReal =>
          if !errorsMatch eReal eVal then
            recordMismatch mismatchRef
              s!"WITHDB_VALIDATE_ERR_MISMATCH path={repr resolvedPath} cfg={repr cfg} real={repr eReal} val={repr eVal}"
          else
            trackerRef.modify (·.record "withDb" s!"err.{errKindTag eReal.kind}")
        | .ok _ =>
          recordMismatch mismatchRef
            s!"WITHDB_VALIDATE_BYPASS path={repr resolvedPath} cfg={repr cfg} expected={repr eVal}"
      | .ok _ =>
        let st0 ← worldRef.get
        let (openRes, st1) := Model.modelRawOps.openDb resolvedPath cfg st0
        worldRef.set st1
        match openRes with
        | .error eModel =>
          match resReal with
          | .error eReal =>
            if !errorsMatch eReal eModel then
              recordMismatch mismatchRef
                s!"WITHDB_OPEN_ERR_MISMATCH path={repr resolvedPath} cfg={repr cfg} real={repr eReal} model={repr eModel}"
            else
              trackerRef.modify (·.record "withDb" s!"err.{errKindTag eReal.kind}")
          | .ok _ =>
            recordMismatch mismatchRef
              s!"WITHDB_OPEN_BYPASS path={repr resolvedPath} cfg={repr cfg} expected={repr eModel}"
        | .ok mDb =>
          let (_, stClose) := Model.modelRawOps.closeDb mDb st1
          worldRef.set stClose
          recordMismatch mismatchRef
            s!"WITHDB_REAL_FAILED_OPEN_MODEL_OK path={repr resolvedPath} cfg={repr cfg} real={repr resReal}"
  else
    match ← modelDbRef.get with
    | none =>
      recordMismatch mismatchRef "INTERNAL_MISSING_MODEL_DB"
    | some modelDb =>
      let stBeforeClose ← worldRef.get
      let (closeRes, stAfterClose) := Model.modelRawOps.closeDb modelDb stBeforeClose
      worldRef.set stAfterClose
      match closeRes with
      | .error _ =>
        recordMismatch mismatchRef s!"WITHDB_MODEL_CLOSE_ERR closeRes={repr closeRes}"
      | .ok () =>
        let memTag := match target with | .memory => "ok.memory" | _ => "ok.file"
        match exitMode with
        | .returnOk =>
          match threwMsg? with
          | some msg =>
            recordMismatch mismatchRef s!"WITHDB_RETURNOK_THREW msg={msg}"
          | none =>
            match resReal with
            | .error eReal =>
              recordMismatch mismatchRef s!"WITHDB_RETURNOK_ERR real={repr eReal}"
            | .ok () =>
              trackerRef.modify (·.record "withDb" memTag)
        | .returnCallerErr err =>
          match threwMsg? with
          | some msg =>
            recordMismatch mismatchRef s!"WITHDB_CALLER_ERR_THREW msg={msg}"
          | none =>
            match resReal with
            | .ok () =>
              recordMismatch mismatchRef s!"WITHDB_CALLER_ERR_MISSING expected={repr err}"
            | .error eGot =>
              if eGot != err then
                recordMismatch mismatchRef
                  s!"WITHDB_CALLER_ERR_MISMATCH real={repr eGot} expected={repr err}"
              else
                trackerRef.modify (·.record "withDb" memTag)
        | .throwIoUserError msg =>
          match threwMsg? with
          | none =>
            recordMismatch mismatchRef s!"WITHDB_THROW_DID_NOT_PROPAGATE res={repr resReal}"
          | some gotMsg =>
            if !(gotMsg.endsWith msg) then
              recordMismatch mismatchRef
                s!"WITHDB_THROW_MSG_MISMATCH got={repr gotMsg} expectedSuffix={repr msg}"
            else
              trackerRef.modify (·.record "withDb" memTag)

private def runWithDbSession
    (epDir : System.FilePath)
    (oracleCfg : OracleBugConfig)
    (target : TargetSpec)
    (cfg : OpenConfig)
    (ops : Array DbConnOp)
    (exitMode : ExitMode)
    (worldRef : IO.Ref Model.SqliteWorldState)
    (trackerRef : IO.Ref CoverageTracker)
    (opsCountRef : IO.Ref Nat)
    (mismatchRef : IO.Ref (Option String))
    (escapedRef : IO.Ref (Array DbHandle)) : IO Unit :=
  withDbLockstep epDir target cfg 0 exitMode worldRef trackerRef opsCountRef mismatchRef escapedRef
    fun db1 modelDb1 => do
      for op in ops do
        if !(← hasActiveMismatch mismatchRef) then
          match op with
          | .leaf leafOp =>
            runLeafLockstep oracleCfg db1 modelDb1 cfg.foreignKeys false leafOp worldRef trackerRef opsCountRef mismatchRef
          | .withTx txOps txExit =>
            runTxLockstep oracleCfg db1 modelDb1 cfg.foreignKeys txOps txExit worldRef trackerRef opsCountRef mismatchRef
          | .nestedWithDb t2 cfg2 dualOps exitMode2 =>
            withDbLockstep epDir t2 cfg2 1 exitMode2 worldRef trackerRef opsCountRef mismatchRef escapedRef
              fun db2 modelDb2 => do
                for (useSecond, dOp) in dualOps do
                  if !(← hasActiveMismatch mismatchRef) then
                    let (rDb, mDb, fkFlag) :=
                      if useSecond then (db2, modelDb2, cfg2.foreignKeys)
                      else (db1, modelDb1, cfg.foreignKeys)
                    runLeafLockstep oracleCfg rDb mDb fkFlag false dOp worldRef trackerRef opsCountRef mismatchRef
                match exitMode2 with
                | .returnOk => return (.ok () : Except SqliteError Unit)
                | .returnCallerErr e => return (.error e : Except SqliteError Unit)
                | .throwIoUserError msg => throw (IO.userError msg)
      match exitMode with
      | .returnOk => return (.ok () : Except SqliteError Unit)
      | .returnCallerErr e => return (.error e : Except SqliteError Unit)
      | .throwIoUserError msg => throw (IO.userError msg)

private def resolveClosedRef (escaped : Array DbHandle) : ClosedHandleRef → DbHandle
  | .zero => { id := 0 }
  | .huge => { id := 999999 }
  | .raw id => { id := id }
  | .escaped idx =>
    if escaped.isEmpty then { id := 777777 }
    else escaped.getD (idx % escaped.size) { id := 777777 }

private structure EpisodeTemplate where
  roBytes : ByteArray
  walRoBytes : ByteArray
  roCat : Model.DbCatalog
  walRoCat : Model.DbCatalog

private def forceRemoveDirAll (dir : System.FilePath) : IO Unit := do
  try
    IO.FS.removeDirAll dir
  catch _ =>
    pure ()
  let stillExists ← try dir.pathExists catch _ => pure true
  if stillExists then
    try
      let _ ← IO.Process.output
        { cmd := "sh"
          args := #["-c", "chmod -R u+rwX -- \"$1\" 2>/dev/null; rm -rf -- \"$1\"", "sh", dir.toString]
          stdin := .null }
    catch _ =>
      pure ()

private def prepareEpisodeTemplate (rootDir : System.FilePath) : IO EpisodeTemplate := do
  let tplDir := rootDir / "_tpl"
  IO.FS.createDirAll tplDir
  let roPath := (tplDir / "ro0444.sqlite").toString
  let walRoPath := (tplDir / "walro0444.sqlite").toString
  try
    let initRes ← LeanSwe.Sqlite.withDb roPath { walMode := false } fun db =>
      LeanSwe.Sqlite.exec db "CREATE TABLE ro_seed(id INTEGER PRIMARY KEY, x INT)" #[]
    if let .error e := initRes then
      throw (IO.userError s!"SQLITE_FUZZ_TPL_RO_FAILED: {repr e}")
    let initWalRes ← LeanSwe.Sqlite.withDb walRoPath { walMode := true } fun db =>
      LeanSwe.Sqlite.exec db "CREATE TABLE ro_seed(id INTEGER PRIMARY KEY, x INT)" #[]
    if let .error e := initWalRes then
      throw (IO.userError s!"SQLITE_FUZZ_TPL_WALRO_FAILED: {repr e}")
    let roBytes ← IO.FS.readBinFile (tplDir / "ro0444.sqlite")
    let walRoBytes ← IO.FS.readBinFile (tplDir / "walro0444.sqlite")
    let st0 : Model.SqliteWorldState := { existingDirs := ["/", tplDir.toString] }
    let (mRes, st2) := (Model.modelApi.withDb roPath { walMode := false } fun mDb =>
      Model.modelApi.exec mDb "CREATE TABLE ro_seed(id INTEGER PRIMARY KEY, x INT)" #[]).run st0
    if let .error e := mRes then
      throw (IO.userError s!"SQLITE_FUZZ_TPL_MODEL_RO_FAILED: {repr e}")
    let (mWalRes, st3) := (Model.modelApi.withDb walRoPath { walMode := true } fun mDb =>
      Model.modelApi.exec mDb "CREATE TABLE ro_seed(id INTEGER PRIMARY KEY, x INT)" #[]).run st2
    if let .error e := mWalRes then
      throw (IO.userError s!"SQLITE_FUZZ_TPL_MODEL_WALRO_FAILED: {repr e}")
    let findCat := fun (targetPath : String) =>
      match st3.files.find? (fun (p, _) => p == targetPath) with
      | some (_, .dbFile _ _ _ cat) => cat
      | _ => {}
    return { roBytes := roBytes, walRoBytes := walRoBytes,
             roCat := findCat roPath, walRoCat := findCat walRoPath }
  finally
    forceRemoveDirAll tplDir

private def episodeNeedsSym45 (ep : SqliteEpisode) : Bool :=
  let targetHas45 : TargetSpec → Bool
    | .sym45 => true
    | .epSuffix suf => hasSubstr suf "sym_45.sqlite"
    | .epUri _ suf => hasSubstr suf "sym_45.sqlite"
    | .raw p => hasSubstr p "sym_45.sqlite"
    | _ => false
  ep.any fun
    | .withDbSession tgt _ ops _ =>
      targetHas45 tgt || ops.any fun
        | .nestedWithDb t2 _ _ _ => targetHas45 t2
        | _ => false
    | .rawSession tgt _ ops =>
      targetHas45 tgt || ops.any fun
        | .rawPeerExec ptgt _ _ _ => targetHas45 ptgt
        | _ => false
    | _ => false

private def setupEpisodeDir (tpl : EpisodeTemplate) (withSym45 : Bool)
    (epDir : System.FilePath) : IO Model.SqliteWorldState := do
  IO.FS.createDirAll epDir
  IO.FS.createDirAll (epDir / "subdir")
  let d200a := String.ofList (List.replicate 200 'a')
  let d200b := String.ofList (List.replicate 200 'b')
  IO.FS.createDirAll (epDir / d200a / d200b)
  let corruptBytes : ByteArray := ByteArray.mk (Array.replicate 128 0xAA)
  IO.FS.writeBinFile (epDir / "corrupt.sqlite") corruptBytes
  let roPath := (epDir / "ro0444.sqlite").toString
  let walRoPath := (epDir / "walro0444.sqlite").toString
  IO.FS.writeBinFile (epDir / "ro0444.sqlite") tpl.roBytes
  IO.FS.writeBinFile (epDir / "walro0444.sqlite") tpl.walRoBytes
  let roMode : IO.FileRight := { user := { read := true }, group := { read := true }, other := { read := true } }
  IO.setAccessRights (epDir / "ro0444.sqlite") roMode
  IO.setAccessRights (epDir / "walro0444.sqlite") roMode
  let symScript :=
    "cd \"$1\" && ln -s \"$1/db0.sqlite\" sym_db0.sqlite && ln -s sym_db0.sqlite sym_deep.sqlite && ln -s sym_loop_b.sqlite sym_loop_a.sqlite && ln -s sym_loop_a.sqlite sym_loop_b.sqlite && ln -s ../db0.sqlite subdir/sym_rel_db0.sqlite && ln -s subdir sym_dir && ln -s dangling_target.sqlite sym_dangling.sqlite" ++
    (if withSym45 then " && ln -s db0.sqlite sym_01.sqlite && i=2; while [ $i -le 45 ]; do p=$((i-1)); fn=$(printf 'sym_%02d.sqlite' \"$i\"); pn=$(printf 'sym_%02d.sqlite' \"$p\"); ln -s \"$pn\" \"$fn\"; i=$((i+1)); done" else "")
  let out ← IO.Process.output { cmd := "sh", args := #["-c", symScript, "sh", epDir.toString], stdin := .null }
  if out.exitCode != 0 then
    throw (IO.userError s!"SQLITE_FUZZ_LN_FAILED {epDir}: {out.stderr}")
  let baseFiles : List (String × Model.FileNode) :=
    [ (roPath, .dbFile false true 1 tpl.roCat)
    , (walRoPath, .dbFile true true 1 tpl.walRoCat)
    , ((epDir / "subdir").toString, .directory)
    , ((epDir / "corrupt.sqlite").toString, .corruptFile) ]
  let baseSyms : List (String × String) :=
    [ ((epDir / "sym_db0.sqlite").toString, (epDir / "db0.sqlite").toString)
    , ((epDir / "sym_deep.sqlite").toString, "sym_db0.sqlite")
    , ((epDir / "sym_loop_a.sqlite").toString, "sym_loop_b.sqlite")
    , ((epDir / "sym_loop_b.sqlite").toString, "sym_loop_a.sqlite")
    , ((epDir / "subdir" / "sym_rel_db0.sqlite").toString, "../db0.sqlite")
    , ((epDir / "sym_dir").toString, "subdir")
    , ((epDir / "sym_dangling.sqlite").toString, "dangling_target.sqlite") ]
  let extraSyms : List (String × String) :=
    if !withSym45 then []
    else
      let pad2 (n : Nat) : String := if n < 10 then s!"0{n}" else s!"{n}"
      ((epDir / "sym_01.sqlite").toString, "db0.sqlite") ::
        (List.range 44).map fun k =>
          let i := k + 2
          ((epDir / s!"sym_{pad2 i}.sqlite").toString, s!"sym_{pad2 (i - 1)}.sqlite")
  return { existingDirs := ["/", epDir.toString, (epDir / d200a).toString, (epDir / d200a / d200b).toString],
           files := baseFiles, symlinks := baseSyms ++ extraSyms }

private def cleanupEpisodeDir (epDir : System.FilePath) : IO Unit := do
  let rwMode : IO.FileRight :=
    { user := { read := true, write := true }
      group := { read := true }
      other := { read := true } }
  for name in #["ro0444.sqlite", "walro0444.sqlite"] do
    try
      if ← (epDir / name).pathExists then
        IO.setAccessRights (epDir / name) rwMode
    catch _ => pure ()
  forceRemoveDirAll epDir

private def stepResultMatches (a b : Except SqliteError Raw.StepResult) : Bool :=
  match a, b with
  | .ok .done, .ok .done => true
  | .ok (.row r1), .ok (.row r2) => Model.sqliteRowBitEq r1 r2
  | .ok _, .ok _ => false
  | .error e1, .error e2 => errorsMatch e1 e2
  | _, _ => false

private def runRawSessionLockstep
    (epDir : System.FilePath)
    (target : TargetSpec)
    (cfg : OpenConfig)
    (ops : Array RawStepOp)
    (worldRef : IO.Ref Model.SqliteWorldState)
    (trackerRef : IO.Ref CoverageTracker)
    (opsCountRef : IO.Ref Nat)
    (mismatchRef : IO.Ref (Option String)) : IO Unit := do
  opsCountRef.modify (· + 1)
  let resolvedPath := target.resolve epDir
  let rOpen ← LeanSwe.Sqlite.Raw.openDb resolvedPath cfg
  let st0 ← worldRef.get
  let (mOpen, st1) := Model.modelRawOps.openDb resolvedPath cfg st0
  worldRef.set st1
  match rOpen, mOpen with
  | .error eReal, .error eModel =>
    if !errorsMatch eReal eModel then
      recordMismatch mismatchRef
        s!"RAW_OPEN_ERR_MISMATCH path={repr resolvedPath} cfg={repr cfg} real={repr eReal} model={repr eModel}"
    else
      trackerRef.modify (·.record "raw" "open.err")
  | .ok rDb, .error eModel =>
    let _ ← LeanSwe.Sqlite.Raw.closeDb rDb
    recordMismatch mismatchRef
      s!"RAW_OPEN_OUTCOME_MISMATCH path={repr resolvedPath} cfg={repr cfg} real=.ok model={repr eModel}"
  | .error eReal, .ok mDb =>
    let (_, stClose) := Model.modelRawOps.closeDb mDb st1
    worldRef.set stClose
    recordMismatch mismatchRef
      s!"RAW_OPEN_OUTCOME_MISMATCH path={repr resolvedPath} cfg={repr cfg} real={repr eReal} model=.ok"
  | .ok realDb, .ok modelDb =>
    trackerRef.modify (·.record "raw" "open.ok")
    let realSlotsRef ← IO.mkRef (#[(none : Option (StmtHandle × Bool)), none] : Array (Option (StmtHandle × Bool)))
    let modelSlotsRef ← IO.mkRef (#[(none : Option (StmtHandle × Bool)), none] : Array (Option (StmtHandle × Bool)))
    let forgedStmt : StmtHandle := { id := 999999, dbId := realDb.id }
    try
      for op in ops do
        if !(← hasActiveMismatch mismatchRef) then
          opsCountRef.modify (· + 1)
          let rSlots ← realSlotsRef.get
          let mSlots ← modelSlotsRef.get
          match op with
          | .prepare slot sql =>
            let idx := slot % 2
            match rSlots.getD idx none, mSlots.getD idx none with
            | some (oldR, true), some (oldM, true) =>
              let rOldF ← LeanSwe.Sqlite.Raw.finalize oldR
              let stC ← worldRef.get
              let (mOldF, stC') := Model.modelRawOps.finalize oldM stC
              worldRef.set stC'
              realSlotsRef.set (rSlots.setIfInBounds idx none)
              modelSlotsRef.set (mSlots.setIfInBounds idx none)
              match rOldF, mOldF with
              | .ok (), .ok () => pure ()
              | .error e1, .error e2 =>
                if !errorsMatch e1 e2 then
                  recordMismatch mismatchRef
                    s!"RAW_OVERWRITE_FIN_MISMATCH real={repr e1} model={repr e2}"
              | _, _ =>
                recordMismatch mismatchRef
                  s!"RAW_OVERWRITE_FIN_MISMATCH real={repr rOldF} model={repr mOldF}"
            | _, _ => pure ()
            if !(← hasActiveMismatch mismatchRef) then
              let rPrep ← LeanSwe.Sqlite.Raw.prepare realDb sql
              let stNow ← worldRef.get
              let (mPrep, stNext) := Model.modelRawOps.prepare modelDb sql stNow
              worldRef.set stNext
              match rPrep, mPrep with
              | .ok rs, .ok ms =>
                trackerRef.modify (·.record "raw" "prepare.ok")
                realSlotsRef.set ((← realSlotsRef.get).setIfInBounds idx (some (rs, true)))
                modelSlotsRef.set ((← modelSlotsRef.get).setIfInBounds idx (some (ms, true)))
              | .error e1, .error e2 =>
                if !errorsMatch e1 e2 then
                  recordMismatch mismatchRef
                    s!"RAW_PREP_ERR_MISMATCH sql={repr sql} real={repr e1} model={repr e2}"
                else
                  trackerRef.modify (·.record "raw" "prepare.err")
              | .ok rs, .error e2 =>
                let _ ← LeanSwe.Sqlite.Raw.finalize rs
                recordMismatch mismatchRef
                  s!"RAW_PREP_OUTCOME_MISMATCH sql={repr sql} real=.ok model={repr e2}"
              | .error e1, .ok ms =>
                worldRef.set (Model.modelRawOps.finalize ms stNext).2
                recordMismatch mismatchRef
                  s!"RAW_PREP_OUTCOME_MISMATCH sql={repr sql} real={repr e1} model=.ok"
          | .bind slot ps =>
            let idx := slot % 2
            let (rs, rLive) := match rSlots.getD idx none with | some p => p | none => (forgedStmt, false)
            let (ms, _) := match mSlots.getD idx none with | some p => p | none => (forgedStmt, false)
            if !rLive && (rSlots.getD idx none).isSome then
              trackerRef.modify (·.record "raw" "useAfterFinalize")
            let rB ← LeanSwe.Sqlite.Raw.bind rs ps
            let stNow ← worldRef.get
            let (mB, stNext) := Model.modelRawOps.bind ms ps stNow
            worldRef.set stNext
            match rB, mB with
            | .ok (), .ok () => trackerRef.modify (·.record "raw" "bind.ok")
            | .error e1, .error e2 =>
              if !errorsMatch e1 e2 then
                recordMismatch mismatchRef s!"RAW_BIND_ERR_MISMATCH real={repr e1} model={repr e2}"
              else
                trackerRef.modify (·.record "raw" "bind.err")
            | _, _ =>
              recordMismatch mismatchRef s!"RAW_BIND_OUTCOME_MISMATCH real={repr rB} model={repr mB}"
          | .step slot =>
            let idx := slot % 2
            let (rs, rLive) := match rSlots.getD idx none with | some p => p | none => (forgedStmt, false)
            let (ms, _) := match mSlots.getD idx none with | some p => p | none => (forgedStmt, false)
            if !rLive && (rSlots.getD idx none).isSome then
              trackerRef.modify (·.record "raw" "useAfterFinalize")
            let rS ← LeanSwe.Sqlite.Raw.step rs
            let stNow ← worldRef.get
            let witnessRows? ←
              match rS, rLive with
              | .ok .done, true =>
                match ← fetchInsertWitnessRows realDb (Model.stmtInsertIpkTarget? stNow ms) with
                | .ok opt => pure opt
                | .error msg =>
                  recordMismatch mismatchRef msg
                  pure none
              | _, _ => pure none
            if !(← hasActiveMismatch mismatchRef) then
              let (mS, stNext?) := Model.stepRawRelational ms rS stNow witnessRows?
              if let some stNext := stNext? then
                worldRef.set stNext
              if !stepResultMatches rS mS || stNext?.isNone then
                recordMismatch mismatchRef s!"RAW_STEP_MISMATCH real={repr rS} model={repr mS}"
              else
                match rS with
                | .ok .done => trackerRef.modify (·.record "raw" "step.done")
                | .ok (.row _) => trackerRef.modify (·.record "raw" "step.row")
                | .error _ => trackerRef.modify (·.record "raw" "step.err")
          | .finalize slot =>
            let idx := slot % 2
            let (rs, rLive) := match rSlots.getD idx none with | some p => p | none => (forgedStmt, false)
            let (ms, _) := match mSlots.getD idx none with | some p => p | none => (forgedStmt, false)
            if !rLive && (rSlots.getD idx none).isSome then
              trackerRef.modify (·.record "raw" "useAfterFinalize")
            let rF ← LeanSwe.Sqlite.Raw.finalize rs
            let stNow ← worldRef.get
            let (mF, stNext) := Model.modelRawOps.finalize ms stNow
            worldRef.set stNext
            if let some (h, true) := rSlots.getD idx none then
              realSlotsRef.set (rSlots.setIfInBounds idx (some (h, false)))
            if let some (h, true) := mSlots.getD idx none then
              modelSlotsRef.set (mSlots.setIfInBounds idx (some (h, false)))
            match rF, mF with
            | .ok (), .ok () => trackerRef.modify (·.record "raw" "finalize.ok")
            | .error e1, .error e2 =>
              if !errorsMatch e1 e2 then
                recordMismatch mismatchRef s!"RAW_FIN_ERR_MISMATCH real={repr e1} model={repr e2}"
              else
                trackerRef.modify (·.record "raw" "finalize.err")
            | _, _ =>
              recordMismatch mismatchRef s!"RAW_FIN_OUTCOME_MISMATCH real={repr rF} model={repr mF}"
          | .peerExec sql ps =>
            let peerCfg : OpenConfig := { walMode := cfg.walMode, busyTimeoutMs := 0, foreignKeys := cfg.foreignKeys }
            if resolvedPath.startsWith "file:" then
              let runRealRawPeer : IO (Except SqliteError Unit) := do
                match ← LeanSwe.Sqlite.Raw.openDb resolvedPath peerCfg with
                | .error e => return Except.error e
                | .ok pDb =>
                  let res : Except SqliteError Unit ←
                    match ← LeanSwe.Sqlite.Raw.prepare pDb sql with
                    | .error e => pure (Except.error e)
                    | .ok psH =>
                      let bRes : Except SqliteError Unit ←
                        if ps.isEmpty then pure (Except.ok ())
                        else LeanSwe.Sqlite.Raw.bind psH ps
                      let sRes : Except SqliteError Unit ←
                        match bRes with
                        | .error e => pure (Except.error e)
                        | .ok () =>
                          let mut stepErr? : Option SqliteError := none
                          let mut doneLoop := false
                          while !doneLoop do
                            match ← LeanSwe.Sqlite.Raw.step psH with
                            | .error e =>
                              stepErr? := some e
                              doneLoop := true
                            | .ok .done =>
                              doneLoop := true
                            | .ok (.row _) =>
                              pure ()
                          match stepErr? with
                          | some e => pure (Except.error e)
                          | none => pure (Except.ok ())
                      let fRes ← LeanSwe.Sqlite.Raw.finalize psH
                      match sRes with
                      | .error e => pure (Except.error e)
                      | .ok () => pure fRes
                  let cRes ← LeanSwe.Sqlite.Raw.closeDb pDb
                  match cRes with
                  | .error e => return Except.error e
                  | .ok () => return res
              let rPeer ← runRealRawPeer
              let stNow ← worldRef.get
              let (mPeer, stNext) := (do
                match ← Model.modelRawOps.openDb resolvedPath peerCfg with
                | .error e => pure (Except.error e : Except SqliteError Unit)
                | .ok pMod =>
                  let res ← Model.modelExecMaybeBind Model.modelRawOps pMod sql
                    (if ps.isEmpty then none else some ps)
                  let cRes ← Model.modelRawOps.closeDb pMod
                  match cRes with
                  | .error e => pure (Except.error e : Except SqliteError Unit)
                  | .ok () => pure res).run stNow
              worldRef.set stNext
              match rPeer, mPeer with
              | .ok (), .ok () => pure ()
              | .error e1, .error e2 =>
                if !errorsMatch e1 e2 then
                  recordMismatch mismatchRef s!"RAW_PEER_ERR_MISMATCH sql={repr sql} real={repr e1} model={repr e2}"
              | _, _ =>
                recordMismatch mismatchRef s!"RAW_PEER_OUTCOME_MISMATCH sql={repr sql} real={repr rPeer} model={repr mPeer}"
            else
              let rPeer ← LeanSwe.Sqlite.withDb resolvedPath peerCfg fun pDb => LeanSwe.Sqlite.exec pDb sql ps
              let stNow ← worldRef.get
              let (mPeer, stNext) := (Model.modelApi.withDb resolvedPath peerCfg fun pMod =>
                Model.modelApi.exec pMod sql ps).run stNow
              worldRef.set stNext
              match rPeer, mPeer with
              | .ok (), .ok () => pure ()
              | .error e1, .error e2 =>
                if !errorsMatch e1 e2 then
                  recordMismatch mismatchRef s!"RAW_PEER_ERR_MISMATCH sql={repr sql} real={repr e1} model={repr e2}"
              | _, _ =>
                recordMismatch mismatchRef s!"RAW_PEER_OUTCOME_MISMATCH sql={repr sql} real={repr rPeer} model={repr mPeer}"
          | .rawPeerExec peerTgt peerCfg sql ps =>
            let peerPath := peerTgt.resolve epDir
            let rPO ← LeanSwe.Sqlite.Raw.openDb peerPath peerCfg
            let stP0 ← worldRef.get
            let (mPO, stP1) := Model.modelRawOps.openDb peerPath peerCfg stP0
            worldRef.set stP1
            match rPO, mPO with
            | .error e1, .error e2 =>
              if !errorsMatch e1 e2 then
                recordMismatch mismatchRef
                  s!"RAW_PEER_OPEN_ERR_MISMATCH path={repr peerPath} real={repr e1} model={repr e2}"
            | .ok rPDb, .error e2 =>
              let _ ← LeanSwe.Sqlite.Raw.closeDb rPDb
              recordMismatch mismatchRef
                s!"RAW_PEER_OPEN_OUTCOME_MISMATCH path={repr peerPath} real=.ok model={repr e2}"
            | .error e1, .ok mPDb =>
              let (_, stPC) := Model.modelRawOps.closeDb mPDb stP1
              worldRef.set stPC
              recordMismatch mismatchRef
                s!"RAW_PEER_OPEN_OUTCOME_MISMATCH path={repr peerPath} real={repr e1} model=.ok"
            | .ok rPDb, .ok mPDb =>
              let rPP ← LeanSwe.Sqlite.Raw.prepare rPDb sql
              let stP2 ← worldRef.get
              let (mPP, stP3) := Model.modelRawOps.prepare mPDb sql stP2
              worldRef.set stP3
              match rPP, mPP with
              | .error e1, .error e2 =>
                if !errorsMatch e1 e2 then
                  recordMismatch mismatchRef s!"RAW_PEER_PREP_ERR_MISMATCH sql={repr sql} real={repr e1} model={repr e2}"
              | .ok rPSt, .error e2 =>
                let _ ← LeanSwe.Sqlite.Raw.finalize rPSt
                recordMismatch mismatchRef s!"RAW_PEER_PREP_OUTCOME_MISMATCH sql={repr sql} real=.ok model={repr e2}"
              | .error e1, .ok mPSt =>
                worldRef.set (Model.modelRawOps.finalize mPSt stP3).2
                recordMismatch mismatchRef s!"RAW_PEER_PREP_OUTCOME_MISMATCH sql={repr sql} real={repr e1} model=.ok"
              | .ok rPSt, .ok mPSt =>
                let mut bindOk := true
                if !ps.isEmpty then
                  let rPB ← LeanSwe.Sqlite.Raw.bind rPSt ps
                  let stPB0 ← worldRef.get
                  let (mPB, stPB1) := Model.modelRawOps.bind mPSt ps stPB0
                  worldRef.set stPB1
                  match rPB, mPB with
                  | .ok (), .ok () => pure ()
                  | .error e1, .error e2 =>
                    bindOk := false
                    if !errorsMatch e1 e2 then
                      recordMismatch mismatchRef s!"RAW_PEER_BIND_ERR_MISMATCH real={repr e1} model={repr e2}"
                  | _, _ =>
                    bindOk := false
                    recordMismatch mismatchRef s!"RAW_PEER_BIND_OUTCOME_MISMATCH real={repr rPB} model={repr mPB}"
                if bindOk && !(← hasActiveMismatch mismatchRef) then
                  let mut doneP := false
                  while !doneP && !(← hasActiveMismatch mismatchRef) do
                    let rPS ← LeanSwe.Sqlite.Raw.step rPSt
                    let stPS0 ← worldRef.get
                    let pWitnessRows? ←
                      match rPS with
                      | .ok .done =>
                        let rawQ : IO (Except String (Option (List SqliteRow))) := do
                          match Model.stmtInsertIpkTarget? stPS0 mPSt with
                          | none => return .ok none
                          | some (tblName, ipkCol) =>
                            match ← LeanSwe.Sqlite.Raw.prepare rPDb s!"SELECT * FROM {tblName} ORDER BY {ipkCol} ASC" with
                            | .error e => return .error s!"SQLITE_PEER_WITNESS_PREP_ERR tbl={tblName} err={repr e}"
                            | .ok qSt =>
                              let mut qRows : Array SqliteRow := #[]
                              let mut qErr? : Option SqliteError := none
                              let mut qDone := false
                              while !qDone do
                                match ← LeanSwe.Sqlite.Raw.step qSt with
                                | .ok .done => qDone := true
                                | .ok (.row r) => qRows := qRows.push r
                                | .error e =>
                                  qErr? := some e
                                  qDone := true
                              let _ ← LeanSwe.Sqlite.Raw.finalize qSt
                              match qErr? with
                              | some e => return .error s!"SQLITE_PEER_WITNESS_STEP_ERR tbl={tblName} err={repr e}"
                              | none => return .ok (some qRows.toList)
                        match ← rawQ with
                        | .ok opt => pure opt
                        | .error msg =>
                          recordMismatch mismatchRef msg
                          pure none
                      | _ => pure none
                    if !(← hasActiveMismatch mismatchRef) then
                      let (mPS, stPS1?) := Model.stepRawRelational mPSt rPS stPS0 pWitnessRows?
                      if let some stPS1 := stPS1? then
                        worldRef.set stPS1
                      if !stepResultMatches rPS mPS || stPS1?.isNone then
                        recordMismatch mismatchRef s!"RAW_PEER_STEP_MISMATCH sql={repr sql} real={repr rPS} model={repr mPS}"
                        doneP := true
                      else
                        match rPS with
                        | .ok (.row _) => pure ()
                        | _ => doneP := true
                let rPF ← LeanSwe.Sqlite.Raw.finalize rPSt
                let stPF0 ← worldRef.get
                let (mPF, stPF1) := Model.modelRawOps.finalize mPSt stPF0
                worldRef.set stPF1
                if !(← hasActiveMismatch mismatchRef) then
                  match rPF, mPF with
                  | .ok (), .ok () => pure ()
                  | .error e1, .error e2 =>
                    if !errorsMatch e1 e2 then
                      recordMismatch mismatchRef s!"RAW_PEER_FIN_ERR_MISMATCH real={repr e1} model={repr e2}"
                  | _, _ =>
                    recordMismatch mismatchRef s!"RAW_PEER_FIN_OUTCOME_MISMATCH real={repr rPF} model={repr mPF}"
              let rPC ← LeanSwe.Sqlite.Raw.closeDb rPDb
              let stPC0 ← worldRef.get
              let (mPC, stPC1) := Model.modelRawOps.closeDb mPDb stPC0
              worldRef.set stPC1
              if !(← hasActiveMismatch mismatchRef) then
                match rPC, mPC with
                | .ok (), .ok () => pure ()
                | _, _ =>
                  recordMismatch mismatchRef s!"RAW_PEER_CLOSE_MISMATCH real={repr rPC} model={repr mPC}"
      if !(← hasActiveMismatch mismatchRef) then
        let hasLiveR := (← realSlotsRef.get).any fun | some (_, true) => true | _ => false
        if hasLiveR then
          let rBusy ← LeanSwe.Sqlite.Raw.closeDb realDb
          let stNow ← worldRef.get
          let (mBusy, stNext) := Model.modelRawOps.closeDb modelDb stNow
          worldRef.set stNext
          match rBusy, mBusy with
          | .error e1, .error e2 =>
            if e1.kind != .busy || !errorsMatch e1 e2 then
              recordMismatch mismatchRef s!"RAW_CLOSE_BUSY_ERR_MISMATCH real={repr e1} model={repr e2}"
            else
              trackerRef.modify (·.record "raw" "closeBusy")
          | _, _ =>
            recordMismatch mismatchRef s!"RAW_CLOSE_BUSY_OUTCOME_MISMATCH real={repr rBusy} model={repr mBusy}"
    finally
      let rFinalSlots ← realSlotsRef.get
      let mFinalSlots ← modelSlotsRef.get
      for i in List.range rFinalSlots.size do
        match rFinalSlots.getD i none, mFinalSlots.getD i none with
        | some (rs, true), some (ms, true) =>
          let rFin ← LeanSwe.Sqlite.Raw.finalize rs
          let stNow ← worldRef.get
          let (mFin, stNext) := Model.modelRawOps.finalize ms stNow
          worldRef.set stNext
          if !(← hasActiveMismatch mismatchRef) then
            match rFin, mFin with
            | .ok (), .ok () => pure ()
            | .error e1, .error e2 =>
              if !errorsMatch e1 e2 then
                recordMismatch mismatchRef s!"RAW_CLEANUP_FIN_ERR real={repr e1} model={repr e2}"
            | _, _ =>
              recordMismatch mismatchRef s!"RAW_CLEANUP_FIN_ERR real={repr rFin} model={repr mFin}"
        | some (rs, true), none =>
          let _ ← LeanSwe.Sqlite.Raw.finalize rs
        | none, some (ms, true) =>
          let stNow ← worldRef.get
          worldRef.set (Model.modelRawOps.finalize ms stNow).2
        | _, _ => pure ()
      let rClose ← LeanSwe.Sqlite.Raw.closeDb realDb
      let stNow ← worldRef.get
      let (mClose, stClose) := Model.modelRawOps.closeDb modelDb stNow
      worldRef.set stClose
      if !(← hasActiveMismatch mismatchRef) then
        match rClose, mClose with
        | .ok (), .ok () => pure ()
        | _, _ =>
          recordMismatch mismatchRef s!"RAW_CLEANUP_CLOSE_MISMATCH real={repr rClose} model={repr mClose}"
      let dbs ← LeanSwe.Sqlite.activeDbCount
      let stmts ← LeanSwe.Sqlite.activeStmtCount
      if dbs != 0 || stmts != 0 then
        recordMismatch mismatchRef s!"LEAK_AFTER_RAW_SESSION dbs={dbs} stmts={stmts}"

private def runEpisode
    (tpl : EpisodeTemplate)
    (rootDir : System.FilePath)
    (attemptRef : IO.Ref Nat)
    (oracleCfg : OracleBugConfig)
    (ep : SqliteEpisode)
    (tracker : CoverageTracker) : IO (CoverageTracker × Nat × Option String) := do
  let idx ← attemptRef.modifyGet fun n => (n, n + 1)
  let epDir := rootDir / s!"ep-{idx}"
  try
    let stInit ← setupEpisodeDir tpl (episodeNeedsSym45 ep) epDir
    let worldRef ← IO.mkRef stInit
    let trackerRef ← IO.mkRef tracker
    let opsCountRef ← IO.mkRef 0
    let mismatchRef ← IO.mkRef (none : Option String)
    let escapedRef ← IO.mkRef (#[] : Array DbHandle)
    for act in ep do
      if ← hasActiveMismatch mismatchRef then break
      match act with
      | .validateConfig cfg =>
        opsCountRef.modify (· + 1)
        let rRes := LeanSwe.Sqlite.validateConfig cfg
        let mRes := Model.validateConfig cfg
        let eqRes :=
          match rRes, mRes with
          | .ok (), .ok () => true
          | .error e1, .error e2 => e1 == e2
          | _, _ => false
        if !eqRes then
          recordMismatch mismatchRef s!"VALIDATE_CONFIG_MISMATCH cfg={repr cfg} real={repr rRes} model={repr mRes}"
        else
          let b := match rRes with | .ok () => "ok" | .error _ => "err.invalidInput"
          trackerRef.modify (·.record "validateConfig" b)
      | .mapRawError raw =>
        opsCountRef.modify (· + 1)
        let rRes := LeanSwe.Sqlite.mapRawError raw
        let mRes := Model.mapRawError raw
        if rRes != mRes then
          recordMismatch mismatchRef s!"MAP_RAW_ERROR_MISMATCH raw={repr raw} real={repr rRes} model={repr mRes}"
      | .closedHandleOp ref op =>
        let escaped ← escapedRef.get
        let realDb := resolveClosedRef escaped ref
        let modelClosedDb : DbHandle := { id := 999999999 }
        runLeafLockstep oracleCfg realDb modelClosedDb false true op worldRef trackerRef opsCountRef mismatchRef
        let dbs ← LeanSwe.Sqlite.activeDbCount
        let stmts ← LeanSwe.Sqlite.activeStmtCount
        if dbs != 0 || stmts != 0 then
          recordMismatch mismatchRef s!"LEAK_AFTER_CLOSED_OP dbs={dbs} stmts={stmts}"
      | .closedHandleTx ref txOps exitMode =>
        let escaped ← escapedRef.get
        let realDb := resolveClosedRef escaped ref
        let modelClosedDb : DbHandle := { id := 999999999 }
        runTxLockstep oracleCfg realDb modelClosedDb false txOps exitMode worldRef trackerRef opsCountRef mismatchRef
        let dbs ← LeanSwe.Sqlite.activeDbCount
        let stmts ← LeanSwe.Sqlite.activeStmtCount
        if dbs != 0 || stmts != 0 then
          recordMismatch mismatchRef s!"LEAK_AFTER_CLOSED_TX dbs={dbs} stmts={stmts}"
      | .withDbSession target cfg ops exitMode =>
        runWithDbSession epDir oracleCfg target cfg ops exitMode
          worldRef trackerRef opsCountRef mismatchRef escapedRef
      | .rawSession target cfg ops =>
        runRawSessionLockstep epDir target cfg ops worldRef trackerRef opsCountRef mismatchRef
    let tr ← trackerRef.get
    let nOps ← opsCountRef.get
    let mm ← mismatchRef.get
    return (tr, nOps, mm)
  finally
    cleanupEpisodeDir epDir

private def smokeCorpus : Array SqliteEpisode := #[
  #[
    .validateConfig {},
    .validateConfig { readOnly := true, createIfMissing := true },
    .validateConfig { busyTimeoutMs := maxBusyTimeoutMs + 1 },
    .mapRawError (.busy 5 "locked"),
    .mapRawError (.invalidArgument ""),
    .withDbSession .memory {} #[
      .leaf (.exec "CREATE TABLE p(id INTEGER PRIMARY KEY, u INT UNIQUE, v REAL, tag TEXT, bin BLOB, a ANY) STRICT" #[]),
      .leaf (.exec "CREATE TABLE c(id INTEGER PRIMARY KEY AUTOINCREMENT, pid INT NOT NULL REFERENCES p(id), note TEXT) STRICT" #[]),
      .leaf (.exec "INSERT INTO p(id, u, v, tag, bin, a) VALUES (?, ?, ?, ?, ?, ?)"
        #[.int 1, .int 10, .real (Float.ofBits 0), .text "ok\x00nul", .bytes (ByteArray.mk #[0x41, 0x00, 0xFF, 0xFE, 0x80]), .text "any\x00z"]),
      .leaf (.exec "INSERT INTO p(id, u, v, tag, bin, a) VALUES (?, ?, ?, ?, ?, ?)"
        #[.int 2, .int 20, .real (Float.ofBits 0x8000000000000000), .text "negz", .bytes ByteArray.empty, .real (Float.ofBits 0x7ff8000000000000)]),
      .leaf (.exec "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 1, .int 99]),
      .leaf (.query "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 1, .int 99]),
      .leaf (.queryOne "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 1, .int 99]),
      .leaf (.exec "INSERT INTO c(id, pid, note) VALUES (?, ?, ?)" #[.int 1, .null, .text "bad"]),
      .leaf (.exec "INSERT INTO c(id, pid, note) VALUES (?, ?, ?)" #[.int 1, .int 999, .text "badfk"]),
      .leaf (.exec "INSERT INTO c(id, pid, note) VALUES (?, ?, ?)" #[.int 2, .int 1, .bytes ByteArray.empty]),
      .leaf (.exec "INSERT INTO p(id, u) VALUES (?, ?)" #[.text "not_an_int", .int 30]),
      .leaf (.exec "INSERT INTO no_such_table VALUES (?)" #[.int 1]),
      .leaf (.exec "!invalid?" #[]),
      .leaf (.exec "SELECT 1; SELECT 2" #[]),
      .leaf (.query "SELECT v, tag, bin, a FROM p ORDER BY id ASC" #[]),
      .leaf (.query "SELECT id FROM p WHERE id > ? ORDER BY id ASC" #[.int 999]),
      .leaf (.query "!invalid?" #[]),
      .leaf (.query "SELECT 1; SELECT 2" #[]),
      .leaf (.query "SELECT * FROM no_such_table" #[]),
      .leaf (.queryOne "SELECT tag FROM p WHERE id = ?" #[.int 1]),
      .leaf (.queryOne "SELECT tag FROM p WHERE id = ?" #[.int 999]),
      .leaf (.queryOne "!invalid?" #[]),
      .leaf (.queryOne "SELECT 1; SELECT 2" #[]),
      .leaf (.queryOne "SELECT * FROM no_such_table" #[]),
      .leaf (.exec "UPDATE p SET tag = ? WHERE id = ?" #[.text "updated", .int 1]),
      .leaf (.exec "DELETE FROM p WHERE id = ?" #[.int 2]),
      .leaf (.exec "BEGIN IMMEDIATE" #[]),
      .leaf (.exec "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 3, .int 30]),
      .leaf (.exec "ROLLBACK" #[]),
      .withTx #[.exec "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 4, .int 40]] .returnOk,
      .withTx #[.exec "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 5, .int 50]]
        (.returnCallerErr { kind := .constraint, message := "abort constraint" }),
      .withTx #[.exec "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 6, .int 60]]
        (.returnCallerErr { kind := .invalidInput, message := "abort invalid" }),
      .withTx #[.exec "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 7, .int 70]]
        (.throwIoUserError "abort throw"),
      .withTx #[.exec "ROLLBACK" #[]]
        (.returnCallerErr { kind := .invalidInput, message := "abort after manual rb" }),
      .leaf (.exec "CREATE TABLE ob_n(id INTEGER PRIMARY KEY, u INT)" #[]),
      .leaf (.exec "INSERT INTO ob_n(id, u) VALUES (1, NULL), (2, 10), (3, 20)" #[]),
      .leaf (.query "SELECT id, u FROM ob_n ORDER BY u ASC" #[]),
      .leaf (.query "SELECT id, u FROM ob_n ORDER BY u DESC" #[]),
      .leaf (.query "SELECT id FROM p ORDER BY id ASC" #[])
    ] .returnOk
  ],
  #[
    .withDbSession (.raw "file::memory:?cache=shared")
      { readOnly := true, createIfMissing := false, busyTimeoutMs := 0, walMode := false, foreignKeys := false }
      #[] .returnOk,
    .rawSession (.raw "file::memory:?cache=shared&mode=memory")
      { readOnly := false, createIfMissing := false, busyTimeoutMs := 0, walMode := false, foreignKeys := false }
      #[.prepare 0 "CREATE TABLE IF NOT EXISTS sc_sm_ok(id INTEGER PRIMARY KEY)", .step 0, .finalize 0]
  ],
  #[
    .withDbSession (.raw "") {} #[] .returnOk,
    .withDbSession (.raw "file::memory:?cache=shared") {} #[] .returnOk,
    .withDbSession (.epSuffix "/subdir/../missing.sqlite") { walMode := false } #[] .returnOk,
    .withDbSession .missing { createIfMissing := false } #[] .returnOk,
    .withDbSession .subdir {} #[] .returnOk,
    .withDbSession .missingParent {} #[] .returnOk,
    .withDbSession .ro0444 { readOnly := false, createIfMissing := false, walMode := true } #[] .returnOk,
    .withDbSession .corrupt { walMode := true } #[] .returnOk,
    .withDbSession .db0 { walMode := false } #[
      .leaf (.exec "CREATE TABLE ft(id INTEGER PRIMARY KEY, a REAL, b TEXT)" #[]),
      .leaf (.exec "INSERT INTO ft(id, a, b) VALUES (?, ?, ?)" #[.int 1, .real 3500000000000000.2500001, .text "48.00"])
    ] .returnOk,
    .closedHandleOp (.escaped 0) (.exec "SELECT 1" #[]),
    .closedHandleOp (.escaped 0) (.query "SELECT 1" #[]),
    .closedHandleOp (.escaped 0) (.queryOne "SELECT 1" #[]),
    .closedHandleTx (.escaped 0) #[.exec "SELECT 1" #[]] .returnOk,
    .withDbSession .ro0444 { readOnly := true, createIfMissing := false, walMode := false } #[
      .leaf (.exec "INSERT INTO ro_seed(id, x) VALUES (1, 2)" #[]),
      .withTx #[.exec "SELECT 1" #[]] .returnOk,
      .withTx #[.exec "INSERT INTO ro_seed(id, x) VALUES (2, 3)" #[]]
        (.returnCallerErr { kind := .ioError, message := "abort io" })
    ] .returnOk
  ],
  #[
    .withDbSession .db0 { walMode := false } #[
      .leaf (.exec "CREATE TABLE qb(id INTEGER PRIMARY KEY, x INT)" #[]),
      .leaf (.exec "INSERT INTO qb(id, x) VALUES (?, ?)" #[.int 9223372036854775807, .int 1]),
      .leaf (.exec "INSERT INTO qb(id, x) VALUES (NULL, ?)" #[.int 2]),
      .leaf (.query "SELECT id FROM qb ORDER BY id ASC" #[]),
      .leaf (.exec "BEGIN IMMEDIATE" #[]),
      .nestedWithDb .db0 { walMode := false, busyTimeoutMs := 0 } #[
        (true, .exec "INSERT INTO qb(id, x) VALUES (?, ?)" #[.int 3, .int 3]),
        (true, .query "INSERT INTO qb(id, x) VALUES (?, ?)" #[.int 4, .int 4]),
        (true, .queryOne "INSERT INTO qb(id, x) VALUES (?, ?)" #[.int 5, .int 5]),
        (true, .query "SELECT * FROM qb" #[]),
        (true, .queryOne "SELECT x FROM qb WHERE id = ?" #[.int 1])
      ] .returnOk,
      .nestedWithDb .db0 { walMode := true, busyTimeoutMs := 0 } #[] .returnOk,
      .leaf (.exec "ROLLBACK" #[])
    ] .returnOk,
    .withDbSession .db0 { walMode := false } #[
      .leaf (.exec "BEGIN IMMEDIATE" #[]),
      .leaf (.exec "INSERT INTO qb(id, x) VALUES (?, ?)" #[.int 99, .int 9])
    ] (.throwIoUserError "close_rollback"),
    .withDbSession .db0 { walMode := false } #[
      .leaf (.query "SELECT * FROM qb WHERE id = ?" #[.int 99])
    ] .returnOk
  ],
  #[
    .withDbSession .db0 { walMode := false } #[
      .leaf (.exec "CREATE TABLE bt(id INTEGER PRIMARY KEY, x INT)" #[]),
      .leaf (.exec "INSERT INTO bt(id, x) VALUES (1, 10)" #[]),
      .leaf (.exec "BEGIN DEFERRED" #[]),
      .leaf (.query "SELECT x FROM bt WHERE id = ?" #[.int 1]),
      .nestedWithDb .db0 { walMode := false, busyTimeoutMs := 0 } #[
        (true, .exec "INSERT INTO bt(id, x) VALUES (2, 20)" #[])
      ] .returnOk,
      .leaf (.exec "COMMIT" #[])
    ] .returnOk,
    .withDbSession .db1 { walMode := true } #[
      .leaf (.exec "CREATE TABLE wt(id INTEGER PRIMARY KEY, x INT)" #[]),
      .leaf (.exec "INSERT INTO wt(id, x) VALUES (1, 10)" #[]),
      .leaf (.exec "BEGIN DEFERRED" #[]),
      .leaf (.query "SELECT x FROM wt WHERE id = ?" #[.int 1]),
      .nestedWithDb .db1 { walMode := true, busyTimeoutMs := 0 } #[
        (true, .exec "INSERT INTO wt(id, x) VALUES (2, 20)" #[])
      ] .returnOk,
      .leaf (.exec "INSERT INTO wt(id, x) VALUES (3, 30)" #[]),
      .leaf (.exec "COMMIT" #[])
    ] .returnOk
  ],
  #[
    .withDbSession (.raw "/") {} #[] .returnOk,
    .withDbSession (.raw "/") { readOnly := true, createIfMissing := false } #[] .returnOk,
    .withDbSession (.raw "/.") {} #[] .returnOk,
    .withDbSession (.raw "/.") { readOnly := true, createIfMissing := false } #[] .returnOk,
    .withDbSession (.raw "/..") {} #[] .returnOk,
    .withDbSession (.raw "/..") { readOnly := true, createIfMissing := false } #[] .returnOk,
    .withDbSession (.raw ".") {} #[] .returnOk,
    .withDbSession (.raw ".") { readOnly := true, createIfMissing := false } #[] .returnOk,
    .withDbSession (.raw "./") {} #[] .returnOk,
    .withDbSession (.raw "./") { readOnly := true, createIfMissing := false } #[] .returnOk,
    .withDbSession (.raw "..") {} #[] .returnOk,
    .withDbSession (.raw "..") { readOnly := true, createIfMissing := false } #[] .returnOk,
    .withDbSession (.raw "../") {} #[] .returnOk,
    .withDbSession (.raw "../") { readOnly := true, createIfMissing := false } #[] .returnOk,
    .withDbSession (.epSuffix "/.") {} #[] .returnOk,
    .withDbSession (.epSuffix "/.") { readOnly := true, createIfMissing := false } #[] .returnOk,
    .withDbSession (.epSuffix "/..") {} #[] .returnOk,
    .withDbSession (.epSuffix "/..") { readOnly := true, createIfMissing := false } #[] .returnOk,
    .withDbSession (.epSuffix "/subdir/.") { readOnly := true, createIfMissing := false } #[] .returnOk,
    .withDbSession (.epSuffix "/subdir/..") { readOnly := true, createIfMissing := false } #[] .returnOk,
    .withDbSession (.epSuffix "/./db0.sqlite") {} #[
      .leaf (.exec "CREATE TABLE np(id INTEGER PRIMARY KEY, x INT)" #[])
    ] .returnOk,
    .withDbSession (.epSuffix "//db0.sqlite") { createIfMissing := false } #[
      .leaf (.exec "INSERT INTO np(id, x) VALUES (1, 10)" #[])
    ] .returnOk,
    .withDbSession (.epSuffix "/subdir/../db0.sqlite") { readOnly := true, createIfMissing := false } #[
      .leaf (.query "SELECT id, x FROM np ORDER BY id ASC" #[])
    ] .returnOk,
    .withDbSession .db1 { walMode := false, foreignKeys := false } #[
      .leaf (.exec "CREATE TABLE fk_p(id INTEGER PRIMARY KEY, tag TEXT)" #[]),
      .leaf (.exec "CREATE TABLE fk_c(id INTEGER PRIMARY KEY, pid INT REFERENCES fk_p(id), tag TEXT)" #[]),
      .leaf (.exec "INSERT INTO fk_p(id, tag) VALUES (1, ?), (2, ?)" #[.text "p1", .text "p2"]),
      .leaf (.exec "INSERT INTO fk_c(id, pid, tag) VALUES (10, 999, ?)" #[.text "broken"])
    ] .returnOk,
    .withDbSession .db1 { walMode := false, createIfMissing := false, foreignKeys := true } #[
      .leaf (.exec "UPDATE fk_p SET tag = ? WHERE id = 1" #[.text "ok"]),
      .leaf (.exec "UPDATE fk_p SET id = 3 WHERE id = 1" #[]),
      .leaf (.exec "UPDATE fk_c SET tag = ? WHERE id = 10" #[.text "still_broken"]),
      .leaf (.exec "DELETE FROM fk_p WHERE id = 2" #[])
    ] .returnOk,
    .withDbSession .memory {} #[
      .leaf (.exec "CREATE TABLE strict_t0(id INTEGER PRIMARY KEY, u INT, v REAL, t TEXT, b BLOB, a ANY) STRICT" #[]),
      .leaf (.exec "CREATE TABLE strict_ns(id INTEGER PRIMARY KEY, u INT, t TEXT, b BLOB)" #[]),
      .leaf (.exec "INSERT INTO strict_t0(id, u, v, t, b, a) VALUES (1, ?, ?, ?, ?, ?)"
        #[.text "4503599627370496\x00abc", .text "1.213e-300", .text "42", .bytes (ByteArray.mk #[0x34, 0x32]), .int 42]),
      .leaf (.exec "INSERT INTO strict_t0(id, u, v, t, b, a) VALUES (2, ?, ?, ?, ?, ?)"
        #[.text "123\x0b", .text "1213e-303", .real (Float.ofBits 0x01a9feab2284814a), .bytes ByteArray.empty, .text "42"]),
      .leaf (.exec "INSERT INTO strict_t0(id, u, v, t, b, a) VALUES (20, ?, ?, ?, ?, ?)"
        #[.int 20, .text "-1.63680654791682e-46", .real (Float.ofBits 0xb66de7068330430d), .bytes ByteArray.empty, .null]),
      .leaf (.exec "INSERT INTO strict_t0(u, u, id) VALUES (?, ?, ?)" #[.int 77, .int 88, .int 3]),
      .leaf (.exec "INSERT INTO strict_t0(id, id, u) VALUES (?, ?, ?)" #[.int 99, .int 4, .int 11]),
      .leaf (.exec "INSERT INTO strict_t0(id, u) VALUES (9223372036854775807, 5), (NULL, 6)" #[]),
      .leaf (.exec "INSERT INTO strict_t0(id, u) VALUES (NULL, 20), (500, 30)" #[]),
      .leaf (.exec "INSERT INTO strict_t0(id, u) VALUES (NULL, 40), (NULL, 50)" #[]),
      .leaf (.exec "INSERT INTO strict_ns(id, u, t, b) VALUES (1, ?, ?, ?)"
        #[.text "\x0b99", .text "42", .int 42]),
      .leaf (.query "SELECT id, u, v, t FROM strict_t0 ORDER BY id ASC" #[]),
      .leaf (.query "SELECT id FROM strict_t0 WHERE t = b OR t = a ORDER BY id ASC" #[]),
      .leaf (.query "SELECT id FROM strict_ns WHERE t = b ORDER BY id ASC" #[]),
      .leaf (.exec "CREATE TABLE strict_fk_bad(id INTEGER PRIMARY KEY, badcol INT REFERENCES strict_t0(no_such_col))" #[]),
      .leaf (.exec "UPDATE strict_t0 SET u = ?, u = ? WHERE id = ?" #[.int 54, .int 55, .int 1]),
      .leaf (.query "SELECT  \x0b 1" #[]),
      .leaf (.query "SELECT 1; \x0b" #[]),
      .leaf (.query "SELECT 1;\x0b" #[]),
      .leaf (.query "SELECT 1; -- c\n\x0b" #[]),
      .leaf (.query "SELECT 1; /* ok */\x0b" #[]),
      .leaf (.exec "SELECT ?" #[]),
      .leaf (.query "SELECT ?" #[]),
      .leaf (.queryOne "SELECT ?" #[]),
      .leaf (.exec "SELECT 1\x00" #[]),
      .leaf (.exec "CREATE TABLE to(x INT)" #[]),
      .leaf (.exec "CREATE TABLE add(x INT)" #[]),
      .leaf (.exec "CREATE TABLE deferrable(x INT)" #[]),
      .leaf (.exec "CREATE TABLE escape(x INT)" #[]),
      .leaf (.exec "CREATE TABLE isnull(x INT)" #[]),
      .leaf (.exec "CREATE TABLE nothing(x INT)" #[]),
      .leaf (.exec "CREATE TABLE notnull(x INT)" #[]),
      .leaf (.query "SELECT raise FROM strict_t0" #[]),
      .leaf (.query "SELECT id FROM strict_t0 WHERE ((id = ?))" #[.int 1]),
      .leaf (.exec "CREATE TABLE p_s2(a INT, tag TEXT) STRICT" #[]),
      .withTx #[
        .exec "INSERT INTO p_s2(a, tag) VALUES (1, 'ok'), (2, ?)" #[.bytes ByteArray.empty]
      ] .returnOk,
      .leaf (.query "SELECT a, tag FROM p_s2 ORDER BY a ASC" #[]),
      .leaf (.exec "CREATE TABLE p_auto(id INTEGER PRIMARY KEY AUTOINCREMENT, x INT)" #[]),
      .leaf (.exec "INSERT INTO p_auto(id, x) VALUES (9223372036854775807, 1)" #[]),
      .leaf (.exec "BEGIN IMMEDIATE" #[]),
      .leaf (.exec "INSERT INTO p_auto(id, x) VALUES (NULL, 2)" #[]),
      .leaf (.exec "COMMIT" #[]),
      .leaf (.exec "CREATE TABLE fp_r(id INTEGER PRIMARY KEY, r REAL UNIQUE)" #[]),
      .leaf (.exec "CREATE TABLE fc_r(id INTEGER PRIMARY KEY, pid INT REFERENCES fp_r(r))" #[]),
      .leaf (.exec "INSERT INTO fp_r(id, r) VALUES (1, ?)" #[.real 9007199254740992.0]),
      .leaf (.exec "INSERT INTO fc_r(id, pid) VALUES (1, ?)" #[.int 9007199254740993]),
      .leaf (.exec "CREATE TABLE t_sref(id INT UNIQUE, pid TEXT REFERENCES t_sref(id), v INT)" #[]),
      .leaf (.exec "INSERT INTO t_sref(id, pid, v) VALUES (1, '1', 10)" #[]),
      .leaf (.exec "INSERT INTO t_sref(id, pid, v) VALUES (1, NULL, 10)" #[]),
      .leaf (.exec "UPDATE t_sref SET v = 20 WHERE id = 1" #[])
    ] (.returnCallerErr { kind := .invalidInput, message := "smoke caller err" }),
    .withDbSession .walRo0444 { readOnly := false, createIfMissing := false, walMode := true } #[
      .leaf (.query "SELECT id, x FROM ro_seed" #[]),
      .leaf (.exec "INSERT INTO ro_seed(id, x) VALUES (1, 2)" #[])
    ] .returnOk,
    .withDbSession .symDeep { walMode := false } #[
      .leaf (.exec "CREATE TABLE sym_t(id INTEGER PRIMARY KEY, x INT)" #[]),
      .leaf (.exec "INSERT INTO sym_t(id, x) VALUES (1, 42)" #[])
    ] .returnOk,
    .withDbSession .symRelDb0 { createIfMissing := false, walMode := false } #[
      .leaf (.query "SELECT x FROM sym_t WHERE id = 1" #[])
    ] .returnOk,
    .withDbSession .symDirDb0 { walMode := false } #[
      .leaf (.exec "CREATE TABLE sd_t(x INT)" #[])
    ] .returnOk,
    .withDbSession .symLoop { walMode := false } #[] .returnOk,
    .withDbSession .db0 { walMode := false } #[
      .leaf (.exec "CREATE TABLE m_pend(id INTEGER PRIMARY KEY, x INT)" #[]),
      .leaf (.exec "BEGIN IMMEDIATE" #[]),
      .leaf (.exec "INSERT INTO m_pend(id, x) VALUES (1, 10)" #[]),
      .nestedWithDb .db0 { walMode := false, busyTimeoutMs := 0 } #[
        (true, .exec "BEGIN DEFERRED" #[]),
        (true, .exec "CREATE TABLE IF NOT EXISTS m_pend(id INTEGER PRIMARY KEY, x INT)" #[]),
        (false, .exec "COMMIT" #[]),
        (true, .query "SELECT x FROM m_pend" #[]),
        (true, .exec "COMMIT" #[]),
        (false, .exec "COMMIT" #[])
      ] .returnOk,
      .nestedWithDb .db0 { walMode := false, busyTimeoutMs := 0 } #[
        (false, .exec "BEGIN IMMEDIATE" #[]),
        (true, .query "SELECT x FROM m_pend" #[]),
        (false, .exec "COMMIT" #[])
      ] .returnOk
    ] .returnOk,
    .withDbSession .db1 { readOnly := false, createIfMissing := true, busyTimeoutMs := 2, walMode := true, foreignKeys := true } #[
      .nestedWithDb .db1 { readOnly := true, createIfMissing := false, busyTimeoutMs := 0, walMode := false, foreignKeys := false } #[
        (true, .exec "CREATE TABLE t1_stale(id INTEGER PRIMARY KEY, x INT) STRICT" #[]),
        (false, .exec "CREATE TABLE t1_stale(id INTEGER PRIMARY KEY, x INT)" #[]),
        (true, .exec "CREATE TABLE t1_stale(id INTEGER PRIMARY KEY, x INT, tag TEXT)" #[])
      ] .returnOk
    ] .returnOk,
    .withDbSession .sym45 { walMode := false } #[
      .leaf (.exec "CREATE TABLE sym45_t(id INTEGER PRIMARY KEY, x INT)" #[]),
      .leaf (.exec "INSERT INTO sym45_t VALUES (1, 7)" #[])
    ] .returnOk,
    .withDbSession (.epSuffix "/sym_45.sqlite") { createIfMissing := false, walMode := false } #[
      .leaf (.query "SELECT x FROM sym45_t WHERE id = 1" #[])
    ] .returnOk,
    .withDbSession .memory {} #[
      .leaf (.exec "CREATE TABLE bnd(id INTEGER PRIMARY KEY, u INT)" #[]),
      .leaf (.exec "INSERT INTO bnd VALUES (1, 10)" #[]),
      .leaf (.query ("SELECT " ++ String.join (List.replicate 1000 "-") ++ "1") #[]),
      .leaf (.exec ("UPDATE bnd SET u = 1 WHERE " ++ String.join (List.replicate 2492 "(") ++ "id = 1" ++ String.join (List.replicate 2492 ")")) #[]),
      .leaf (.exec ("UPDATE bnd SET u = 1 WHERE " ++ String.join (List.replicate 2495 "(") ++ "id = 1" ++ String.join (List.replicate 2495 ")")) #[]),
      .leaf (.exec ("DELETE FROM bnd WHERE " ++ String.join (List.replicate 2492 "(") ++ "id = 2" ++ String.join (List.replicate 2492 ")")) #[]),
      .leaf (.exec ("DELETE FROM bnd WHERE " ++ String.join (List.replicate 2495 "(") ++ "id = 2" ++ String.join (List.replicate 2495 ")")) #[]),
      .leaf (.query ("SELECT id FROM bnd WHERE id = 1 OR " ++ String.join (List.replicate 2492 "(") ++ "id = 1" ++ String.join (List.replicate 2492 ")")) #[]),
      .leaf (.query ("SELECT id FROM bnd WHERE id = 1 AND " ++ String.join (List.replicate 2492 "(") ++ "id = 1" ++ String.join (List.replicate 2492 ")")) #[]),
      .leaf (.query ("SELECT id FROM bnd WHERE NOT " ++ String.join (List.replicate 2492 "(") ++ "id = 2" ++ String.join (List.replicate 2492 ")")) #[]),
      .leaf (.query ("SELECT id FROM bnd WHERE " ++ String.join (List.replicate 2494 "(") ++ "id IS NOT NULL" ++ String.join (List.replicate 2494 ")")) #[]),
      .leaf (.query ("SELECT id FROM bnd WHERE " ++ String.join (List.replicate 2494 "(") ++ "id = +1" ++ String.join (List.replicate 2494 ")")) #[]),
      .leaf (.exec "CREATE TABLE aff_s(k INT PRIMARY KEY, pid TEXT REFERENCES aff_s(k), v INT)" #[]),
      .leaf (.exec "INSERT INTO aff_s(k, pid, v) VALUES ('1', 2, 10), ('02', 1, 20)" #[]),
      .leaf (.exec "CREATE TABLE aff_p(k TEXT PRIMARY KEY, v INT)" #[]),
      .leaf (.exec "CREATE TABLE aff_c(id INTEGER PRIMARY KEY, pid INT REFERENCES aff_p(k))" #[]),
      .leaf (.exec "INSERT INTO aff_p(k, v) VALUES ('1', 100)" #[]),
      .leaf (.exec "INSERT INTO aff_c(id, pid) VALUES (1, 1)" #[]),
      .leaf (.exec "UPDATE aff_p SET k = '01' WHERE k = '1'" #[])
    ] .returnOk,
    .rawSession .missing { createIfMissing := false } #[],
    .rawSession .db0 { walMode := false } #[
      .prepare 0 "!bad syntax!",
      .prepare 0 "CREATE TABLE IF NOT EXISTS raw_sm(id INT PRIMARY KEY, tag TEXT)",
      .step 0,
      .prepare 0 "INSERT INTO raw_sm(id, tag) VALUES (?, ?)",
      .bind 0 #[.int 1],
      .bind 0 #[.int 1, .text "a"],
      .step 0,
      .bind 0 #[.int 1, .text "dup"],
      .step 0,
      .prepare 1 "SELECT id, tag FROM raw_sm ORDER BY id ASC",
      .step 1,
      .bind 1 #[],
      .peerExec "INSERT INTO raw_sm(id, tag) VALUES (2, 'peer')" #[],
      .step 1,
      .step 1,
      .finalize 0,
      .step 0,
      .finalize 0
    ],
    .rawSession .db0 { walMode := false } #[
      .prepare 0 "BEGIN IMMEDIATE",
      .step 0,
      .prepare 1 "INSERT INTO raw_sm(id, tag) VALUES (9, 'rb')",
      .step 1,
      .prepare 0 "ROLLBACK",
      .step 0,
      .prepare 1 "SELECT id FROM raw_sm WHERE id = 9",
      .step 1,
      .finalize 0
    ],
    .withDbSession (.raw (String.ofList (List.replicate 4097 'p'))) {} #[] .returnOk,
    .withDbSession .memory {} #[
      .leaf (.query ("SELECT 1 -- " ++ String.ofList (List.replicate 65530 'x')) #[])
    ] .returnOk,
    .rawSession .memory { walMode := false, foreignKeys := true } #[
      .prepare 0 "CREATE TABLE raw_mor(id INTEGER PRIMARY KEY, u1 INT UNIQUE, u2 INT UNIQUE, a INT)",
      .step 0,
      .finalize 0,
      .prepare 0 "INSERT INTO raw_mor VALUES (1, 100, 20, 1), (2, 10, 200, 1), (3, 300, 300, 2)",
      .step 0,
      .finalize 0,
      .prepare 0 "SELECT id, u1, u2 FROM raw_mor WHERE u1 = 10 OR u2 = 20",
      .step 0,
      .step 0,
      .step 0,
      .finalize 0,
      .prepare 0 "SELECT id, u1, u2 FROM raw_mor WHERE u1 = 10 OR u2 = 20 ORDER BY id ASC",
      .step 0,
      .prepare 1 "BEGIN",
      .step 1,
      .finalize 1,
      .prepare 1 "CREATE TABLE raw_mor_rb(x INT)",
      .step 1,
      .finalize 1,
      .prepare 1 "ROLLBACK",
      .step 1,
      .finalize 1,
      .step 0,
      .step 0,
      .finalize 0,
      .prepare 0 "SELECT id, u1 FROM raw_mor WHERE u1 = 10 OR u1 = 100",
      .step 0,
      .prepare 1 "DELETE FROM raw_mor WHERE id = 2",
      .step 1,
      .finalize 1,
      .prepare 1 "INSERT INTO raw_mor VALUES (4, 10, 400, 1)",
      .step 1,
      .finalize 1,
      .step 0,
      .step 0,
      .finalize 0
    ]
  ]
]

private def getFuzzRootDir : IO System.FilePath := do
  let pid ← IO.Process.getPID
  let root : System.FilePath := s!"/tmp/leanswe-sqlite-fuzz-{pid}"
  IO.FS.createDirAll root
  return root

private def runBusyWithTxProbe (tpl : EpisodeTemplate) (rootDir : System.FilePath) (attemptRef : IO.Ref Nat)
    (tracker : CoverageTracker) : IO (CoverageTracker × Nat) := do
  let idx ← attemptRef.modifyGet fun n => (n, n + 1)
  let epDir := rootDir / s!"ep-txbusy-{idx}"
  try
    let stInit ← setupEpisodeDir tpl false epDir
    let worldRef ← IO.mkRef stInit
    let trackerRef ← IO.mkRef tracker
    let opsCountRef ← IO.mkRef 0
    let mismatchRef ← IO.mkRef (none : Option String)
    let escapedRef ← IO.mkRef (#[] : Array DbHandle)
    withDbLockstep epDir .db0 { walMode := false } 0 .returnOk worldRef trackerRef opsCountRef mismatchRef escapedRef
      fun db1 mDb1 => do
        runLeafLockstep {} db1 mDb1 false false (.exec "CREATE TABLE btx(x INT)" #[])
          worldRef trackerRef opsCountRef mismatchRef
        runLeafLockstep {} db1 mDb1 false false (.exec "BEGIN IMMEDIATE" #[])
          worldRef trackerRef opsCountRef mismatchRef
        withDbLockstep epDir .db0 { walMode := false, busyTimeoutMs := 0 } 1 .returnOk
          worldRef trackerRef opsCountRef mismatchRef escapedRef fun db2 mDb2 => do
            runTxLockstep {} db2 mDb2 false #[.exec "INSERT INTO btx VALUES (1)" #[]] .returnOk
              worldRef trackerRef opsCountRef mismatchRef
            return (.ok () : Except SqliteError Unit)
        runLeafLockstep {} db1 mDb1 false false (.exec "ROLLBACK" #[])
          worldRef trackerRef opsCountRef mismatchRef
        return (.ok () : Except SqliteError Unit)
    if let some msg ← mismatchRef.get then
      throw (IO.userError s!"SQLITE_TX_BUSY_PROBE_MISMATCH: {msg}")
    let tr ← trackerRef.get
    let nOps ← opsCountRef.get
    return (tr, nOps)
  finally
    cleanupEpisodeDir epDir

private def runCommitBusyWithTxProbe (tpl : EpisodeTemplate) (rootDir : System.FilePath) (attemptRef : IO.Ref Nat)
    (tracker : CoverageTracker) : IO (CoverageTracker × Nat) := do
  let idx ← attemptRef.modifyGet fun n => (n, n + 1)
  let epDir := rootDir / s!"ep-txcommitbusy-{idx}"
  try
    let stInit ← setupEpisodeDir tpl false epDir
    let worldRef ← IO.mkRef stInit
    let trackerRef ← IO.mkRef tracker
    let opsCountRef ← IO.mkRef 0
    let mismatchRef ← IO.mkRef (none : Option String)
    let escapedRef ← IO.mkRef (#[] : Array DbHandle)
    withDbLockstep epDir .db0 { walMode := false } 0 .returnOk worldRef trackerRef opsCountRef mismatchRef escapedRef
      fun db1 mDb1 => do
        runLeafLockstep {} db1 mDb1 false false (.exec "CREATE TABLE btx2(x INT)" #[])
          worldRef trackerRef opsCountRef mismatchRef
        withDbLockstep epDir .db0 { walMode := false, busyTimeoutMs := 0 } 1 .returnOk
          worldRef trackerRef opsCountRef mismatchRef escapedRef fun db2 mDb2 => do
            runLeafLockstep {} db2 mDb2 false false (.exec "BEGIN DEFERRED" #[])
              worldRef trackerRef opsCountRef mismatchRef
            runLeafLockstep {} db2 mDb2 false false (.query "SELECT x FROM btx2" #[])
              worldRef trackerRef opsCountRef mismatchRef
            runTxLockstep {} db1 mDb1 false #[.exec "INSERT INTO btx2 VALUES (1)" #[]] .returnOk
              worldRef trackerRef opsCountRef mismatchRef
            runLeafLockstep {} db2 mDb2 false false (.exec "ROLLBACK" #[])
              worldRef trackerRef opsCountRef mismatchRef
            return (.ok () : Except SqliteError Unit)
        runTxLockstep {} db1 mDb1 false #[.exec "INSERT INTO btx2 VALUES (2)" #[]] .returnOk
          worldRef trackerRef opsCountRef mismatchRef
        runLeafLockstep {} db1 mDb1 false false (.query "SELECT x FROM btx2 ORDER BY x ASC" #[])
          worldRef trackerRef opsCountRef mismatchRef
        return (.ok () : Except SqliteError Unit)
    if let some msg ← mismatchRef.get then
      throw (IO.userError s!"SQLITE_TX_COMMIT_BUSY_PROBE_MISMATCH: {msg}")
    let tr ← trackerRef.get
    let nOps ← opsCountRef.get
    return (tr, nOps)
  finally
    cleanupEpisodeDir epDir

private def episodeFailsTagged (tpl : EpisodeTemplate) (rootDir : System.FilePath) (attemptRef : IO.Ref Nat)
    (oracleCfg : OracleBugConfig) (expectedTag? : Option String) (ep : SqliteEpisode) : IO Bool := do
  let (_, _, mm?) ← runEpisode tpl rootDir attemptRef oracleCfg ep CoverageTracker.empty
  match expectedTag?, mm? with
  | _, none => return false
  | none, some _ => return true
  | some tag, some msg => return mismatchTag msg == tag

private def shrinkEpisode (tpl : EpisodeTemplate) (rootDir : System.FilePath) (attemptRef : IO.Ref Nat)
    (oracleCfg : OracleBugConfig) (initMsg : String) (ep : SqliteEpisode) : IO SqliteEpisode := do
  let pred := episodeFailsTagged tpl rootDir attemptRef oracleCfg (some (mismatchTag initMsg))
  let mut cur := ep
  for _ in List.range 4 do
    let p1 ← shrinkTrace pred cur
    let p2 ← shrinkElements shrinkTopAction pred p1
    if p2 == cur then
      return p2
    cur := p2
  return cur

private def unwrapOrThrow {α : Type} (msg : String) : Except SqliteError α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{msg}: {repr e}")

private def removeFileQuiet (p : System.FilePath) : IO Unit :=
  try IO.FS.removeFile p catch _ => pure ()

private def runFinalizeRaceProbe (realDb : DbHandle) : IO Unit := do
  let bind200Sql := "SELECT " ++ String.intercalate "," (List.replicate 200 "?")
  let bind200Params : Array SqliteValue := Array.replicate 200 (.int 7)
  for _ in List.range 20 do
    let bStmt ← unwrapOrThrow "SQLITE_THREAD_PROBE_BIND_PREP_ERR"
      (← LeanSwe.Sqlite.Raw.prepare realDb bind200Sql)
    let tBind ← IO.asTask do
      match ← LeanSwe.Sqlite.Raw.bind bStmt bind200Params with
      | .ok () => pure ()
      | .error e =>
        if e.kind != .misuse then
          throw (IO.userError s!"SQLITE_THREAD_PROBE_BIND_RACE_ERR: {repr e}")
    let tFin ← IO.asTask do
      let _ ← LeanSwe.Sqlite.Raw.finalize bStmt
      pure ()
    match tBind.get with | .error e => throw e | .ok () => pure ()
    match tFin.get with | .error e => throw e | .ok () => pure ()
    let _ ← LeanSwe.Sqlite.Raw.finalize bStmt
  for _ in List.range 20 do
    let sRace ← unwrapOrThrow "SQLITE_THREAD_PROBE_STEPFIN_PREP_ERR"
      (← LeanSwe.Sqlite.Raw.prepare realDb "SELECT id, txt, bin FROM th ORDER BY id ASC")
    let tStep ← IO.asTask do
      match ← LeanSwe.Sqlite.Raw.step sRace with
      | .ok _ => pure ()
      | .error e =>
        if e.kind != .misuse then
          throw (IO.userError s!"SQLITE_THREAD_PROBE_STEP_RACE_ERR: {repr e}")
    let tFin ← IO.asTask do
      let _ ← LeanSwe.Sqlite.Raw.finalize sRace
      pure ()
    match tStep.get with | .error e => throw e | .ok () => pure ()
    match tFin.get with | .error e => throw e | .ok () => pure ()
    let _ ← LeanSwe.Sqlite.Raw.finalize sRace

private def runReprepareRaceProbe (rootDir : System.FilePath) : IO Unit := do
  let repPath := (rootDir / "reprepare_probe.sqlite").toString
  let repDb1 ← unwrapOrThrow "SQLITE_REPREP_OPEN1" (← LeanSwe.Sqlite.Raw.openDb repPath { walMode := true })
  let repDb2 ← unwrapOrThrow "SQLITE_REPREP_OPEN2" (← LeanSwe.Sqlite.Raw.openDb repPath { walMode := true })
  try
    let _ ← unwrapOrThrow "SQLITE_REPREP_CREATE"
      (← LeanSwe.Sqlite.exec repDb1 "CREATE TABLE IF NOT EXISTS rep(id INTEGER PRIMARY KEY, x INT)" #[])
    let _ ← unwrapOrThrow "SQLITE_REPREP_INS"
      (← LeanSwe.Sqlite.exec repDb1 "INSERT INTO rep VALUES (1, 10)" #[])
    let repStmt ← unwrapOrThrow "SQLITE_REPREP_PREP"
      (← LeanSwe.Sqlite.Raw.prepare repDb1 "SELECT id, x FROM rep WHERE id = ?")
    let tDdl ← IO.asTask do
      for i in List.range 20 do
        let _ ← unwrapOrThrow "SQLITE_REPREP_DDL"
          (← LeanSwe.Sqlite.exec repDb2 s!"CREATE TABLE IF NOT EXISTS rep_d{i}(z INT)" #[])
    for _ in List.range 30 do
      let _ ← unwrapOrThrow "SQLITE_REPREP_BIND" (← LeanSwe.Sqlite.Raw.bind repStmt #[.int 1])
      let sRes ← unwrapOrThrow "SQLITE_REPREP_STEP" (← LeanSwe.Sqlite.Raw.step repStmt)
      if !Model.sqliteRowBitEq (match sRes with | .row r => r | .done => #[]) #[.int 1, .int 10] then
        throw (IO.userError s!"SQLITE_REPREP_STEP_ROW: {repr sRes}")
    let ddlRes := tDdl.get
    let _ ← unwrapOrThrow "SQLITE_REPREP_FIN" (← LeanSwe.Sqlite.Raw.finalize repStmt)
    if let .error e := ddlRes then throw e
  finally
    let c2 ← LeanSwe.Sqlite.Raw.closeDb repDb2
    let c1 ← LeanSwe.Sqlite.Raw.closeDb repDb1
    removeFileQuiet repPath
    let _ ← unwrapOrThrow "SQLITE_REPREP_CLOSE2" c2
    let _ ← unwrapOrThrow "SQLITE_REPREP_CLOSE1" c1

private def runBusyLockGrowthProbe (rootDir : System.FilePath) : IO Unit := do
  let busyPath := (rootDir / "busy_lock_probe.sqlite").toString
  try
    let busyHitsRef ← IO.mkRef 0
    let outerRes ← LeanSwe.Sqlite.withDb busyPath { walMode := false } fun db1 => do
      let _ ← unwrapOrThrow "SQLITE_BUSY_PROBE_CREATE" (← LeanSwe.Sqlite.exec db1 "CREATE TABLE bl(x INT)" #[])
      let _ ← unwrapOrThrow "SQLITE_BUSY_PROBE_BEGIN" (← LeanSwe.Sqlite.exec db1 "BEGIN IMMEDIATE" #[])
      let _ ← unwrapOrThrow "SQLITE_BUSY_PROBE_INS" (← LeanSwe.Sqlite.exec db1 "INSERT INTO bl VALUES (1)" #[])
      for _ in List.range 500 do
        let res2 ← LeanSwe.Sqlite.withDb busyPath { walMode := false, busyTimeoutMs := 0 } fun db2 =>
          LeanSwe.Sqlite.exec db2 "INSERT INTO bl VALUES (2)" #[]
        match res2 with
        | .error e =>
          if e.kind == .busy then busyHitsRef.modify (· + 1)
          else throw (IO.userError s!"SQLITE_BUSY_PROBE_UNEXPECTED_ERR: {repr e}")
        | .ok () => throw (IO.userError "SQLITE_BUSY_PROBE_UNEXPECTED_OK")
      let _ ← unwrapOrThrow "SQLITE_BUSY_PROBE_ROLLBACK" (← LeanSwe.Sqlite.exec db1 "ROLLBACK" #[])
      return (.ok () : Except SqliteError Unit)
    let _ ← unwrapOrThrow "SQLITE_BUSY_PROBE_OUTER" outerRes
    if (← busyHitsRef.get) != 500 then
      throw (IO.userError s!"SQLITE_THREAD_PROBE_BUSY_COUNT hits={← busyHitsRef.get}")
  finally
    removeFileQuiet busyPath

private def runWithDbBusyCloseProbe (rootDir : System.FilePath) : IO Unit := do
  let waitPath := (rootDir / "withdb_err_close_probe.sqlite").toString
  try
    let heldRef ← IO.mkRef (none : Option (DbHandle × StmtHandle))
    let resBusy ← LeanSwe.Sqlite.withDb waitPath {} fun db => do
      let _ ← unwrapOrThrow "SQLITE_WITHDB_BUSY_CREATE"
        (← LeanSwe.Sqlite.exec db "CREATE TABLE wl(id INTEGER PRIMARY KEY)" #[])
      let s ← unwrapOrThrow "SQLITE_WITHDB_BUSY_PREP"
        (← LeanSwe.Sqlite.Raw.prepare db "SELECT id FROM wl")
      heldRef.set (some (db, s))
      return (.ok () : Except SqliteError Unit)
    match resBusy with
    | .error e =>
      if e.kind != .busy then
        throw (IO.userError s!"SQLITE_WITHDB_BUSY_ERR_PROP_FAILED got={repr e}")
    | .ok () =>
      throw (IO.userError "SQLITE_WITHDB_BUSY_ERR_PROP_MISSING")
    if let some (db, s) ← heldRef.get then
      let _ ← unwrapOrThrow "SQLITE_WITHDB_BUSY_FIN" (← LeanSwe.Sqlite.Raw.finalize s)
      let _ ← unwrapOrThrow "SQLITE_WITHDB_BUSY_CLOSE" (← LeanSwe.Sqlite.Raw.closeDb db)
    heldRef.set none
    let resPrimary ← LeanSwe.Sqlite.withDb waitPath {} fun db => do
      let s ← unwrapOrThrow "SQLITE_WITHDB_PRIMARY_PREP"
        (← LeanSwe.Sqlite.Raw.prepare db "SELECT id FROM wl")
      heldRef.set (some (db, s))
      return (Except.error { kind := .invalidInput, message := "caller abort" } : Except SqliteError Unit)
    match resPrimary with
    | .error e =>
      if e.kind != .invalidInput || e.message != "caller abort" then
        throw (IO.userError s!"SQLITE_WITHDB_PRIMARY_ERR_PROP_FAILED got={repr e}")
    | .ok () =>
      throw (IO.userError "SQLITE_WITHDB_PRIMARY_ERR_PROP_MISSING")
    if let some (db, s) ← heldRef.get then
      let _ ← unwrapOrThrow "SQLITE_WITHDB_PRIMARY_FIN" (← LeanSwe.Sqlite.Raw.finalize s)
      let _ ← unwrapOrThrow "SQLITE_WITHDB_PRIMARY_CLOSE" (← LeanSwe.Sqlite.Raw.closeDb db)
  finally
    removeFileQuiet waitPath

private def runThreadedStepSafetyProbe (rootDir : System.FilePath) : IO Unit := do
  let realDb ← unwrapOrThrow "SQLITE_THREAD_PROBE_OPEN_ERR"
    (← LeanSwe.Sqlite.Raw.openDb ":memory:" {})
  try
    for sql in #[
      "CREATE TABLE th(id INTEGER PRIMARY KEY, txt TEXT, bin BLOB)",
      "INSERT INTO th VALUES (1, 'alpha', X'010203'), (2, 'beta', X''), (3, NULL, X'AA')"
    ] do
      let s ← unwrapOrThrow "SQLITE_THREAD_PROBE_STEP_PREP_ERR" (← LeanSwe.Sqlite.Raw.prepare realDb sql)
      let sRes ← LeanSwe.Sqlite.Raw.step s
      let _ ← LeanSwe.Sqlite.Raw.finalize s
      let _ ← unwrapOrThrow "SQLITE_THREAD_PROBE_STEP_ERR" sRes
    let stmt ← unwrapOrThrow "SQLITE_THREAD_PROBE_QPREP_ERR"
      (← LeanSwe.Sqlite.Raw.prepare realDb "SELECT id, txt, bin FROM th ORDER BY id ASC")
    let validRows : List SqliteRow :=
      [ #[.int 1, .text "alpha", .bytes (ByteArray.mk #[1, 2, 3])]
      , #[.int 2, .text "beta", .bytes ByteArray.empty]
      , #[.int 3, .null, .bytes (ByteArray.mk #[0xAA])] ]
    let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
    for _ in List.range 4 do
      let t ← IO.asTask do
        for _ in List.range 50 do
          match ← LeanSwe.Sqlite.Raw.step stmt with
          | .error e => throw (IO.userError s!"SQLITE_THREAD_PROBE_RACESTEP: {repr e}")
          | .ok .done => pure ()
          | .ok (.row row) =>
            if !validRows.contains row then
              throw (IO.userError s!"SQLITE_THREAD_PROBE_TORN_ROW row={repr row}")
      tasks := tasks.push t
    let mut taskErr? : Option IO.Error := none
    for t in tasks do
      if let .error e := t.get then
        if taskErr?.isNone then taskErr? := some e
    let _ ← LeanSwe.Sqlite.Raw.finalize stmt
    if let some e := taskErr? then throw e
    let mut multiTasks : Array (Task (Except IO.Error Unit)) := #[]
    for _ in List.range 4 do
      let t ← IO.asTask do
        for _ in List.range 20 do
          let ms ← unwrapOrThrow "SQLITE_THREAD_PROBE_MULTI_PREP"
            (← LeanSwe.Sqlite.Raw.prepare realDb "SELECT id, txt, bin FROM th ORDER BY id ASC")
          try
            let mut finished := false
            while !finished do
              match ← LeanSwe.Sqlite.Raw.step ms with
              | .error e => throw (IO.userError s!"SQLITE_THREAD_PROBE_MULTISTMT_STEP: {repr e}")
              | .ok .done => finished := true
              | .ok (.row row) =>
                if !validRows.contains row then
                  throw (IO.userError s!"SQLITE_THREAD_PROBE_MULTISTMT_TORN row={repr row}")
          finally
            let _ ← LeanSwe.Sqlite.Raw.finalize ms
      multiTasks := multiTasks.push t
    for t in multiTasks do
      if let .error e := t.get then
        if taskErr?.isNone then taskErr? := some e
    if let some e := taskErr? then throw e
    runFinalizeRaceProbe realDb
  finally
    let _ ← LeanSwe.Sqlite.Raw.closeDb realDb
  runReprepareRaceProbe rootDir
  runBusyLockGrowthProbe rootDir
  runWithDbBusyCloseProbe rootDir
  let dbs ← LeanSwe.Sqlite.Raw.activeDbCount
  let stmts ← LeanSwe.Sqlite.Raw.activeStmtCount
  if dbs != 0 || stmts != 0 then
    throw (IO.userError s!"SQLITE_THREAD_PROBE_LEAK dbs={dbs} stmts={stmts}")

private def runCorruptBeginImmProbe (rootDir : System.FilePath) : IO Unit := do
  let corruptPath := (rootDir / "raw_corrupt_probe.sqlite").toString
  IO.FS.writeBinFile corruptPath (ByteArray.mk (Array.replicate 128 0xAA))
  let stC0 : Model.SqliteWorldState := { existingDirs := ["/", rootDir.toString], files := [(corruptPath, .corruptFile)] }
  let rCDb ← unwrapOrThrow "SQLITE_RAW_CORRUPT_OPEN_R"
    (← LeanSwe.Sqlite.Raw.openDb corruptPath { walMode := false })
  let (mCDbRes, stC1) := Model.modelRawOps.openDb corruptPath { walMode := false } stC0
  let mCDb ← unwrapOrThrow "SQLITE_RAW_CORRUPT_OPEN_M" mCDbRes
  try
    let rCSt ← unwrapOrThrow "SQLITE_RAW_CORRUPT_PREP_R"
      (← LeanSwe.Sqlite.Raw.prepare rCDb "BEGIN IMMEDIATE")
    let (mCStRes, stC2) := Model.modelRawOps.prepare mCDb "BEGIN IMMEDIATE" stC1
    let mCSt ← unwrapOrThrow "SQLITE_RAW_CORRUPT_PREP_M" mCStRes
    let rCS ← LeanSwe.Sqlite.Raw.step rCSt
    let (mCS, stC3) := Model.modelRawOps.step mCSt stC2
    let rCFin ← LeanSwe.Sqlite.Raw.finalize rCSt
    let (mCFin, _) := Model.modelRawOps.finalize mCSt stC3
    let finMatch := match rCFin, mCFin with
      | .ok (), .ok () => true
      | .error e1, .error e2 => errorsMatch e1 e2
      | _, _ => false
    if !stepResultMatches rCS mCS || !finMatch then
      throw (IO.userError s!"SQLITE_RAW_CORRUPT_BEGIN_IMM_MISMATCH real={repr rCS} model={repr mCS} rFin={repr rCFin} mFin={repr mCFin}")
  finally
    let cRes ← LeanSwe.Sqlite.Raw.closeDb rCDb
    removeFileQuiet corruptPath
    let _ ← unwrapOrThrow "SQLITE_RAW_CORRUPT_CLOSE_R" cRes

private def runMidscanLockProbe (rootDir : System.FilePath) : IO Unit := do
  let scanPath := (rootDir / "raw_midscan_probe.sqlite").toString
  let stM0 : Model.SqliteWorldState := { existingDirs := ["/", rootDir.toString] }
  let rMDb1 ← unwrapOrThrow "SQLITE_RAW_SCAN_OPEN1"
    (← LeanSwe.Sqlite.Raw.openDb scanPath { walMode := false, busyTimeoutMs := 0 })
  let (mMDb1Res, stM1) := Model.modelRawOps.openDb scanPath { walMode := false, busyTimeoutMs := 0 } stM0
  let mMDb1 ← unwrapOrThrow "SQLITE_RAW_SCAN_MOPEN1" mMDb1Res
  try
    let _ ← unwrapOrThrow "SQLITE_RAW_SCAN_CREATE_R"
      (← LeanSwe.Sqlite.exec rMDb1 "CREATE TABLE sc(id INTEGER PRIMARY KEY)" #[])
    let _ ← unwrapOrThrow "SQLITE_RAW_SCAN_INS_R"
      (← LeanSwe.Sqlite.exec rMDb1 "INSERT INTO sc VALUES (1), (2)" #[])
    let (mCRes, stM2) := (Model.modelApi.exec mMDb1 "CREATE TABLE sc(id INTEGER PRIMARY KEY)" #[]).run stM1
    let _ ← unwrapOrThrow "SQLITE_RAW_SCAN_CREATE_M" mCRes
    let (mIRes, stM3) := (Model.modelApi.exec mMDb1 "INSERT INTO sc VALUES (1), (2)" #[]).run stM2
    let _ ← unwrapOrThrow "SQLITE_RAW_SCAN_INS_M" mIRes
    let rMSt ← unwrapOrThrow "SQLITE_RAW_SCAN_PREP_R"
      (← LeanSwe.Sqlite.Raw.prepare rMDb1 "SELECT id FROM sc ORDER BY id ASC")
    let (mMStRes, stM4) := Model.modelRawOps.prepare mMDb1 "SELECT id FROM sc ORDER BY id ASC" stM3
    let mMSt ← unwrapOrThrow "SQLITE_RAW_SCAN_PREP_M" mMStRes
    let rMS1 ← LeanSwe.Sqlite.Raw.step rMSt
    let (mMS1, stM5) := Model.modelRawOps.step mMSt stM4
    let rW2 ← LeanSwe.Sqlite.withDb scanPath { walMode := false, busyTimeoutMs := 0 } fun d2 =>
      LeanSwe.Sqlite.exec d2 "INSERT INTO sc VALUES (3)" #[]
    let (mW2, stM6) := (Model.modelApi.withDb scanPath { walMode := false, busyTimeoutMs := 0 } fun md2 =>
      Model.modelApi.exec md2 "INSERT INTO sc VALUES (3)" #[]).run stM5
    let _ ← unwrapOrThrow "SQLITE_RAW_SCAN_FIN_R" (← LeanSwe.Sqlite.Raw.finalize rMSt)
    let _ ← unwrapOrThrow "SQLITE_RAW_SCAN_FIN_M" (Model.modelRawOps.finalize mMSt stM6).1
    let w2Match := match rW2, mW2 with | .error e1, .error e2 => errorsMatch e1 e2 | _, _ => false
    if !stepResultMatches rMS1 mMS1 || !w2Match then
      throw (IO.userError s!"SQLITE_RAW_MIDSCAN_MISMATCH rMS1={repr rMS1} mMS1={repr mMS1} rW2={repr rW2} mW2={repr mW2}")
  finally
    let cRes ← LeanSwe.Sqlite.Raw.closeDb rMDb1
    removeFileQuiet scanPath
    let _ ← unwrapOrThrow "SQLITE_RAW_SCAN_CLOSE_R" cRes

private def runRawApiProbe (rootDir : System.FilePath) : IO Unit := do
  runThreadedStepSafetyProbe rootDir
  let realDb ← unwrapOrThrow "SQLITE_RAW_PROBE_OPEN_ERR"
    (← LeanSwe.Sqlite.Raw.openDb ":memory:" {})
  let mut st : Model.SqliteWorldState := {}
  let (mOpen, st1) := Model.modelRawOps.openDb ":memory:" {} st
  st := st1
  let modelDb ←
    match mOpen with
    | .ok d => pure d
    | .error e =>
      let _ ← LeanSwe.Sqlite.Raw.closeDb realDb
      throw (IO.userError s!"SQLITE_RAW_PROBE_MODEL_OPEN_ERR: {repr e}")
  let probeSqls : Array String :=
    #[ "SELECT  \x0b 1"
     , " \x0bSELECT 1"
     , "SELECT 1; \x0b"
     , "SELECT 1; -- c\n\x0b"
     , "SELECT 1; /* ok */ \x0b"
     , "SELECT 1;\x0b"
     , "SELECT 1; /* ok */\x0b"
     , "SELECT 1; /* unclosed"
     , "SELECT 1 /* unclosed"
     , "SELECT 1 /*"
     , "/*"
     , "\uFEFF\x0bSELECT 1"
     , "SELECT\uFEFF 1"
     , "SELECT 1\uFEFF"
     , "SELECT 1;;"
     , "\uFEFFSELECT 1"
     , "SELECT \uFEFF 1"
     , "SELECT 1;\uFEFF"
     , "SELECT 1;\uFEFF\x0b"
     , ";SELECT 1"
     , ";;;SELECT 1"
     , ";" ]
  try
    for sql in probeSqls do
      let resReal ← LeanSwe.Sqlite.Raw.prepare realDb sql
      let (resModel, stNext) := Model.modelRawOps.prepare modelDb sql st
      st := stNext
      match resReal, resModel with
      | .ok rStmt, .ok mStmt =>
        let rPS ← LeanSwe.Sqlite.Raw.step rStmt
        let (mPS, stPS) := Model.modelRawOps.step mStmt st
        st := stPS
        if !stepResultMatches rPS mPS then
          let _ ← LeanSwe.Sqlite.Raw.finalize rStmt
          let (_, stFin) := Model.modelRawOps.finalize mStmt st
          st := stFin
          throw (IO.userError s!"SQLITE_RAW_PROBE_STEP_MISMATCH sql={repr sql} real={repr rPS} model={repr mPS}")
        let rFin ← unwrapOrThrow "SQLITE_RAW_PROBE_FIN_R" (← LeanSwe.Sqlite.Raw.finalize rStmt)
        let (mFinRes, stFin) := Model.modelRawOps.finalize mStmt st
        let _ ← unwrapOrThrow "SQLITE_RAW_PROBE_FIN_M" mFinRes
        let _ := rFin
        st := stFin
      | .error eReal, .error eModel =>
        if !errorsMatch eReal eModel then
          throw (IO.userError
            s!"SQLITE_RAW_PREPARE_MISMATCH sql={repr sql} real={repr eReal} model={repr eModel}")
      | .ok rStmt, .error eModel =>
        let _ ← LeanSwe.Sqlite.Raw.finalize rStmt
        throw (IO.userError
          s!"SQLITE_RAW_PREPARE_OUTCOME_MISMATCH sql={repr sql} real=.ok model={repr eModel}")
      | .error eReal, .ok mStmt =>
        let (_, stFin) := Model.modelRawOps.finalize mStmt st
        st := stFin
        throw (IO.userError
          s!"SQLITE_RAW_PREPARE_OUTCOME_MISMATCH sql={repr sql} real={repr eReal} model=.ok")
    let rP ← LeanSwe.Sqlite.Raw.prepare realDb "SELECT ?"
    let (mP, stP) := Model.modelRawOps.prepare modelDb "SELECT ?" st
    st := stP
    match rP, mP with
    | .ok rs, .ok ms =>
      let _ ← unwrapOrThrow "SQLITE_RAW_PROBE_BIND_R" (← LeanSwe.Sqlite.Raw.bind rs #[.int 7])
      let (mb1, st1b) := Model.modelRawOps.bind ms #[.int 7] st
      let _ ← unwrapOrThrow "SQLITE_RAW_PROBE_BIND_M" mb1
      let sr1 ← LeanSwe.Sqlite.Raw.step rs
      let (sm1, st2) := Model.modelRawOps.step ms st1b
      let sr2 ← LeanSwe.Sqlite.Raw.step rs
      let (sm2, st3) := Model.modelRawOps.step ms st2
      let sr3 ← LeanSwe.Sqlite.Raw.step rs
      let (sm3, st4) := Model.modelRawOps.step ms st3
      let rbErr ← LeanSwe.Sqlite.Raw.bind rs #[]
      let (mbErr, st5) := Model.modelRawOps.bind ms #[] st4
      let sr4 ← LeanSwe.Sqlite.Raw.step rs
      let (sm4, st6) := Model.modelRawOps.step ms st5
      st := st6
      let _ ← unwrapOrThrow "SQLITE_RAW_PROBE_FIN2_R" (← LeanSwe.Sqlite.Raw.finalize rs)
      let (mf2, stFin2) := Model.modelRawOps.finalize ms st
      let _ ← unwrapOrThrow "SQLITE_RAW_PROBE_FIN2_M" mf2
      st := stFin2
      if !stepResultMatches sr1 sm1 || !stepResultMatches sr2 sm2 ||
          !stepResultMatches sr3 sm3 || !stepResultMatches sr4 sm4 then
        throw (IO.userError s!"SQLITE_RAW_STEP_REUSE_MISMATCH {repr sr1}/{repr sm1} {repr sr2}/{repr sm2} {repr sr3}/{repr sm3} {repr sr4}/{repr sm4}")
      match rbErr, mbErr with
      | .error e1, .error e2 =>
        if !errorsMatch e1 e2 then
          throw (IO.userError s!"SQLITE_RAW_BIND_ERR_MISMATCH real={repr e1} model={repr e2}")
      | _, _ => throw (IO.userError s!"SQLITE_RAW_BIND_OUTCOME_MISMATCH real={repr rbErr} model={repr mbErr}")
    | _, _ => throw (IO.userError "SQLITE_RAW_PROBE_SELECT_Q_PREP_FAILED")

    let _ ← unwrapOrThrow "SQLITE_RAW_PROBE_STICKY_CR"
      (← LeanSwe.Sqlite.exec realDb "CREATE TABLE u_sticky(x INT UNIQUE)" #[])
    let _ ← unwrapOrThrow "SQLITE_RAW_PROBE_STICKY_IR"
      (← LeanSwe.Sqlite.exec realDb "INSERT INTO u_sticky VALUES (1)" #[])
    let (mCr, stCr) := (Model.modelApi.exec modelDb "CREATE TABLE u_sticky(x INT UNIQUE)" #[]).run st
    let _ ← unwrapOrThrow "SQLITE_RAW_PROBE_STICKY_CM" mCr
    let (mIn, stIn) := (Model.modelApi.exec modelDb "INSERT INTO u_sticky VALUES (1)" #[]).run stCr
    let _ ← unwrapOrThrow "SQLITE_RAW_PROBE_STICKY_IM" mIn
    let rStk ← unwrapOrThrow "SQLITE_RAW_PROBE_STICKY_PREP_R"
      (← LeanSwe.Sqlite.Raw.prepare realDb "INSERT INTO u_sticky VALUES (?)")
    let (mStkRes, stStk) := Model.modelRawOps.prepare modelDb "INSERT INTO u_sticky VALUES (?)" stIn
    let mStk ← unwrapOrThrow "SQLITE_RAW_PROBE_STICKY_PREP_M" mStkRes
    st := stStk
    let _ ← unwrapOrThrow "SQLITE_RAW_PROBE_STICKY_BR" (← LeanSwe.Sqlite.Raw.bind rStk #[.int 1])
    let (mB1, stB1) := Model.modelRawOps.bind mStk #[.int 1] st
    let _ ← unwrapOrThrow "SQLITE_RAW_PROBE_STICKY_BM" mB1
    let rS1 ← LeanSwe.Sqlite.Raw.step rStk
    let (mS1, stStk1) := Model.modelRawOps.step mStk stB1
    let rB2 ← LeanSwe.Sqlite.Raw.bind rStk #[.int 2]
    let (mB2, stStk2) := Model.modelRawOps.bind mStk #[.int 2] stStk1
    let rS2 ← LeanSwe.Sqlite.Raw.step rStk
    let (mS2, stStk3) := Model.modelRawOps.step mStk stStk2
    let _ ← unwrapOrThrow "SQLITE_RAW_PROBE_STICKY_DR"
      (← LeanSwe.Sqlite.exec realDb "DELETE FROM u_sticky" #[])
    let (mDel, stStk4) := (Model.modelApi.exec modelDb "DELETE FROM u_sticky" #[]).run stStk3
    let _ ← unwrapOrThrow "SQLITE_RAW_PROBE_STICKY_DM" mDel
    let rS3 ← LeanSwe.Sqlite.Raw.step rStk
    let (mS3, stStk5) := Model.modelRawOps.step mStk stStk4
    let rRows ← LeanSwe.Sqlite.query realDb "SELECT x FROM u_sticky ORDER BY x ASC" #[]
    let (mRows, stStk6) := (Model.modelApi.query modelDb "SELECT x FROM u_sticky ORDER BY x ASC" #[]).run stStk5
    let _ ← unwrapOrThrow "SQLITE_RAW_PROBE_STICKY_FR" (← LeanSwe.Sqlite.Raw.finalize rStk)
    let (mFinS, stFinS) := Model.modelRawOps.finalize mStk stStk6
    let _ ← unwrapOrThrow "SQLITE_RAW_PROBE_STICKY_FM" mFinS
    st := stFinS
    let bindMatch := match rB2, mB2 with | .error e1, .error e2 => errorsMatch e1 e2 | _, _ => false
    let rowsMatch :=
      match rRows, mRows with
      | .ok a, .ok b => a.size == b.size && (List.zip a.toList b.toList).all (fun (x, y) => Model.sqliteRowBitEq x y)
      | _, _ => false
    if !stepResultMatches rS1 mS1 || !stepResultMatches rS2 mS2 || !stepResultMatches rS3 mS3 ||
        !bindMatch || !rowsMatch then
      throw (IO.userError s!"SQLITE_RAW_STICKY_BIND_MISMATCH rS1={repr rS1} mS1={repr mS1} rS2={repr rS2} mS2={repr mS2} rS3={repr rS3} mS3={repr mS3} rRows={repr rRows} mRows={repr mRows}")
    let rBadUtf8 ← unwrapOrThrow "SQLITE_RAW_BAD_UTF8_PREP"
      (← LeanSwe.Sqlite.Raw.prepare realDb "SELECT CAST(X'FF' AS TEXT)")
    let rBadStep ← LeanSwe.Sqlite.Raw.step rBadUtf8
    let _ ← unwrapOrThrow "SQLITE_RAW_BAD_UTF8_FIN" (← LeanSwe.Sqlite.Raw.finalize rBadUtf8)
    match rBadStep with
    | .error e =>
      if e.kind != .ioError || e.sqliteCode.isSome || e.message.isEmpty then
        throw (IO.userError s!"SQLITE_RAW_BAD_UTF8_UNEXPECTED_ERR: {repr e}")
    | .ok out =>
      throw (IO.userError s!"SQLITE_RAW_BAD_UTF8_EXPECTED_ERR: {repr out}")
  finally
    let cRes ← LeanSwe.Sqlite.Raw.closeDb realDb
    let _ ← unwrapOrThrow "SQLITE_RAW_PROBE_CLOSE" cRes
  runCorruptBeginImmProbe rootDir
  runMidscanLockProbe rootDir
  let dbs ← LeanSwe.Sqlite.Raw.activeDbCount
  let stmts ← LeanSwe.Sqlite.Raw.activeStmtCount
  if dbs != 0 || stmts != 0 then
    throw (IO.userError s!"SQLITE_RAW_PROBE_LEAK dbs={dbs} stmts={stmts}")

private def runWarmup (tpl : EpisodeTemplate) (rootDir : System.FilePath) (attemptRef : IO.Ref Nat)
    (tracker : CoverageTracker) : IO (CoverageTracker × Nat) := do
  runRawApiProbe rootDir
  let mut tr := tracker
  let mut totalOps := 0
  for ep in smokeCorpus do
    let (tr', nOps, mm?) ← runEpisode tpl rootDir attemptRef {} ep tr
    tr := tr'
    totalOps := totalOps + nOps
    if let some msg := mm? then
      let shrunk ← shrinkEpisode tpl rootDir attemptRef {} msg ep
      throw (IO.userError s!"SQLITE_FUZZ_SMOKE_MISMATCH: {msg}\nshrunk={repr shrunk}")
  let (trBusy, nBusy) ← runBusyWithTxProbe tpl rootDir attemptRef tr
  let (trCommitBusy, nCommitBusy) ← runCommitBusyWithTxProbe tpl rootDir attemptRef trBusy
  return (trCommitBusy, totalOps + nBusy + nCommitBusy)

private def safePrintln (s : String) : IO Unit := do
  try
    IO.println s
    (← IO.getStdout).flush
  catch _ =>
    pure ()

private def countOpenFds? : IO (Option Nat) := do
  try
    return some (← System.FilePath.readDir "/proc/self/fd").size
  catch _ =>
    return none

private def assertNoFdLeak (ctx : String) (before? after? : Option Nat) : IO Unit := do
  match before?, after? with
  | some b, some a =>
    if a > b then
      throw (IO.userError s!"SQLITE_FD_LEAK ctx={ctx} before={b} after={a}")
  | _, _ => pure ()

private def runSqliteSmoke (cfg : FuzzConfig) : IO Unit := do
  let rootDir ← getFuzzRootDir
  let attemptRef ← IO.mkRef 0
  try
    let tpl ← prepareEpisodeTemplate rootDir
    let (tr, nOps) ← runWarmup tpl rootDir attemptRef CoverageTracker.empty
    let fdBase? ← countOpenFds?
    let (tr2, nOps2) ← runWarmup tpl rootDir attemptRef tr
    let fdAfter? ← countOpenFds?
    assertNoFdLeak "smoke" fdBase? fdAfter?
    assertCoverage "sqlite" tr2 requiredBuckets
    safePrintln (tr2.formatReport "sqlite")
    safePrintln s!"FUZZ_SUMMARY suite=sqlite mode=smoke steps={nOps + nOps2} seed={cfg.seed}"
  finally
    forceRemoveDirAll rootDir

private def runSqliteFuzz (cfg : FuzzConfig) : IO Unit := do
  let rootDir ← getFuzzRootDir
  let attemptRef ← IO.mkRef 0
  try
    let tpl ← prepareEpisodeTemplate rootDir
    let (trWarmup, _) ← runWarmup tpl rootDir attemptRef CoverageTracker.empty
    assertCoverage "sqlite" trWarmup requiredBuckets
    let fdBase? ← countOpenFds?
    let mut tr := CoverageTracker.empty
    let mut rng := Rng.seed cfg.seed
    let mut done := 0
    while done < cfg.steps do
      let (ep, rNext) := Gen.genEpisode rng
      rng := rNext
      let (tr', nOps, mm?) ← runEpisode tpl rootDir attemptRef {} ep tr
      tr := tr'
      done := done + nOps
      if let some msg := mm? then
        let shrunk ← shrinkEpisode tpl rootDir attemptRef {} msg ep
        throw (IO.userError
          s!"SQLITE_FUZZ_MISMATCH seed={cfg.seed} steps={done}: {msg}\nshrunk_size={shrunk.size} shrunk={repr shrunk}")
    let fdAfter? ← countOpenFds?
    assertNoFdLeak "fuzz" fdBase? fdAfter?
    if cfg.steps >= 10000 then
      assertCoverage "sqlite" tr requiredBuckets
    safePrintln (tr.formatReport "sqlite")
    safePrintln s!"FUZZ_SUMMARY suite=sqlite mode=fuzz steps={done} seed={cfg.seed}"
  finally
    forceRemoveDirAll rootDir

private def totalInnerOps (ep : SqliteEpisode) : Nat :=
  ep.foldl (init := 0) fun acc act =>
    match act with
    | .withDbSession _ _ ops _ => acc + ops.size
    | .closedHandleTx _ txOps _ => acc + txOps.size
    | .rawSession _ _ ops => acc + ops.size
    | _ => acc + 1

private def runSqliteSelfTestShrink (seedVal : UInt64) : IO Unit := do
  let rootDir ← getFuzzRootDir
  let attemptRef ← IO.mkRef 0
  let bugCfg : OracleBugConfig := { dropWhereOnTable? := some "t_sh" }
  try
    let tpl ← prepareEpisodeTemplate rootDir
    let mut rng := Rng.seed (seedVal ^^^ 0xa5a5a5a55a5a5a5a)
    let mut prefixActs : Array TopAction := #[]
    for _ in List.range 10 do
      let (act, r') := Gen.genTopAction rng
      rng := r'
      prefixActs := prefixActs.push act
    let mut suffixActs : Array TopAction := #[]
    for _ in List.range 10 do
      let (act, r') := Gen.genTopAction rng
      rng := r'
      suffixActs := suffixActs.push act
    let faultSess1 : TopAction := .withDbSession .db0 {} #[
      .leaf (.exec "CREATE TABLE t_sh(id INTEGER PRIMARY KEY, x INT)" #[]),
      .leaf (.exec "INSERT INTO t_sh(id, x) VALUES (?, ?)" #[.int 1, .int 10]),
      .leaf (.exec "INSERT INTO t_sh(id, x) VALUES (?, ?)" #[.int 2, .int 20])
    ] .returnOk
    let faultSess2 : TopAction := .withDbSession .db0 {} #[
      .nestedWithDb .db0 { walMode := true } #[
        (true, .queryOne "SELECT id FROM t_sh WHERE x = ?" #[.int 999])
      ] .returnOk
    ] .returnOk
    let ep := (prefixActs.push faultSess1).push faultSess2 ++ suffixActs
    let origInner := totalInnerOps ep
    let (_, _, initMm?) ← runEpisode tpl rootDir attemptRef bugCfg ep CoverageTracker.empty
    let initMsg ←
      match initMm? with
      | some m => pure m
      | none => throw (IO.userError "SQLITE_SHRINK_SELFTEST_FAULT_DID_NOT_TRIGGER")
    let shrunk ← shrinkEpisode tpl rootDir attemptRef bugCfg initMsg ep
    if !(← episodeFailsTagged tpl rootDir attemptRef bugCfg (some (mismatchTag initMsg)) shrunk) then
      throw (IO.userError "SQLITE_SHRINK_SELFTEST_SHRUNK_LOST_FAILURE")
    let hasUnwrappedLeaf := shrunk.any fun
      | .withDbSession _ _ ops _ => ops.any fun | .leaf (.queryOne _ _) => true | _ => false
      | _ => false
    if !hasUnwrappedLeaf then
      throw (IO.userError s!"SQLITE_SHRINK_SELFTEST_NESTED_TRUE_NOT_UNWRAPPED: {repr shrunk}")
    let tUnique := mismatchTag "EXEC_ERR_MISMATCH sql=\"X\" real={ kind := .constraint,\n  sqliteCode := some 1555,\n  message := \"u\" } model={ kind := .constraint,\n  sqliteCode := some 2067,\n  message := \"u\" }"
    let tNone := mismatchTag "EXEC_ERR_MISMATCH sql=\"X\" real={ kind := .constraint,\n  sqliteCode := none,\n  message := \"u\" } model={ kind := .constraint,\n  sqliteCode := some 2067,\n  message := \"u\" }"
    let tIo := mismatchTag "EXEC_ERR_MISMATCH sql=\"Y\" real={ kind := .ioError, sqliteCode := some 1, message := \"s\" } model={ kind := .ioError, sqliteCode := some 8, message := \"r\" }"
    let tQSome := mismatchTag "QUERYONE_ROW_MISMATCH sql=\"Z\" params=#[] real=(some #[SqliteValue.int 1]) model=none"
    let tQNone := mismatchTag "QUERYONE_ROW_MISMATCH sql=\"Z\" params=#[] real=none model=(some #[SqliteValue.int 1])"
    let tSR := mismatchTag "RAW_STEP_MISMATCH real=Except.ok (LeanSwe.Sqlite.Raw.StepResult.row #[SqliteValue.int 1]) model=Except.ok (LeanSwe.Sqlite.Raw.StepResult.done)"
    let tSD := mismatchTag "RAW_STEP_MISMATCH real=Except.ok (LeanSwe.Sqlite.Raw.StepResult.done) model=Except.ok (LeanSwe.Sqlite.Raw.StepResult.row #[SqliteValue.int 1])"
    if tUnique == tIo || tUnique == tNone || tQSome == tQNone || tSR == tSD then
      throw (IO.userError s!"SQLITE_SHRINK_SELFTEST_TAG_COLLISION: {tUnique} / {tNone} / {tIo} / {tQSome} / {tQNone} / {tSR} / {tSD}")
    if (← episodeFailsTagged tpl rootDir attemptRef bugCfg (some tUnique) shrunk) then
      throw (IO.userError "SQLITE_SHRINK_SELFTEST_SLIPPAGE_ACCEPTED_WRONG_TAG")
    if shrunk.size > 2 then
      throw (IO.userError s!"SQLITE_SHRINK_SELFTEST_TOO_LARGE: expected <= 2 top actions, got {shrunk.size}: {repr shrunk}")
    let shrunkInner := totalInnerOps shrunk
    if shrunkInner > 4 || shrunkInner >= origInner then
      throw (IO.userError s!"SQLITE_SHRINK_SELFTEST_INNER_NOT_REDUCED: orig={origInner}, shrunk={shrunkInner}")
    let nestedSample : TopAction :=
      .withDbSession .db0 {} #[
        .nestedWithDb .db1 { walMode := true } #[
          (false, .exec "CREATE TABLE t_sh(id INTEGER PRIMARY KEY)" #[]),
          (false, .queryOne "SELECT id FROM t_sh" #[])
        ] .returnOk
      ] .returnOk
    let unwrappedNested : TopAction :=
      .withDbSession .db0 {} #[
        .leaf (.exec "CREATE TABLE t_sh(id INTEGER PRIMARY KEY)" #[]),
        .leaf (.queryOne "SELECT id FROM t_sh" #[])
      ] .returnOk
    if !(shrinkTopAction nestedSample).contains unwrappedNested then
      throw (IO.userError "SQLITE_SHRINK_SELFTEST_NESTED_SPLICE_MISSING")
    let rawPeerSample : TopAction :=
      .rawSession .db0 {} #[.rawPeerExec .db1 { walMode := true, busyTimeoutMs := 5 } "SELECT 1" #[]]
    if !(shrinkTopAction rawPeerSample).contains (.rawSession .db0 {} #[.peerExec "SELECT 1" #[]]) then
      throw (IO.userError "SQLITE_SHRINK_SELFTEST_RAWPEER_SIMP_MISSING")
    let coupledSlot1 : TopAction :=
      .rawSession .memory {} #[.prepare 1 "SELECT 1", .step 1, .finalize 1]
    if !(shrinkTopAction coupledSlot1).contains
        (.rawSession .memory {} #[.prepare 0 "SELECT 1", .step 0, .finalize 0]) then
      throw (IO.userError "SQLITE_SHRINK_SELFTEST_COUPLED_SLOT_MISSING")
    if !(shrinkTopAction (.rawSession (.exactPathBytes 512) {} #[])).contains
        (.rawSession (.exactPathBytes 505) {} #[]) then
      throw (IO.userError "SQLITE_SHRINK_SELFTEST_EXACT_PATH_MISSING")
    if !(shrinkTopAction (.rawSession (.intermDotDotBytes 600) {} #[])).contains
        (.rawSession (.intermDotDotBytes 512) {} #[]) then
      throw (IO.userError "SQLITE_SHRINK_SELFTEST_INTERM_PATH_MISSING")
    if !(shrinkTopAction (.validateConfig { busyTimeoutMs := maxBusyTimeoutMs + 100 })).contains
        (.validateConfig { busyTimeoutMs := maxBusyTimeoutMs + 1 }) then
      throw (IO.userError "SQLITE_SHRINK_SELFTEST_VALIDATE_CFG_MISSING")
    if (shrinkTopAction (.mapRawError (.sqliteCodeError 5 "detail"))).isEmpty then
      throw (IO.userError "SQLITE_SHRINK_SELFTEST_MAP_RAW_ERR_MISSING")
    if !(shrinkTopAction (.closedHandleOp (.escaped 2) (.exec "SELECT 1" #[]))).contains
        (.closedHandleOp .zero (.exec "SELECT 1" #[])) then
      throw (IO.userError "SQLITE_SHRINK_SELFTEST_CLOSED_REF_MISSING")
    safePrintln s!"SQLITE_SHRINK_SELFTEST_OK orig_top={ep.size} shrunk_top={shrunk.size} orig_inner={origInner} shrunk_inner={shrunkInner}"
  finally
    forceRemoveDirAll rootDir

/-- Registered `sqlite` differential fuzzing suite comparing `LeanSwe.Sqlite` against `Model` and SQLite `3.54.1`. -/
def suite : FuzzSuite :=
  { name := "sqlite"
    description := "Stateful multi-connection SQLite 3.54.1 vs LeanSwe.Sqlite.Model differential fuzzer"
    runSmoke := runSqliteSmoke
    runFuzz := runSqliteFuzz
    selfTestShrink := runSqliteSelfTestShrink }

end Fuzz.Sqlite
