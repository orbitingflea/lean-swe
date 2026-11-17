import Core.NondetTest
import LeanSwe.Sqlite.Types

namespace LeanSwe.Sqlite

open Core (NondetTest)
open Core.NondetTest

/-- Simulated failure injection mode for `mockRawOps`. -/
inductive MockFailMode where
  /-- All raw primitives succeed normally. -/
  | none
  /-- `openDb` fails with `kind`. -/
  | failOpen (kind : SqliteErrorKind)
  /-- `prepare` fails with `kind`. -/
  | failPrepare (kind : SqliteErrorKind)
  /-- `bind` fails with `kind`. -/
  | failBind (kind : SqliteErrorKind)
  /-- `step` fails immediately with `kind`. -/
  | failStep (kind : SqliteErrorKind)
  /-- `step` returns the first row and fails on the second step with `kind`. -/
  | failStepAfterFirstRow (kind : SqliteErrorKind)
  /-- `BEGIN` statement fails during `step` with `kind`. -/
  | failBegin (kind : SqliteErrorKind)
  /-- `COMMIT` statement fails during `step` with `kind`. -/
  | failCommit (kind : SqliteErrorKind)
  deriving Repr, BEq, DecidableEq

/-- In-flight prepared statement entry tracked inside `MockDb`. -/
structure MockStmt where
  /-- Statement handle identifier. -/
  id : UInt64
  /-- Owning database handle identifier. -/
  dbId : UInt64
  /-- Unmodified SQL string passed to `prepare`. -/
  sql : String
  /-- Bound typed parameters passed to `bind`. -/
  boundParams : Option (Array SqliteValue) := none
  /-- Number of rows already yielded by `step`. -/
  stepIndex : Nat := 0
  deriving Repr, BEq

/-- Deterministic transactional mock state backing `mockRawOps : RawSqliteOpsM (StateM MockDb)`. -/
structure MockDb where
  /-- Next database handle identifier to allocate. -/
  nextDbId : UInt64 := 1
  /-- Next statement handle identifier to allocate. -/
  nextStmtId : UInt64 := 1
  /-- Currently open database handle identifiers. -/
  openDbs : List UInt64 := []
  /-- Currently active prepared statements. -/
  openStmts : List MockStmt := []
  /-- Whether a transaction is currently active. -/
  inTransaction : Bool := false
  /-- Writes permanently committed in the mock database. -/
  committedWrites : List (String × Array SqliteValue) := []
  /-- Writes staged inside the active transaction, pending `COMMIT` or `ROLLBACK`. -/
  stagedWrites : List (String × Array SqliteValue) := []
  /-- Result rows yielded sequentially by `SELECT` statements. -/
  queryRows : Array SqliteRow := #[]
  /-- Chronological log of `(sql, params)` pairs passed to `bind`. -/
  boundCalls : List (String × Array SqliteValue) := []
  /-- Chronological log of `(path, cfg)` pairs passed to `openDb`. -/
  openCalls : List (String × OpenConfig) := []
  /-- Fault-injection mode for testing error paths and cleanup. -/
  failMode : MockFailMode := .none
  deriving Repr, BEq

private def strEq (a b : String) : Bool :=
  a.toList == b.toList

private def isBeginSql (sql : String) : Bool :=
  strEq sql "BEGIN" || strEq sql "BEGIN IMMEDIATE" || strEq sql "BEGIN TRANSACTION"

private def isCommitSql (sql : String) : Bool :=
  strEq sql "COMMIT" || strEq sql "COMMIT TRANSACTION"

private def isRollbackSql (sql : String) : Bool :=
  strEq sql "ROLLBACK" || strEq sql "ROLLBACK TRANSACTION"

private def isSelectSql (sql : String) : Bool :=
  sql.toList.take 6 == ['S', 'E', 'L', 'E', 'C', 'T']

private def mockMapRawError (raw : SqliteRawError) : SqliteError :=
  match raw with
  | .cantOpen p? c _ => { kind := .notFound, sqliteCode := some c, path := p?, message := "cantOpen" }
  | .busy c _ => { kind := .busy, sqliteCode := some c, message := "busy" }
  | .constraint c _ => { kind := .constraint, sqliteCode := some c, message := "constraint" }
  | .misuse c _ => { kind := .misuse, sqliteCode := some c, message := "misuse" }
  | .invalidArgument _ => { kind := .invalidInput, message := "invalidArgument" }
  | .ioFailure c _ => { kind := .ioError, sqliteCode := some c, message := "ioFailure" }
  | .sqliteCodeError c _ => { kind := .ioError, sqliteCode := some c, message := "sqliteCodeError" }
  | .userError _ => { kind := .ioError, message := "userError" }

private def mockOpenDb (path : String) (cfg : OpenConfig) : MockDb → Except SqliteError DbHandle × MockDb
  | ⟨nextDbId, nextStmtId, openDbs, openStmts, inTx, comm, staged, qRows, bCalls, oCalls, fMode⟩ =>
    let oCalls' := oCalls ++ [(path, cfg)]
    let s1 : MockDb := ⟨nextDbId, nextStmtId, openDbs, openStmts, inTx, comm, staged, qRows, bCalls, oCalls', fMode⟩
    match fMode with
    | .failOpen k => (.error { kind := k, path := some path, message := "mock open failure" }, s1)
    | _ =>
      if path.toList == [] then
        (.error { kind := .invalidInput, path := some path, message := "empty path" }, s1)
      else
        (.ok { id := nextDbId },
          ⟨nextDbId + 1, nextStmtId, openDbs ++ [nextDbId], openStmts, inTx, comm, staged, qRows, bCalls, oCalls', fMode⟩)

private def mockCloseDb (db : DbHandle) : MockDb → Except SqliteError Unit × MockDb
  | s@⟨nextDbId, nextStmtId, openDbs, openStmts, inTx, comm, staged, qRows, bCalls, oCalled, fMode⟩ =>
    if !(openDbs.contains db.id) then
      (.error { kind := .misuse, message := "unknown db handle" }, s)
    else
      (.ok (), ⟨nextDbId, nextStmtId, openDbs.filter (· != db.id), openStmts, inTx, comm, staged, qRows, bCalls, oCalled, fMode⟩)

private def mockPrepare (db : DbHandle) (sql : String) : MockDb → Except SqliteError StmtHandle × MockDb
  | s@⟨nextDbId, nextStmtId, openDbs, openStmts, inTx, comm, staged, qRows, bCalls, oCalled, fMode⟩ =>
    if !(openDbs.contains db.id) then
      (.error { kind := .misuse, message := "closed db handle" }, s)
    else
      match fMode with
      | .failPrepare k => (.error { kind := k, message := "mock prepare failure" }, s)
      | _ =>
        let entry : MockStmt := { id := nextStmtId, dbId := db.id, sql := sql }
        (.ok { id := nextStmtId, dbId := db.id },
          ⟨nextDbId, nextStmtId + 1, openDbs, openStmts ++ [entry], inTx, comm, staged, qRows, bCalls, oCalled, fMode⟩)

private def mockBind (stmt : StmtHandle) (params : Array SqliteValue) : MockDb → Except SqliteError Unit × MockDb
  | s@⟨nextDbId, nextStmtId, openDbs, openStmts, inTx, comm, staged, qRows, bCalls, oCalled, fMode⟩ =>
    match openStmts.find? (fun st => st.id == stmt.id && st.dbId == stmt.dbId) with
    | none => (.error { kind := .misuse, message := "unknown stmt handle" }, s)
    | some st =>
      match fMode with
      | .failBind k => (.error { kind := k, message := "mock bind failure" }, s)
      | _ =>
        let updated := openStmts.map fun cur =>
          if cur.id == stmt.id then { cur with boundParams := some params } else cur
        (.ok (), ⟨nextDbId, nextStmtId, openDbs, updated, inTx, comm, staged, qRows, bCalls ++ [(st.sql, params)], oCalled, fMode⟩)

private def mockStep (stmt : StmtHandle) : MockDb → Except SqliteError StepResult × MockDb
  | s@⟨nextDbId, nextStmtId, openDbs, openStmts, inTx, comm, staged, qRows, bCalls, oCalled, fMode⟩ =>
    match openStmts.find? (fun st => st.id == stmt.id && st.dbId == stmt.dbId) with
    | none => (.error { kind := .misuse, message := "unknown stmt handle" }, s)
    | some st =>
      if isBeginSql st.sql then
        match fMode with
        | .failBegin k => (.error { kind := k, message := "mock begin failure" }, s)
        | _ =>
          if inTx then
            (.error { kind := .misuse, message := "transaction already active" }, s)
          else
            (.ok .done, ⟨nextDbId, nextStmtId, openDbs, openStmts, true, comm, [], qRows, bCalls, oCalled, fMode⟩)
      else if isCommitSql st.sql then
        match fMode with
        | .failCommit k => (.error { kind := k, message := "mock commit failure" }, s)
        | _ =>
          if !inTx then
            (.error { kind := .misuse, message := "no active transaction" }, s)
          else
            (.ok .done, ⟨nextDbId, nextStmtId, openDbs, openStmts, false, comm ++ staged, [], qRows, bCalls, oCalled, fMode⟩)
      else if isRollbackSql st.sql then
        if !inTx then
          (.error { kind := .misuse, message := "no active transaction" }, s)
        else
          (.ok .done, ⟨nextDbId, nextStmtId, openDbs, openStmts, false, comm, [], qRows, bCalls, oCalled, fMode⟩)
      else
        match fMode with
        | .failStep k => (.error { kind := k, message := "mock step failure" }, s)
        | _ =>
          let params := st.boundParams.getD #[]
          if isSelectSql st.sql then
            if hIdx : st.stepIndex < qRows.size then
              match fMode with
              | .failStepAfterFirstRow k =>
                if st.stepIndex > 0 then
                  (.error { kind := k, message := "mock mid-stream step failure" }, s)
                else
                  let row := qRows[st.stepIndex]
                  let updated := openStmts.map fun cur =>
                    if cur.id == stmt.id then { cur with stepIndex := cur.stepIndex + 1 } else cur
                  (.ok (.row row), ⟨nextDbId, nextStmtId, openDbs, updated, inTx, comm, staged, qRows, bCalls, oCalled, fMode⟩)
              | _ =>
                let row := qRows[st.stepIndex]
                let updated := openStmts.map fun cur =>
                  if cur.id == stmt.id then { cur with stepIndex := cur.stepIndex + 1 } else cur
                (.ok (.row row), ⟨nextDbId, nextStmtId, openDbs, updated, inTx, comm, staged, qRows, bCalls, oCalled, fMode⟩)
            else
              (.ok .done, s)
          else if st.stepIndex == 0 then
            if inTx then
              (.ok .done, ⟨nextDbId, nextStmtId, openDbs, openStmts, inTx, comm, staged ++ [(st.sql, params)], qRows, bCalls, oCalled, fMode⟩)
            else
              (.ok .done, ⟨nextDbId, nextStmtId, openDbs, openStmts, inTx, comm ++ [(st.sql, params)], staged, qRows, bCalls, oCalled, fMode⟩)
          else
            (.ok .done, s)

private def mockFinalize (stmt : StmtHandle) : MockDb → Except SqliteError Unit × MockDb
  | s@⟨nextDbId, nextStmtId, openDbs, openStmts, inTx, comm, staged, qRows, bCalls, oCalled, fMode⟩ =>
    if !(openStmts.any (fun st => st.id == stmt.id && st.dbId == stmt.dbId)) then
      (.error { kind := .misuse, message := "unknown stmt handle" }, s)
    else
      (.ok (), ⟨nextDbId, nextStmtId, openDbs, openStmts.filter (fun st => st.id != stmt.id), inTx, comm, staged, qRows, bCalls, oCalled, fMode⟩)

/-- Pure `StateM MockDb` implementation of `RawSqliteOpsM` for specification checks. -/
def mockRawOps : RawSqliteOpsM (StateM MockDb) :=
  { mapRawError := mockMapRawError
    openDb := mockOpenDb
    closeDb := mockCloseDb
    prepare := mockPrepare
    bind := mockBind
    step := mockStep
    finalize := mockFinalize
    activeDbCount := fun s => (s.openDbs.length, s)
    activeStmtCount := fun s => (s.openStmts.length, s) }

/-- Every error returned by `api.mapRawError` carries a non-empty diagnostic message. -/
def test_sqlite_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (api : SqliteApi) : runner Unit := do
  let raw ← nondet SqliteRawError
  let err := api.mapRawError raw
  NondetTest.assert (err.message ≠ "")

/-- Known `SqliteRawError` inputs map to expected `SqliteErrorKind` categories with non-empty messages. -/
def test_sqlite_mapRawError_mapsExpectedKinds
    {runner} [NondetTest runner] (api : SqliteApi) : runner Unit := do
  let path? ← nondet (Option String)
  let code ← nondet UInt32
  let detail ← nondet String
  let eNotFound := api.mapRawError (.cantOpen path? code detail)
  let eBusy := api.mapRawError (.busy code detail)
  let eConstraint := api.mapRawError (.constraint code detail)
  let eMisuse := api.mapRawError (.misuse code detail)
  let eInvalid := api.mapRawError (.invalidArgument detail)
  let eIo := api.mapRawError (.ioFailure code detail)
  NondetTest.assert (eNotFound.kind = .notFound ∧ eNotFound.message ≠ "")
  NondetTest.assert (eBusy.kind = .busy ∧ eBusy.message ≠ "")
  NondetTest.assert (eConstraint.kind = .constraint ∧ eConstraint.message ≠ "")
  NondetTest.assert (eMisuse.kind = .misuse ∧ eMisuse.message ≠ "")
  NondetTest.assert (eInvalid.kind = .invalidInput ∧ eInvalid.message ≠ "")
  NondetTest.assert (eIo.kind = .ioError ∧ eIo.message ≠ "")

/-- `validateConfig` rejects combining `readOnly = true` with `createIfMissing = true`. -/
def test_sqlite_validateConfig_rejectsReadOnlyWithCreate
    {runner} [NondetTest runner] (api : SqliteApi) : runner Unit := do
  let cfg ← nondet OpenConfig
  assume (cfg.readOnly = true ∧ cfg.createIfMissing = true)
  match api.validateConfig cfg with
  | .ok () => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidInput ∧ e.message ≠ "")

/-- `validateConfig` rejects `busyTimeoutMs` exceeding `maxBusyTimeoutMs`. -/
def test_sqlite_validateConfig_rejectsExcessiveBusyTimeout
    {runner} [NondetTest runner] (api : SqliteApi) : runner Unit := do
  let cfg ← nondet OpenConfig
  assume (cfg.busyTimeoutMs > maxBusyTimeoutMs)
  match api.validateConfig cfg with
  | .ok () => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidInput ∧ e.message ≠ "")

/-- `validateConfig` accepts valid `OpenConfig` values. -/
def test_sqlite_validateConfig_acceptsValidConfig
    {runner} [NondetTest runner] (api : SqliteApi) : runner Unit := do
  let cfg ← nondet OpenConfig
  assume (!(cfg.readOnly && cfg.createIfMissing))
  assume (cfg.busyTimeoutMs ≤ maxBusyTimeoutMs)
  NondetTest.assert (api.validateConfig cfg = .ok ())

/-- `withDb` validates `OpenConfig`, propagates `.busy`, and preserves `activeDbCount` on `.ok` and `.error`. -/
def test_sqlite_withDb_preservesActiveDbCount_andPropagatesBusy
    {runner} [NondetTest runner]
    (mkApi : RawSqliteOpsM (StateM MockDb) → SqliteApiM (StateM MockDb)) : runner Unit := do
  let path ← nondet String
  let cfg ← nondet OpenConfig
  let failOnBody ← nondet Bool
  let bodyErr ← nondet SqliteError
  assume (path ≠ "")
  let api := mkApi mockRawOps
  let validCfg : OpenConfig := { cfg with readOnly := false, busyTimeoutMs := cfg.busyTimeoutMs % (maxBusyTimeoutMs + 1) }
  let sOk : MockDb := {}
  let outOk := (api.withDb path validCfg (fun _ =>
    if failOnBody then pure (.error bodyErr) else pure (.ok "done"))).run sOk
  NondetTest.assert (outOk.2.openDbs.length = 0 ∧ (api.activeDbCount.run outOk.2).1 = 0 ∧
    outOk.2.openCalls = [(path, validCfg)])
  if failOnBody then
    NondetTest.assert (outOk.1 = .error bodyErr)
  else
    NondetTest.assert (outOk.1 = .ok "done")
  let sBusy : MockDb := { failMode := .failOpen .busy }
  let outBusy := (api.withDb path validCfg (fun _ => pure (.ok ()))).run sBusy
  NondetTest.assert ((∃ e, outBusy.1 = .error e ∧ e.kind = .busy) ∧
    outBusy.2.openDbs.length = 0 ∧ (api.activeDbCount.run outBusy.2).1 = 0 ∧
    outBusy.2.openCalls = [(path, validCfg)])
  let badCfg : OpenConfig := { readOnly := true, createIfMissing := true }
  let outBad := (api.withDb path badCfg (fun _ => pure (.ok ()))).run sOk
  NondetTest.assert ((∃ e, outBad.1 = .error e ∧ e.kind = .invalidInput) ∧
    outBad.2.openCalls = [] ∧ outBad.2.openDbs.length = 0)

/-- `exec` propagates `.busy`/`.constraint` errors and preserves `activeStmtCount` on all success and failure paths. -/
def test_sqlite_exec_preservesActiveStmtCount_andPropagatesErrors
    {runner} [NondetTest runner]
    (mkApi : RawSqliteOpsM (StateM MockDb) → SqliteApiM (StateM MockDb)) : runner Unit := do
  let sql ← nondet String
  let params ← nondet (Array SqliteValue)
  let mode ← nondet MockFailMode
  assume (mode = .none ∨ mode = .failPrepare .invalidInput ∨ mode = .failBind .invalidInput ∨
    mode = .failStep .busy ∨ mode = .failStep .constraint)
  assume (!(isBeginSql sql || isCommitSql sql || isRollbackSql sql))
  let api := mkApi mockRawOps
  let s₀ : MockDb := { openDbs := [1], nextDbId := 2, failMode := mode }
  let out := (api.exec { id := 1 } sql params).run s₀
  NondetTest.assert (out.2.openStmts.length = 0 ∧ (api.activeStmtCount.run out.2).1 = 0)
  match mode with
  | .none => NondetTest.assert (out.1 = .ok ())
  | .failPrepare k => NondetTest.assert (∃ e, out.1 = .error e ∧ e.kind = k)
  | .failBind k => NondetTest.assert (∃ e, out.1 = .error e ∧ e.kind = k)
  | .failStep k => NondetTest.assert (∃ e, out.1 = .error e ∧ e.kind = k)
  | _ => pure ()

/-- `query` collects all rows in order and preserves `activeStmtCount` even on mid-stream `.busy` failures. -/
def test_sqlite_query_collectsRows_andPreservesActiveStmtCount
    {runner} [NondetTest runner]
    (mkApi : RawSqliteOpsM (StateM MockDb) → SqliteApiM (StateM MockDb)) : runner Unit := do
  let r0 ← nondet SqliteRow
  let r1 ← nondet SqliteRow
  let params ← nondet (Array SqliteValue)
  let api := mkApi mockRawOps
  let rows := #[r0, r1]
  let sOk : MockDb := { openDbs := [1], nextDbId := 2, queryRows := rows, failMode := .none }
  let outOk := (api.query { id := 1 } "SELECT id, name FROM items WHERE id = ?" params).run sOk
  NondetTest.assert (outOk.1 = .ok rows ∧ outOk.2.openStmts.length = 0 ∧ (api.activeStmtCount.run outOk.2).1 = 0)
  let sMidErr : MockDb := { openDbs := [1], nextDbId := 2, queryRows := rows, failMode := .failStepAfterFirstRow .busy }
  let outErr := (api.query { id := 1 } "SELECT id, name FROM items WHERE id = ?" params).run sMidErr
  NondetTest.assert ((∃ e, outErr.1 = .error e ∧ e.kind = .busy) ∧
    outErr.2.openStmts.length = 0 ∧ (api.activeStmtCount.run outErr.2).1 = 0)

/-- `queryOne` returns `none` on empty result, `some row` on non-empty result, and preserves `activeStmtCount`. -/
def test_sqlite_queryOne_returnsOptionalRow_andPreservesActiveStmtCount
    {runner} [NondetTest runner]
    (mkApi : RawSqliteOpsM (StateM MockDb) → SqliteApiM (StateM MockDb)) : runner Unit := do
  let row ← nondet SqliteRow
  let params ← nondet (Array SqliteValue)
  let api := mkApi mockRawOps
  let sEmpty : MockDb := { openDbs := [1], nextDbId := 2, queryRows := #[], failMode := .none }
  let outEmpty := (api.queryOne { id := 1 } "SELECT id FROM items WHERE id = ?" params).run sEmpty
  NondetTest.assert (outEmpty.1 = .ok none ∧ outEmpty.2.openStmts.length = 0 ∧ (api.activeStmtCount.run outEmpty.2).1 = 0)
  let sOne : MockDb := { openDbs := [1], nextDbId := 2, queryRows := #[row], failMode := .none }
  let outOne := (api.queryOne { id := 1 } "SELECT id FROM items WHERE id = ?" params).run sOne
  NondetTest.assert (outOne.1 = .ok (some row) ∧ outOne.2.openStmts.length = 0 ∧ (api.activeStmtCount.run outOne.2).1 = 0)
  let sBusy : MockDb := { openDbs := [1], nextDbId := 2, queryRows := #[row], failMode := .failStep .busy }
  let outBusy := (api.queryOne { id := 1 } "SELECT id FROM items WHERE id = ?" params).run sBusy
  NondetTest.assert ((∃ e, outBusy.1 = .error e ∧ e.kind = .busy) ∧
    outBusy.2.openStmts.length = 0 ∧ (api.activeStmtCount.run outBusy.2).1 = 0)

private def txCommitBody (api : SqliteApiM (StateM MockDb)) (val : SqliteValue)
    (db : DbHandle) : StateM MockDb (Except SqliteError String) := fun s =>
  match (api.exec db "INSERT INTO items(v) VALUES (?)" #[val]).run s with
  | (.error e, s1) => (.error e, s1)
  | (.ok (), s1) => (.ok "committed", s1)

private def txRollbackBody (api : SqliteApiM (StateM MockDb)) (val : SqliteValue)
    (err : SqliteError) (db : DbHandle) : StateM MockDb (Except SqliteError Unit) := fun s =>
  match (api.exec db "INSERT INTO items(v) VALUES (?)" #[val]).run s with
  | (.error e, s1) => (.error e, s1)
  | (.ok (), s1) => (.error err, s1)

private def txExecInsert (api : SqliteApiM (StateM MockDb)) (val : SqliteValue)
    (db : DbHandle) : StateM MockDb (Except SqliteError Unit) :=
  api.exec db "INSERT INTO items(v) VALUES (?)" #[val]

private def dbTxExec (api : SqliteApiM (StateM MockDb)) (val : SqliteValue)
    (db : DbHandle) : StateM MockDb (Except SqliteError Unit) :=
  api.withTransaction db (fun h => api.exec h "INSERT INTO logs(msg) VALUES (?)" #[val])

/-- `withTransaction` commits staged writes when `action` returns `.ok` and leaves `activeStmtCount` clean. -/
def test_sqlite_withTransaction_commitsOnOk
    {runner} [NondetTest runner]
    (mkApi : RawSqliteOpsM (StateM MockDb) → SqliteApiM (StateM MockDb)) : runner Unit := do
  let val ← nondet SqliteValue
  let api := mkApi mockRawOps
  let s₀ : MockDb := { openDbs := [1], nextDbId := 2, failMode := .none }
  let out := (api.withTransaction { id := 1 } (txCommitBody api val)).run s₀
  NondetTest.assert (out.1 = .ok "committed")
  NondetTest.assert (out.2.inTransaction = false ∧ out.2.stagedWrites = [])
  NondetTest.assert (out.2.committedWrites = [("INSERT INTO items(v) VALUES (?)", #[val])])
  NondetTest.assert (out.2.openStmts.length = 0 ∧ (api.activeStmtCount.run out.2).1 = 0)

/-- `withTransaction` rolls back all staged writes when `action` returns `.error`, preserving the error. -/
def test_sqlite_withTransaction_rollsBackOnError
    {runner} [NondetTest runner]
    (mkApi : RawSqliteOpsM (StateM MockDb) → SqliteApiM (StateM MockDb)) : runner Unit := do
  let val ← nondet SqliteValue
  let err ← nondet SqliteError
  let api := mkApi mockRawOps
  let prior : List (String × Array SqliteValue) := [("INSERT INTO items(v) VALUES (?)", #[.int 1])]
  let s₀ : MockDb := { openDbs := [1], nextDbId := 2, committedWrites := prior, failMode := .none }
  let out := (api.withTransaction { id := 1 } (txRollbackBody api val err)).run s₀
  NondetTest.assert (out.1 = .error err)
  NondetTest.assert (out.2.inTransaction = false ∧ out.2.stagedWrites = [])
  NondetTest.assert (out.2.committedWrites = prior)
  NondetTest.assert (out.2.openStmts.length = 0 ∧ (api.activeStmtCount.run out.2).1 = 0)

/-- `withTransaction` propagates `.busy` on `BEGIN` or `COMMIT` failure and leaves committed state unchanged. -/
def test_sqlite_withTransaction_rollsBackOnCommitAndBeginBusy
    {runner} [NondetTest runner]
    (mkApi : RawSqliteOpsM (StateM MockDb) → SqliteApiM (StateM MockDb)) : runner Unit := do
  let val ← nondet SqliteValue
  let api := mkApi mockRawOps
  let sBeginBusy : MockDb := { openDbs := [1], nextDbId := 2, failMode := .failBegin .busy }
  let outBegin := (api.withTransaction { id := 1 } (txExecInsert api val)).run sBeginBusy
  NondetTest.assert (∃ e, outBegin.1 = .error e ∧ e.kind = .busy)
  NondetTest.assert (outBegin.2.boundCalls = [] ∧ outBegin.2.committedWrites = [] ∧ outBegin.2.inTransaction = false)
  NondetTest.assert (outBegin.2.openStmts.length = 0 ∧ (api.activeStmtCount.run outBegin.2).1 = 0)
  let sCommitBusy : MockDb := { openDbs := [1], nextDbId := 2, failMode := .failCommit .busy }
  let outCommit := (api.withTransaction { id := 1 } (txExecInsert api val)).run sCommitBusy
  NondetTest.assert (∃ e, outCommit.1 = .error e ∧ e.kind = .busy)
  NondetTest.assert (outCommit.2.committedWrites = [] ∧ outCommit.2.stagedWrites = [] ∧ outCommit.2.inTransaction = false)
  NondetTest.assert (outCommit.2.openStmts.length = 0 ∧ (api.activeStmtCount.run outCommit.2).1 = 0)

/-- `exec`, `query`, and `queryOne` bind typed `SqliteValue` arrays directly via `bind` without SQL string interpolation. -/
def test_sqlite_binding_noSqlStringInterpolation
    {runner} [NondetTest runner]
    (mkApi : RawSqliteOpsM (StateM MockDb) → SqliteApiM (StateM MockDb)) : runner Unit := do
  let payload ← nondet String
  let n ← nondet Int64
  let api := mkApi mockRawOps
  let insertSql := "INSERT INTO users(name, age) VALUES (?, ?)"
  let selectSql := "SELECT name, age FROM users WHERE name = ? AND age = ?"
  let selectOneSql := "SELECT name, age FROM users WHERE name = ? AND age = ? LIMIT 1"
  let params : Array SqliteValue := #[.text payload, .int n]
  let s₀ : MockDb := { openDbs := [1], nextDbId := 2, failMode := .none }
  let outExec := (api.exec { id := 1 } insertSql params).run s₀
  let outQuery := (api.query { id := 1 } selectSql params).run outExec.2
  let outQueryOne := (api.queryOne { id := 1 } selectOneSql params).run outQuery.2
  NondetTest.assert (outExec.1 = .ok () ∧ outQuery.1 = .ok #[] ∧ outQueryOne.1 = .ok none)
  NondetTest.assert (outQueryOne.2.boundCalls = [(insertSql, params), (selectSql, params), (selectOneSql, params)])

/-- `withDb` wrapping `withTransaction` and `exec` preserves both `activeDbCount` and `activeStmtCount`. -/
def test_sqlite_withDb_withTransaction_preservesAllHandles
    {runner} [NondetTest runner]
    (mkApi : RawSqliteOpsM (StateM MockDb) → SqliteApiM (StateM MockDb)) : runner Unit := do
  let val ← nondet SqliteValue
  let api := mkApi mockRawOps
  let cfg : OpenConfig := {}
  let s₀ : MockDb := {}
  let out := (api.withDb ":memory:" cfg (dbTxExec api val)).run s₀
  NondetTest.assert (out.1 = .ok ())
  NondetTest.assert (out.2.openDbs.length = 0 ∧ out.2.openStmts.length = 0)
  NondetTest.assert ((api.activeDbCount.run out.2).1 = 0 ∧ (api.activeStmtCount.run out.2).1 = 0)

end LeanSwe.Sqlite
