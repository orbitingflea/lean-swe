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
  assert (err.message ≠ "")

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
  assert (eNotFound.kind = .notFound ∧ eNotFound.message ≠ "")
  assert (eBusy.kind = .busy ∧ eBusy.message ≠ "")
  assert (eConstraint.kind = .constraint ∧ eConstraint.message ≠ "")
  assert (eMisuse.kind = .misuse ∧ eMisuse.message ≠ "")
  assert (eInvalid.kind = .invalidInput ∧ eInvalid.message ≠ "")
  assert (eIo.kind = .ioError ∧ eIo.message ≠ "")

/-- `validateConfig` rejects combining `readOnly = true` with `createIfMissing = true`. -/
def test_sqlite_validateConfig_rejectsReadOnlyWithCreate
    {runner} [NondetTest runner] (api : SqliteApi) : runner Unit := do
  let cfg ← nondet OpenConfig
  assume (cfg.readOnly = true ∧ cfg.createIfMissing = true)
  match api.validateConfig cfg with
  | .ok () => assert False
  | .error e => assert (e.kind = .invalidInput ∧ e.message ≠ "")

/-- `validateConfig` rejects `busyTimeoutMs` exceeding `maxBusyTimeoutMs`. -/
def test_sqlite_validateConfig_rejectsExcessiveBusyTimeout
    {runner} [NondetTest runner] (api : SqliteApi) : runner Unit := do
  let cfg ← nondet OpenConfig
  assume (cfg.busyTimeoutMs > maxBusyTimeoutMs)
  match api.validateConfig cfg with
  | .ok () => assert False
  | .error e => assert (e.kind = .invalidInput ∧ e.message ≠ "")

/-- `validateConfig` accepts valid `OpenConfig` values. -/
def test_sqlite_validateConfig_acceptsValidConfig
    {runner} [NondetTest runner] (api : SqliteApi) : runner Unit := do
  let cfg ← nondet OpenConfig
  assume (!(cfg.readOnly && cfg.createIfMissing))
  assume (cfg.busyTimeoutMs ≤ maxBusyTimeoutMs)
  assert (api.validateConfig cfg = .ok ())

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
  assert (outOk.2.openDbs.length = 0 ∧ (api.activeDbCount.run outOk.2).1 = 0 ∧
    outOk.2.openCalls = [(path, validCfg)])
  if failOnBody then
    assert (outOk.1 = .error bodyErr)
  else
    assert (outOk.1 = .ok "done")
  let sBusy : MockDb := { failMode := .failOpen .busy }
  let outBusy := (api.withDb path validCfg (fun _ => pure (.ok ()))).run sBusy
  assert ((∃ e, outBusy.1 = .error e ∧ e.kind = .busy) ∧
    outBusy.2.openDbs.length = 0 ∧ (api.activeDbCount.run outBusy.2).1 = 0 ∧
    outBusy.2.openCalls = [(path, validCfg)])
  let badCfg : OpenConfig := { readOnly := true, createIfMissing := true }
  let outBad := (api.withDb path badCfg (fun _ => pure (.ok ()))).run sOk
  assert ((∃ e, outBad.1 = .error e ∧ e.kind = .invalidInput) ∧
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
  assert (out.2.openStmts.length = 0 ∧ (api.activeStmtCount.run out.2).1 = 0)
  match mode with
  | .none => assert (out.1 = .ok ())
  | .failPrepare k => assert (∃ e, out.1 = .error e ∧ e.kind = k)
  | .failBind k => assert (∃ e, out.1 = .error e ∧ e.kind = k)
  | .failStep k => assert (∃ e, out.1 = .error e ∧ e.kind = k)
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
  assert (outOk.1 = .ok rows ∧ outOk.2.openStmts.length = 0 ∧ (api.activeStmtCount.run outOk.2).1 = 0)
  let sMidErr : MockDb := { openDbs := [1], nextDbId := 2, queryRows := rows, failMode := .failStepAfterFirstRow .busy }
  let outErr := (api.query { id := 1 } "SELECT id, name FROM items WHERE id = ?" params).run sMidErr
  assert ((∃ e, outErr.1 = .error e ∧ e.kind = .busy) ∧
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
  assert (outEmpty.1 = .ok none ∧ outEmpty.2.openStmts.length = 0 ∧ (api.activeStmtCount.run outEmpty.2).1 = 0)
  let sOne : MockDb := { openDbs := [1], nextDbId := 2, queryRows := #[row], failMode := .none }
  let outOne := (api.queryOne { id := 1 } "SELECT id FROM items WHERE id = ?" params).run sOne
  assert (outOne.1 = .ok (some row) ∧ outOne.2.openStmts.length = 0 ∧ (api.activeStmtCount.run outOne.2).1 = 0)
  let sBusy : MockDb := { openDbs := [1], nextDbId := 2, queryRows := #[row], failMode := .failStep .busy }
  let outBusy := (api.queryOne { id := 1 } "SELECT id FROM items WHERE id = ?" params).run sBusy
  assert ((∃ e, outBusy.1 = .error e ∧ e.kind = .busy) ∧
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
  assert (out.1 = .ok "committed")
  assert (out.2.inTransaction = false ∧ out.2.stagedWrites = [])
  assert (out.2.committedWrites = [("INSERT INTO items(v) VALUES (?)", #[val])])
  assert (out.2.openStmts.length = 0 ∧ (api.activeStmtCount.run out.2).1 = 0)

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
  assert (out.1 = .error err)
  assert (out.2.inTransaction = false ∧ out.2.stagedWrites = [])
  assert (out.2.committedWrites = prior)
  assert (out.2.openStmts.length = 0 ∧ (api.activeStmtCount.run out.2).1 = 0)

/-- `withTransaction` propagates `.busy` on `BEGIN` or `COMMIT` failure and leaves committed state unchanged. -/
def test_sqlite_withTransaction_rollsBackOnCommitAndBeginBusy
    {runner} [NondetTest runner]
    (mkApi : RawSqliteOpsM (StateM MockDb) → SqliteApiM (StateM MockDb)) : runner Unit := do
  let val ← nondet SqliteValue
  let api := mkApi mockRawOps
  let sBeginBusy : MockDb := { openDbs := [1], nextDbId := 2, failMode := .failBegin .busy }
  let outBegin := (api.withTransaction { id := 1 } (txExecInsert api val)).run sBeginBusy
  assert (∃ e, outBegin.1 = .error e ∧ e.kind = .busy)
  assert (outBegin.2.boundCalls = [] ∧ outBegin.2.committedWrites = [] ∧ outBegin.2.inTransaction = false)
  assert (outBegin.2.openStmts.length = 0 ∧ (api.activeStmtCount.run outBegin.2).1 = 0)
  let sCommitBusy : MockDb := { openDbs := [1], nextDbId := 2, failMode := .failCommit .busy }
  let outCommit := (api.withTransaction { id := 1 } (txExecInsert api val)).run sCommitBusy
  assert (∃ e, outCommit.1 = .error e ∧ e.kind = .busy)
  assert (outCommit.2.committedWrites = [] ∧ outCommit.2.stagedWrites = [] ∧ outCommit.2.inTransaction = false)
  assert (outCommit.2.openStmts.length = 0 ∧ (api.activeStmtCount.run outCommit.2).1 = 0)

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
  assert (outExec.1 = .ok () ∧ outQuery.1 = .ok #[] ∧ outQueryOne.1 = .ok none)
  assert (outQueryOne.2.boundCalls = [(insertSql, params), (selectSql, params), (selectOneSql, params)])

/-- `withDb` wrapping `withTransaction` and `exec` preserves both `activeDbCount` and `activeStmtCount`. -/
def test_sqlite_withDb_withTransaction_preservesAllHandles
    {runner} [NondetTest runner]
    (mkApi : RawSqliteOpsM (StateM MockDb) → SqliteApiM (StateM MockDb)) : runner Unit := do
  let val ← nondet SqliteValue
  let api := mkApi mockRawOps
  let cfg : OpenConfig := {}
  let s₀ : MockDb := {}
  let out := (api.withDb ":memory:" cfg (dbTxExec api val)).run s₀
  assert (out.1 = .ok ())
  assert (out.2.openDbs.length = 0 ∧ out.2.openStmts.length = 0)
  assert ((api.activeDbCount.run out.2).1 = 0 ∧ (api.activeStmtCount.run out.2).1 = 0)

private def stubGoodApi : SqliteApi :=
  { mapRawError := mockMapRawError
    validateConfig := fun cfg =>
      if cfg.readOnly && cfg.createIfMissing then
        .error { kind := .invalidInput, message := "readOnly cannot be combined with createIfMissing" }
      else if cfg.busyTimeoutMs > maxBusyTimeoutMs then
        .error { kind := .invalidInput, message := "busyTimeoutMs exceeds int32 max" }
      else
        .ok ()
    withDb := fun _ _ _ => pure (.error { kind := .ioError, message := "stub" })
    withTransaction := fun _ _ => pure (.error { kind := .ioError, message := "stub" })
    exec := fun _ _ _ => pure (.ok ())
    query := fun _ _ _ => pure (.ok #[])
    queryOne := fun _ _ _ => pure (.ok none)
    activeDbCount := pure 0
    activeStmtCount := pure 0 }

private def goodExecLoop (ops : RawSqliteOpsM (StateM MockDb)) (stmt : StmtHandle) :
    Nat → StateM MockDb (Except SqliteError Unit)
  | 0 => pure (.error { kind := .ioError, message := "step fuel exhausted" })
  | fuel + 1 => fun s =>
    match ops.step stmt s with
    | (.error e, s1) => (.error e, s1)
    | (.ok .done, s1) => (.ok (), s1)
    | (.ok (.row _), s1) => goodExecLoop ops stmt fuel s1

private def goodExec (ops : RawSqliteOpsM (StateM MockDb))
    (db : DbHandle) (sql : String) (params : Array SqliteValue) :
    StateM MockDb (Except SqliteError Unit) := fun s =>
  match ops.prepare db sql s with
  | (.error e, s1) => (Except.error e, s1)
  | (.ok stmt, s1) =>
    let (res, s2) : Except SqliteError Unit × MockDb :=
      match ops.bind stmt params s1 with
      | (.error e, s1b) => (Except.error e, s1b)
      | (.ok (), s1b) => goodExecLoop ops stmt 4 s1b
    let (finRes, s3) := ops.finalize stmt s2
    match res with
    | Except.error e => (Except.error e, s3)
    | Except.ok () =>
      match finRes with
      | Except.error e => (Except.error e, s3)
      | Except.ok () => (Except.ok (), s3)

private def goodQueryLoop (ops : RawSqliteOpsM (StateM MockDb)) (stmt : StmtHandle)
    (acc : Array SqliteRow) : Nat → StateM MockDb (Except SqliteError (Array SqliteRow))
  | 0 => pure (.error { kind := .ioError, message := "step fuel exhausted" })
  | fuel + 1 => fun s =>
    match ops.step stmt s with
    | (.error e, s1) => (.error e, s1)
    | (.ok .done, s1) => (.ok acc, s1)
    | (.ok (.row r), s1) => goodQueryLoop ops stmt (acc.push r) fuel s1

private def goodQuery (ops : RawSqliteOpsM (StateM MockDb))
    (db : DbHandle) (sql : String) (params : Array SqliteValue) :
    StateM MockDb (Except SqliteError (Array SqliteRow)) := fun s =>
  match ops.prepare db sql s with
  | (.error e, s1) => (Except.error e, s1)
  | (.ok stmt, s1) =>
    let (res, s2) : Except SqliteError (Array SqliteRow) × MockDb :=
      match ops.bind stmt params s1 with
      | (.error e, s1b) => (Except.error e, s1b)
      | (.ok (), s1b) => goodQueryLoop ops stmt #[] 4 s1b
    let (finRes, s3) := ops.finalize stmt s2
    match res with
    | Except.error e => (Except.error e, s3)
    | Except.ok rows =>
      match finRes with
      | Except.error e => (Except.error e, s3)
      | Except.ok () => (Except.ok rows, s3)

private def goodQueryOne (ops : RawSqliteOpsM (StateM MockDb))
    (db : DbHandle) (sql : String) (params : Array SqliteValue) :
    StateM MockDb (Except SqliteError (Option SqliteRow)) := fun s =>
  match ops.prepare db sql s with
  | (.error e, s1) => (Except.error e, s1)
  | (.ok stmt, s1) =>
    let (res, s2) : Except SqliteError (Option SqliteRow) × MockDb :=
      match ops.bind stmt params s1 with
      | (.error e, s1b) => (Except.error e, s1b)
      | (.ok (), s1b) =>
        match ops.step stmt s1b with
        | (.error e, s1c) => (Except.error e, s1c)
        | (.ok .done, s1c) => (Except.ok none, s1c)
        | (.ok (.row r), s1c) => (Except.ok (some r), s1c)
    let (finRes, s3) := ops.finalize stmt s2
    match res with
    | Except.error e => (Except.error e, s3)
    | Except.ok row? =>
      match finRes with
      | Except.error e => (Except.error e, s3)
      | Except.ok () => (Except.ok row?, s3)

private def goodMkApi (ops : RawSqliteOpsM (StateM MockDb)) : SqliteApiM (StateM MockDb) :=
  { mapRawError := ops.mapRawError
    validateConfig := stubGoodApi.validateConfig
    withDb := fun path cfg action s =>
      match stubGoodApi.validateConfig cfg with
      | .error e => (.error e, s)
      | .ok () =>
        match ops.openDb path cfg s with
        | (.error e, s1) => (.error e, s1)
        | (.ok db, s1) =>
          let (res, s2) := action db s1
          let (closeRes, s3) := ops.closeDb db s2
          match res with
          | .error e => (.error e, s3)
          | .ok a =>
            match closeRes with
            | .error e => (.error e, s3)
            | .ok () => (.ok a, s3)
    withTransaction := fun db action s =>
      match goodExec ops db "BEGIN IMMEDIATE" #[] s with
      | (.error e, s1) => (.error e, s1)
      | (.ok (), s1) =>
        let (res, s2) := action db s1
        match res with
        | .error e =>
          let (_, s3) := goodExec ops db "ROLLBACK" #[] s2
          (.error e, s3)
        | .ok a =>
          match goodExec ops db "COMMIT" #[] s2 with
          | (.ok (), s3) => (.ok a, s3)
          | (.error e, s3) =>
            let (_, s4) := goodExec ops db "ROLLBACK" #[] s3
            (.error e, s4)
    exec := goodExec ops
    query := goodQuery ops
    queryOne := goodQueryOne ops
    activeDbCount := ops.activeDbCount
    activeStmtCount := ops.activeStmtCount }

private def buggyEmptyErrApi (base : SqliteApi) : SqliteApi :=
  { base with mapRawError := fun _ => { kind := .ioError, message := "" } }

private def buggyKindApi (base : SqliteApi) : SqliteApi :=
  { base with mapRawError := fun _ => { kind := .ioError, message := "bad" } }

private def buggyValidateReadOnlyApi (base : SqliteApi) : SqliteApi :=
  { base with validateConfig := fun _ => .ok () }

private def buggyWithDbLeakMkApi (ops : RawSqliteOpsM (StateM MockDb)) : SqliteApiM (StateM MockDb) :=
  let base := goodMkApi ops
  { base with
    withDb := fun path cfg action s =>
      match base.validateConfig cfg with
      | .error e => (.error e, s)
      | .ok () =>
        match ops.openDb path cfg s with
        | (.error e, s1) => (.error e, s1)
        | (.ok db, s1) => action db s1 }

private def buggyExecLeakMkApi (ops : RawSqliteOpsM (StateM MockDb)) : SqliteApiM (StateM MockDb) :=
  let base := goodMkApi ops
  { base with
    exec := fun db sql params s =>
      match ops.prepare db sql s with
      | (.error e, s1) => (.error e, s1)
      | (.ok stmt, s1) =>
        match ops.bind stmt params s1 with
        | (.error e, s2) => (.error e, s2)
        | (.ok (), s2) =>
          match ops.step stmt s2 with
          | (.error e, s3) => (.error e, s3)
          | (.ok _, s3) => ops.finalize stmt s3 }

private def buggyQueryLeakLoop (ops : RawSqliteOpsM (StateM MockDb)) (stmt : StmtHandle)
    (acc : Array SqliteRow) : Nat → StateM MockDb (Except SqliteError (Array SqliteRow))
  | 0 => pure (.error { kind := .ioError, message := "fuel" })
  | fuel + 1 => fun s =>
    match ops.step stmt s with
    | (.error e, s1) => (.error e, s1)
    | (.ok .done, s1) =>
      let (_, s2) := ops.finalize stmt s1
      (.ok acc, s2)
    | (.ok (.row r), s1) => buggyQueryLeakLoop ops stmt (acc.push r) fuel s1

private def buggyQueryLeakMkApi (ops : RawSqliteOpsM (StateM MockDb)) : SqliteApiM (StateM MockDb) :=
  let base := goodMkApi ops
  { base with
    query := fun db sql params s =>
      match ops.prepare db sql s with
      | (.error e, s1) => (.error e, s1)
      | (.ok stmt, s1) =>
        match ops.bind stmt params s1 with
        | (.error e, s2) => (.error e, s2)
        | (.ok (), s2) => buggyQueryLeakLoop ops stmt #[] 4 s2 }

private def buggyQueryOneLeakMkApi (ops : RawSqliteOpsM (StateM MockDb)) : SqliteApiM (StateM MockDb) :=
  let base := goodMkApi ops
  { base with
    queryOne := fun db sql params s =>
      match ops.prepare db sql s with
      | (.error e, s1) => (.error e, s1)
      | (.ok stmt, s1) =>
        match ops.bind stmt params s1 with
        | (.error e, s2) => (.error e, s2)
        | (.ok (), s2) =>
          match ops.step stmt s2 with
          | (.error e, s3) => (.error e, s3)
          | (.ok .done, s3) =>
            let (_, s4) := ops.finalize stmt s3
            (.ok none, s4)
          | (.ok (.row r), s3) =>
            let (_, s4) := ops.finalize stmt s3
            (.ok (some r), s4) }

private def buggyNoCommitMkApi (ops : RawSqliteOpsM (StateM MockDb)) : SqliteApiM (StateM MockDb) :=
  let base := goodMkApi ops
  { base with
    withTransaction := fun db action s =>
      match base.exec db "BEGIN" #[] s with
      | (.error e, s1) => (.error e, s1)
      | (.ok (), s1) => action db s1 }

private def buggyNoRollbackMkApi (ops : RawSqliteOpsM (StateM MockDb)) : SqliteApiM (StateM MockDb) :=
  let base := goodMkApi ops
  { base with
    withTransaction := fun db action s =>
      match base.exec db "BEGIN" #[] s with
      | (.error e, s1) => (.error e, s1)
      | (.ok (), s1) =>
        match action db s1 with
        | (.error e, s2) => (.error e, s2)
        | (.ok a, s2) =>
          match base.exec db "COMMIT" #[] s2 with
          | (.error e, s3) => (.error e, s3)
          | (.ok (), s3) => (.ok a, s3) }

private def buggyInterpolateMkApi (ops : RawSqliteOpsM (StateM MockDb)) : SqliteApiM (StateM MockDb) :=
  let base := goodMkApi ops
  { base with
    exec := fun db sql _params => base.exec db (sql ++ " -- interpolated") #[] }

private def buggyInterpolateQueryOneMkApi (ops : RawSqliteOpsM (StateM MockDb)) : SqliteApiM (StateM MockDb) :=
  let base := goodMkApi ops
  { base with
    queryOne := fun db sql _params => base.queryOne db (sql ++ " -- interpolated") #[] }

private def buggyDropOpenCfgMkApi (ops : RawSqliteOpsM (StateM MockDb)) : SqliteApiM (StateM MockDb) :=
  let base := goodMkApi ops
  { base with
    withDb := fun path _cfg action => base.withDb path {} action }

example : ¬ Core.AllPass (test_sqlite_mapRawError_returnsNonEmptyMessage (buggyEmptyErrApi stubGoodApi)) := by
  intro h
  have h0 := h (.userError "boom")
  simp [buggyEmptyErrApi, assert] at h0

example : ¬ Core.AllPass (test_sqlite_mapRawError_mapsExpectedKinds (buggyKindApi stubGoodApi)) := by
  intro h
  have h0 := h none 5 "locked"
  simp [buggyKindApi, bind, assert] at h0

example : ¬ Core.AllPass (test_sqlite_validateConfig_rejectsReadOnlyWithCreate (buggyValidateReadOnlyApi stubGoodApi)) := by
  intro h
  have h0 := h { readOnly := true, createIfMissing := true } ⟨rfl, rfl⟩
  simp [buggyValidateReadOnlyApi, assert] at h0

example : ¬ Core.AllPass (test_sqlite_validateConfig_rejectsExcessiveBusyTimeout (buggyValidateReadOnlyApi stubGoodApi)) := by
  intro h
  have h0 := h { busyTimeoutMs := maxBusyTimeoutMs + 1 } (by decide)
  simp [buggyValidateReadOnlyApi, assert] at h0

example : ¬ Core.AllPass (test_sqlite_validateConfig_acceptsValidConfig
    { stubGoodApi with validateConfig := fun _ => .error { kind := .invalidInput, message := "bad" } }) := by
  intro h
  have h0 := h {} (by decide) (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_sqlite_withDb_preservesActiveDbCount_andPropagatesBusy buggyWithDbLeakMkApi) := by
  intro h
  have h0 := h "db" {} false { kind := .ioError, message := "e" } (by decide)
  dsimp only [test_sqlite_withDb_preservesActiveDbCount_andPropagatesBusy, Core.NondetTest.assert,
    bind, StateT.run] at h0
  simp only [Bool.false_eq_true, ↓reduceIte] at h0
  have hLen : ((buggyWithDbLeakMkApi mockRawOps).withDb "db"
      { busyTimeoutMs := 5000 % (maxBusyTimeoutMs + 1) } (fun _ => pure (.ok "done"))
      {}).2.openDbs.length = 1 := rfl
  have hBad := h0.1.1
  rw [hLen] at hBad
  cases hBad

example : ¬ Core.AllPass (test_sqlite_exec_preservesActiveStmtCount_andPropagatesErrors buggyExecLeakMkApi) := by
  intro h
  have h0 := h "x" #[] (.failStep .busy) (by decide) (by decide)
  dsimp only [test_sqlite_exec_preservesActiveStmtCount_andPropagatesErrors, Core.NondetTest.assert,
    bind, StateT.run] at h0
  have hLen : ((buggyExecLeakMkApi mockRawOps).exec { id := 1 } "x" #[]
      { openDbs := [1], nextDbId := 2, failMode := .failStep .busy }).2.openStmts.length = 1 := rfl
  have hBad := h0.1.1
  rw [hLen] at hBad
  cases hBad

example : ¬ Core.AllPass (test_sqlite_query_collectsRows_andPreservesActiveStmtCount buggyQueryLeakMkApi) := by
  intro h
  have h0 := h #[.int 1] #[.int 2] #[]
  dsimp only [test_sqlite_query_collectsRows_andPreservesActiveStmtCount, Core.NondetTest.assert,
    bind, StateT.run] at h0
  have hLen : ((buggyQueryLeakMkApi mockRawOps).query { id := 1 }
      "SELECT id, name FROM items WHERE id = ?" #[]
      { openDbs := [1], nextDbId := 2, queryRows := #[#[.int 1], #[.int 2]],
        failMode := .failStepAfterFirstRow .busy }).2.openStmts.length = 1 := rfl
  have hBad := h0.2.1.2.1
  rw [hLen] at hBad
  cases hBad

example : ¬ Core.AllPass (test_sqlite_queryOne_returnsOptionalRow_andPreservesActiveStmtCount buggyQueryOneLeakMkApi) := by
  intro h
  have h0 := h #[.int 1] #[]
  dsimp only [test_sqlite_queryOne_returnsOptionalRow_andPreservesActiveStmtCount, Core.NondetTest.assert,
    bind, StateT.run] at h0
  have hLen : ((buggyQueryOneLeakMkApi mockRawOps).queryOne { id := 1 }
      "SELECT id FROM items WHERE id = ?" #[]
      { openDbs := [1], nextDbId := 2, queryRows := #[#[.int 1]],
        failMode := .failStep .busy }).2.openStmts.length = 1 := rfl
  have hBad := h0.2.2.1.2.1
  rw [hLen] at hBad
  cases hBad

example : ¬ Core.AllPass (test_sqlite_withTransaction_commitsOnOk buggyNoCommitMkApi) := by
  intro h
  have h0 := h (.int 42)
  dsimp only [test_sqlite_withTransaction_commitsOnOk, Core.NondetTest.assert,
    bind, StateT.run] at h0
  have hComm : ((buggyNoCommitMkApi mockRawOps).withTransaction { id := 1 }
      (txCommitBody (buggyNoCommitMkApi mockRawOps) (.int 42))
      { openDbs := [1], nextDbId := 2, failMode := .none }).2.committedWrites = [] := rfl
  have hBad := h0.2.2.1
  rw [hComm] at hBad
  cases hBad

example : ¬ Core.AllPass (test_sqlite_withTransaction_rollsBackOnError buggyNoRollbackMkApi) := by
  intro h
  have h0 := h (.int 42) { kind := .constraint, message := "fail" }
  dsimp only [test_sqlite_withTransaction_rollsBackOnError, Core.NondetTest.assert,
    bind, StateT.run] at h0
  have hInTx : ((buggyNoRollbackMkApi mockRawOps).withTransaction { id := 1 }
      (txRollbackBody (buggyNoRollbackMkApi mockRawOps) (.int 42) { kind := .constraint, message := "fail" })
      { openDbs := [1], nextDbId := 2,
        committedWrites := [("INSERT INTO items(v) VALUES (?)", #[.int 1])],
        failMode := .none }).2.inTransaction = true := rfl
  have hBad := h0.2.1.1
  rw [hInTx] at hBad
  cases hBad

example : ¬ Core.AllPass (test_sqlite_withTransaction_rollsBackOnCommitAndBeginBusy buggyNoRollbackMkApi) := by
  intro h
  have h0 := h (.int 42)
  dsimp only [test_sqlite_withTransaction_rollsBackOnCommitAndBeginBusy, Core.NondetTest.assert,
    bind, StateT.run] at h0
  have hInTx : ((buggyNoRollbackMkApi mockRawOps).withTransaction { id := 1 }
      (txExecInsert (buggyNoRollbackMkApi mockRawOps) (.int 42))
      { openDbs := [1], nextDbId := 2, failMode := .failCommit .busy }).2.inTransaction = true := rfl
  have hBad := h0.2.2.2.2.1.2.2
  rw [hInTx] at hBad
  cases hBad

example : ¬ Core.AllPass (test_sqlite_binding_noSqlStringInterpolation buggyInterpolateMkApi) := by
  intro h
  have h0 := h "'; DROP TABLE users; --" 7
  dsimp only [test_sqlite_binding_noSqlStringInterpolation, Core.NondetTest.nondet,
    Core.NondetTest.assert, bind, StateT.run] at h0
  have hBound : ((buggyInterpolateMkApi mockRawOps).queryOne { id := 1 }
      "SELECT name, age FROM users WHERE name = ? AND age = ? LIMIT 1"
      #[.text "'; DROP TABLE users; --", .int 7]
      ((buggyInterpolateMkApi mockRawOps).query { id := 1 }
        "SELECT name, age FROM users WHERE name = ? AND age = ?"
        #[.text "'; DROP TABLE users; --", .int 7]
        ((buggyInterpolateMkApi mockRawOps).exec { id := 1 }
          "INSERT INTO users(name, age) VALUES (?, ?)" #[.text "'; DROP TABLE users; --", .int 7]
          { openDbs := [1], nextDbId := 2, failMode := .none }).2).2).2.boundCalls =
      [("INSERT INTO users(name, age) VALUES (?, ?) -- interpolated", #[]),
       ("SELECT name, age FROM users WHERE name = ? AND age = ?",
        #[.text "'; DROP TABLE users; --", .int 7]),
       ("SELECT name, age FROM users WHERE name = ? AND age = ? LIMIT 1",
        #[.text "'; DROP TABLE users; --", .int 7])] := rfl
  have hBad := h0.2.1
  rw [hBound] at hBad
  simp at hBad

example : ¬ Core.AllPass (test_sqlite_binding_noSqlStringInterpolation buggyInterpolateQueryOneMkApi) := by
  intro h
  have h0 := h "'; DROP TABLE users; --" 7
  dsimp only [test_sqlite_binding_noSqlStringInterpolation, Core.NondetTest.nondet,
    Core.NondetTest.assert, bind, StateT.run] at h0
  have hBound : ((buggyInterpolateQueryOneMkApi mockRawOps).queryOne { id := 1 }
      "SELECT name, age FROM users WHERE name = ? AND age = ? LIMIT 1"
      #[.text "'; DROP TABLE users; --", .int 7]
      ((buggyInterpolateQueryOneMkApi mockRawOps).query { id := 1 }
        "SELECT name, age FROM users WHERE name = ? AND age = ?"
        #[.text "'; DROP TABLE users; --", .int 7]
        ((buggyInterpolateQueryOneMkApi mockRawOps).exec { id := 1 }
          "INSERT INTO users(name, age) VALUES (?, ?)" #[.text "'; DROP TABLE users; --", .int 7]
          { openDbs := [1], nextDbId := 2, failMode := .none }).2).2).2.boundCalls =
      [("INSERT INTO users(name, age) VALUES (?, ?)",
        #[.text "'; DROP TABLE users; --", .int 7]),
       ("SELECT name, age FROM users WHERE name = ? AND age = ?",
        #[.text "'; DROP TABLE users; --", .int 7]),
       ("SELECT name, age FROM users WHERE name = ? AND age = ? LIMIT 1 -- interpolated", #[])] := rfl
  have hBad := h0.2.1
  rw [hBound] at hBad
  simp at hBad

example : ¬ Core.AllPass (test_sqlite_withDb_preservesActiveDbCount_andPropagatesBusy buggyDropOpenCfgMkApi) := by
  intro h
  have h0 := h "db" { busyTimeoutMs := 123, walMode := false } false { kind := .ioError, message := "e" } (by decide)
  dsimp only [test_sqlite_withDb_preservesActiveDbCount_andPropagatesBusy, Core.NondetTest.assert,
    bind, StateT.run] at h0
  simp only [Bool.false_eq_true, ↓reduceIte] at h0
  have hCalls : ((buggyDropOpenCfgMkApi mockRawOps).withDb "db"
      { busyTimeoutMs := 123 % (maxBusyTimeoutMs + 1), walMode := false }
      (fun _ => pure (.ok "done"))
      {}).2.openCalls = [("db", {})] := rfl
  have hBad := h0.1.2.2
  rw [hCalls] at hBad
  simp at hBad

example : ¬ Core.AllPass (test_sqlite_withDb_withTransaction_preservesAllHandles buggyWithDbLeakMkApi) := by
  intro h
  have h0 := h (.int 99)
  dsimp only [test_sqlite_withDb_withTransaction_preservesAllHandles, Core.NondetTest.assert,
    bind, StateT.run] at h0
  have hOpen : ((buggyWithDbLeakMkApi mockRawOps).withDb ":memory:" {}
      (dbTxExec (buggyWithDbLeakMkApi mockRawOps) (.int 99))
      {}).2.openDbs.length = 1 := rfl
  have hBad := h0.2.1.1
  rw [hOpen] at hBad
  cases hBad

end LeanSwe.Sqlite
