import Core.NondetTest
import LeanSwe.Sqlite.Types
import LeanSwe.Sqlite.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Sqlite`. -/

namespace LeanSwe.Sqlite

open Core (NondetTest)
open Core.NondetTest

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
          match res, closeRes with
          | .error e, _ => (.error e, s3)
          | .ok _, .error e => (.error e, s3)
          | .ok a, .ok () => (.ok a, s3)
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

private def buggyDiscardCloseMkApi (ops : RawSqliteOpsM (StateM MockDb)) : SqliteApiM (StateM MockDb) :=
  let base := goodMkApi ops
  { base with
    withDb := fun path cfg action s =>
      match base.validateConfig cfg with
      | .error e => (.error e, s)
      | .ok () =>
        match ops.openDb path cfg s with
        | (.error e, s1) => (.error e, s1)
        | (.ok db, s1) =>
          let (res, s2) := action db s1
          let (_, s3) := ops.closeDb db s2
          (res, s3) }

private def buggyDiscardFinalizeExecMkApi (ops : RawSqliteOpsM (StateM MockDb)) : SqliteApiM (StateM MockDb) :=
  let base := goodMkApi ops
  { base with
    exec := fun db sql params s =>
      match ops.prepare db sql s with
      | (.error e, s1) => (.error e, s1)
      | (.ok stmt, s1) =>
        match ops.bind stmt params s1 with
        | (.error e, s2) => (.error e, ops.finalize stmt s2 |>.2)
        | (.ok (), s2) =>
          match ops.step stmt s2 with
          | (.error e, s3) => (.error e, ops.finalize stmt s3 |>.2)
          | (.ok _, s3) => (.ok (), (ops.finalize stmt s3).2) }

private def buggyDiscardFinalizeQueryMkApi (ops : RawSqliteOpsM (StateM MockDb)) : SqliteApiM (StateM MockDb) :=
  let base := goodMkApi ops
  { base with
    query := fun db sql params s =>
      match ops.prepare db sql s with
      | (.error e, s1) => (.error e, s1)
      | (.ok stmt, s1) =>
        match ops.bind stmt params s1 with
        | (.error e, s2) => (.error e, (ops.finalize stmt s2).2)
        | (.ok (), s2) =>
          match ops.step stmt s2 with
          | (.error e, s3) => (.error e, (ops.finalize stmt s3).2)
          | (.ok .done, s3) => (.ok #[], (ops.finalize stmt s3).2)
          | (.ok (.row r), s3) => (.ok #[r], (ops.finalize stmt s3).2) }

private def buggyDiscardFinalizeQueryOneMkApi (ops : RawSqliteOpsM (StateM MockDb)) : SqliteApiM (StateM MockDb) :=
  let base := goodMkApi ops
  { base with
    queryOne := fun db sql params s =>
      match ops.prepare db sql s with
      | (.error e, s1) => (.error e, s1)
      | (.ok stmt, s1) =>
        match ops.bind stmt params s1 with
        | (.error e, s2) => (.error e, (ops.finalize stmt s2).2)
        | (.ok (), s2) =>
          match ops.step stmt s2 with
          | (.error e, s3) => (.error e, (ops.finalize stmt s3).2)
          | (.ok .done, s3) => (.ok none, (ops.finalize stmt s3).2)
          | (.ok (.row r), s3) => (.ok (some r), (ops.finalize stmt s3).2) }

private def buggyOverwriteRollbackTxBodyMkApi (ops : RawSqliteOpsM (StateM MockDb)) : SqliteApiM (StateM MockDb) :=
  let base := goodMkApi ops
  { base with
    withTransaction := fun db action => do
      match ← base.exec db "BEGIN IMMEDIATE" #[] with
      | .error e => pure (.error e)
      | .ok () =>
        let (res, finRes) ← tryFinally' (action db) fun
          | some (.ok _) => base.exec db "COMMIT" #[]
          | _ => base.exec db "ROLLBACK" #[]
        match res with
        | .error e =>
          match finRes with
          | .error rbErr => pure (.error rbErr)
          | .ok () => pure (.error e)
        | .ok a =>
          match finRes with
          | .ok () => pure (.ok a)
          | .error e =>
            let _ ← base.exec db "ROLLBACK" #[]
            pure (.error e) }

private def buggyOverwriteRollbackCommitMkApi (ops : RawSqliteOpsM (StateM MockDb)) : SqliteApiM (StateM MockDb) :=
  let base := goodMkApi ops
  { base with
    withTransaction := fun db action => do
      match ← base.exec db "BEGIN IMMEDIATE" #[] with
      | .error e => pure (.error e)
      | .ok () =>
        let (res, finRes) ← tryFinally' (action db) fun
          | some (.ok _) => base.exec db "COMMIT" #[]
          | _ => base.exec db "ROLLBACK" #[]
        match res with
        | .error e => pure (.error e)
        | .ok a =>
          match finRes with
          | .ok () => pure (.ok a)
          | .error e =>
            match ← base.exec db "ROLLBACK" #[] with
            | .error rbErr => pure (.error rbErr)
            | .ok () => pure (.error e) }

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
  have h0 := h "DELETE FROM items" #[] (.failStep .busy) (by decide) (by decide)
  dsimp only [test_sqlite_exec_preservesActiveStmtCount_andPropagatesErrors, Core.NondetTest.assert,
    bind, StateT.run] at h0
  have hLen : ((buggyExecLeakMkApi mockRawOps).exec { id := 1 } "DELETE FROM items" #[]
      { openDbs := [1], nextDbId := 2, failMode := .failStep .busy }).2.openStmts.length = 1 := rfl
  have hBad := h0.1.1
  rw [hLen] at hBad
  cases hBad

example : ¬ Core.AllPass (test_sqlite_query_collectsRows_andPreservesActiveStmtCount buggyQueryLeakMkApi) := by
  intro h
  have h0 := h #[.int 1] #[.int 2] #[.int 7]
  dsimp only [test_sqlite_query_collectsRows_andPreservesActiveStmtCount, Core.NondetTest.assert,
    bind, StateT.run] at h0
  have hLen : ((buggyQueryLeakMkApi mockRawOps).query { id := 1 }
      "SELECT id, name FROM items WHERE id = ?" #[.int 7]
      { openDbs := [1], nextDbId := 2, queryRows := #[#[.int 1], #[.int 2]],
        failMode := .failStepAfterFirstRow .busy }).2.openStmts.length = 1 := rfl
  have hBad := h0.2.1.2.1
  rw [hLen] at hBad
  cases hBad

example : ¬ Core.AllPass (test_sqlite_queryOne_returnsOptionalRow_andPreservesActiveStmtCount buggyQueryOneLeakMkApi) := by
  intro h
  have h0 := h #[.int 1] #[.int 7]
  dsimp only [test_sqlite_queryOne_returnsOptionalRow_andPreservesActiveStmtCount, Core.NondetTest.assert,
    bind, StateT.run] at h0
  have hLen : ((buggyQueryOneLeakMkApi mockRawOps).queryOne { id := 1 }
      "SELECT id FROM items WHERE id = ?" #[.int 7]
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
  erw [hComm] at hBad
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
  erw [hInTx] at hBad
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
  erw [hInTx] at hBad
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
  erw [hOpen] at hBad
  cases hBad

example : ¬ Core.AllPass (test_sqlite_defaultApi_agreesWithModelValidator (buggyKindApi stubGoodApi)) := by
  intro h
  have h0 := h (.invalidArgument "bad") {}
  dsimp only [test_sqlite_defaultApi_agreesWithModelValidator, Core.NondetTest.assert, bind] at h0
  have hBad := h0.1
  simp [buggyKindApi, stubGoodApi, Model.mapRawError, Model.nonEmptyMsg] at hBad

example : ¬ Core.AllPass (test_sqlite_cleanupFailuresPropagate buggyDiscardCloseMkApi) := by
  intro h
  have h0 := h false { kind := .busy, message := "b" }
  dsimp only [test_sqlite_cleanupFailuresPropagate, Core.NondetTest.assert, bind, StateT.run] at h0
  have hOut : ((buggyDiscardCloseMkApi mockRawOps).withDb ":memory:" {}
      (fun _ => if false = true then pure (.error { kind := .busy, message := "b" }) else pure (.ok "done"))
      { failMode := .failClose .ioError }).1 = .ok "done" := rfl
  have hBad := h0.1.1
  rw [hOut] at hBad
  rcases hBad with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_sqlite_cleanupFailuresPropagate buggyDiscardFinalizeExecMkApi) := by
  intro h
  have h0 := h false { kind := .busy, message := "b" }
  dsimp only [test_sqlite_cleanupFailuresPropagate, Core.NondetTest.assert, bind, StateT.run] at h0
  have hOut : ((buggyDiscardFinalizeExecMkApi mockRawOps).exec { id := 1 } "DELETE FROM items" #[]
      { openDbs := [1], nextDbId := 2, failMode := .failFinalize .ioError }).1 = .ok () := rfl
  have hBad := h0.2.1.1
  rw [hOut] at hBad
  rcases hBad with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_sqlite_cleanupFailuresPropagate buggyDiscardFinalizeQueryMkApi) := by
  intro h
  have h0 := h false { kind := .busy, message := "b" }
  dsimp only [test_sqlite_cleanupFailuresPropagate, Core.NondetTest.assert, bind, StateT.run] at h0
  have hOut : ((buggyDiscardFinalizeQueryMkApi mockRawOps).query { id := 1 } "SELECT id FROM items" #[]
      { openDbs := [1], nextDbId := 2, failMode := .failFinalize .ioError }).1 = .ok #[] := rfl
  have hBad := h0.2.2.1.1
  rw [hOut] at hBad
  rcases hBad with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_sqlite_cleanupFailuresPropagate buggyDiscardFinalizeQueryOneMkApi) := by
  intro h
  have h0 := h false { kind := .busy, message := "b" }
  dsimp only [test_sqlite_cleanupFailuresPropagate, Core.NondetTest.assert, bind, StateT.run] at h0
  have hOut : ((buggyDiscardFinalizeQueryOneMkApi mockRawOps).queryOne { id := 1 } "SELECT id FROM items" #[]
      { openDbs := [1], nextDbId := 2, failMode := .failFinalize .ioError }).1 = .ok none := rfl
  have hBad := h0.2.2.2.1.1
  rw [hOut] at hBad
  rcases hBad with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_sqlite_cleanupFailuresPropagate buggyOverwriteRollbackTxBodyMkApi) := by
  intro h
  have h0 := h false { kind := .busy, message := "b" }
  dsimp only [test_sqlite_cleanupFailuresPropagate, Core.NondetTest.assert, bind, StateT.run] at h0
  have hOut : ((buggyOverwriteRollbackTxBodyMkApi mockRawOps).withTransaction (α := String) { id := 1 }
      (fun _ => pure (.error { kind := .busy, message := "b" }))
      { openDbs := [1], nextDbId := 2, failMode := .failRollback .ioError }).1 =
      .error { kind := .ioError, message := "mock rollback failure" } := rfl
  have hBad := h0.2.2.2.2.1.1
  rw [hOut] at hBad
  cases hBad

example : ¬ Core.AllPass (test_sqlite_cleanupFailuresPropagate buggyOverwriteRollbackCommitMkApi) := by
  intro h
  have h0 := h false { kind := .busy, message := "b" }
  dsimp only [test_sqlite_cleanupFailuresPropagate, Core.NondetTest.assert, bind, StateT.run] at h0
  have hOut : ((buggyOverwriteRollbackCommitMkApi mockRawOps).withTransaction (α := String) { id := 1 }
      (fun _ => pure (.ok "done"))
      { openDbs := [1], nextDbId := 2, failMode := .failCommitThenRollback .busy .ioError }).1 =
      .error { kind := .ioError, message := "mock rollback failure" } := rfl
  have hBad := h0.2.2.2.2.2.1.1
  rw [hOut] at hBad
  rcases hBad with ⟨e, he, hk⟩
  cases he
  cases hk

private def buggyModelNoRollbackApi : SqliteApiM (StateM Model.SqliteWorldState) :=
  { Model.modelApi with
    withTransaction := fun db action => do
      match ← Model.modelApi.exec db "BEGIN IMMEDIATE" #[] with
      | .error e => pure (.error e)
      | .ok () =>
        let res ← action db
        let _ ← Model.modelApi.exec db "COMMIT" #[]
        pure res }

private def buggyModelEmptyQueryApi : SqliteApiM (StateM Model.SqliteWorldState) :=
  { Model.modelApi with
    query := fun _ _ _ => pure (.ok #[]) }

private theorem mut_state_bind_step {S α β : Type} {f : StateM S α} {k : α → StateM S β}
    {s0 s1 : S} {a : α} (hf : f s0 = (a, s1)) :
    StateT.bind f k s0 = k a s1 := by
  simp [StateT.bind, Bind.bind, hf]

private theorem mut_state_tryFinally_step {S α β : Type} {x : StateM S α}
    {f : Option α → StateM S β} {s0 s1 s2 : S} {a : α} {b : β}
    (hx : x s0 = (a, s1)) (hf : f (some a) s1 = (b, s2)) :
    tryFinally' x f s0 = ((a, b), s2) := by
  change (let (a', s') := x s0; let (b', s'') := f (some a') s'; ((a', b'), s'')) = ((a, b), s2)
  rw [hx]
  dsimp only
  rw [hf]

private def mutTblP0 : Model.TableData :=
  { name := "p"
    cols := [{ name := "id", colType := .integer, primaryKey := true },
             { name := "u", colType := .int, unique := true }]
    strict := true }

private def mutTblC0 : Model.TableData :=
  { name := "c"
    cols := [{ name := "id", colType := .integer, primaryKey := true },
             { name := "pid", colType := .int, notNull := true, references? := some ("p", "id") },
             { name := "tag", colType := .text }]
    strict := true }

private def mutTblP1 : Model.TableData :=
  { mutTblP0 with rows := [(1, #[.int 1, .int 10])] }

private def mutTblC1 : Model.TableData :=
  { mutTblC0 with rows := [(4, #[.int 4, .int 1, .text "live"])] }

private def mutMem (nextStmt : UInt64) (epoch : Nat) (tbls : List (String × Model.TableData))
    (tx : Model.ConnTxState := .autocommit) (writeDirty : Bool := false)
    (cached? : Option (List String) := some ["p", "c"]) : Model.SqliteWorldState :=
  { nextDbId := 2
    nextStmtId := nextStmt
    conns := [{ id := 1, backing := .memory { tables := tbls } epoch,
                effectiveReadOnly := false, foreignKeys := true, tx := tx,
                writeDirty := writeDirty, schemaCache? := cached? }]
    mutGen := 2 * (nextStmt.toNat - 1) }

private def mutS1 : Model.SqliteWorldState := mutMem 1 0 [] .autocommit false none
private def mutS2 : Model.SqliteWorldState := mutMem 2 1 [("p", mutTblP0)] .autocommit false (some ["p"])
private def mutS3 : Model.SqliteWorldState := mutMem 3 2 [("p", mutTblP0), ("c", mutTblC0)]
private def mutS4 : Model.SqliteWorldState := mutMem 4 3 [("c", mutTblC0), ("p", mutTblP1)]
private def mutS5 : Model.SqliteWorldState := mutMem 5 3 [("c", mutTblC0), ("p", mutTblP1)]
private def mutS6 : Model.SqliteWorldState := mutMem 6 3 [("c", mutTblC0), ("p", mutTblP1)]
private def mutS7 : Model.SqliteWorldState := mutMem 7 3 [("c", mutTblC0), ("p", mutTblP1)]
private def mutS8 : Model.SqliteWorldState := mutMem 8 3 [("c", mutTblC0), ("p", mutTblP1)]
private def mutS9 : Model.SqliteWorldState := mutMem 9 3 [("c", mutTblC0), ("p", mutTblP1)]
private def mutS10 : Model.SqliteWorldState := mutMem 10 4 [("p", mutTblP1), ("c", mutTblC1)]

private theorem mut_h_open : Model.modelRawOps.openDb ":memory:" {} {} = (.ok { id := 1 }, mutS1) := rfl
private theorem mut_h_1 :
    Model.modelApi.exec { id := 1 } "CREATE TABLE p(id INTEGER PRIMARY KEY, u INT UNIQUE) STRICT" #[] mutS1 =
      (.ok (), mutS2) := rfl
set_option maxRecDepth 2048 in
private theorem mut_h_2 :
    Model.modelApi.exec { id := 1 } "CREATE TABLE c(id INTEGER PRIMARY KEY, pid INT NOT NULL REFERENCES p(id), tag TEXT) STRICT" #[] mutS2 =
      (.ok (), mutS3) := rfl
private theorem mut_h_3 :
    Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 1, .int 10] mutS3 =
      (.ok (), mutS4) := rfl
private theorem mut_h_4 :
    Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 1, .int 20] mutS4 =
      (.error { kind := .constraint, sqliteCode := some 1555, message := "UNIQUE constraint failed: p" }, mutS5) := rfl
private theorem mut_h_5 :
    Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 10] mutS5 =
      (.error { kind := .constraint, sqliteCode := some 2067, message := "UNIQUE constraint failed: p.u" }, mutS6) := rfl
private theorem mut_h_6 :
    Model.modelApi.exec { id := 1 } "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 1, .int 99, .text "bad"] mutS6 =
      (.error { kind := .constraint, sqliteCode := some 787, message := "FOREIGN KEY constraint failed" }, mutS7) := rfl
private theorem mut_h_7 :
    Model.modelApi.exec { id := 1 } "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 2, .int 1, .bytes ByteArray.empty] mutS7 =
      (.error { kind := .constraint, sqliteCode := some 3091, message := "cannot store value in STRICT column tag" }, mutS8) := rfl
private theorem mut_h_8 :
    Model.modelApi.exec { id := 1 } "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 3, .null, .text "ok"] mutS8 =
      (.error { kind := .constraint, sqliteCode := some 1299, message := "NOT NULL constraint failed: pid" }, mutS9) := rfl
private theorem mut_h_9 :
    Model.modelApi.exec { id := 1 } "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 4, .int 1, .text "live"] mutS9 =
      (.ok (), mutS10) := rfl

private theorem mut_do_bind {S α β : Type} {f : StateM S α} {k : α → StateM S β}
    {s0 s1 : S} {a : α} (hf : f s0 = (a, s1)) :
    (f >>= k) s0 = k a s1 := by
  change (match f s0 with | (a', s') => k a' s') = k a s1
  rw [hf]

private theorem mut_allPass_assert_bind {P : Prop} {k : Unit → Core.AllPassRun Unit}
    {post : Unit → Prop} :
    (Bind.bind (Core.NondetTest.assert (runner := Core.AllPassRun) P) k) post =
      (P ∧ k () post) := rfl

private theorem mut_allPass_assert_end {P : Prop} :
    (Core.NondetTest.assert (runner := Core.AllPassRun) P) (fun _ => True) = (P ∧ True) := rfl

private theorem mut_withDb_memory_step {β : Type}
    (body : DbHandle → StateM Model.SqliteWorldState (Except SqliteError β))
    {s1 s2 : Model.SqliteWorldState} {res : Except SqliteError β}
    (hBody : body { id := 1 } mutS1 = (res, s1))
    (hClose : Model.modelRawOps.closeDb { id := 1 } s1 = (.ok (), s2)) :
    Model.modelApi.withDb ":memory:" {} body {} = (res, s2) := by
  dsimp only [Model.modelApi]
  have hVal : Model.validateConfigWith Model.modelRawOps.mapRawError {} = .ok () := rfl
  rw [hVal]
  dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure]
  rw [mut_h_open]
  dsimp only
  rw [mut_state_bind_step (mut_state_tryFinally_step hBody hClose)]
  cases res <;> rfl

private def mutTblP2 : Model.TableData :=
  { mutTblP0 with rows := [(1, #[.int 1, .int 10]), (2, #[.int 2, .int 20])] }
private def mutTblP3NoRb : Model.TableData :=
  { mutTblP0 with rows := [(1, #[.int 1, .int 10]), (2, #[.int 2, .int 20]), (3, #[.int 3, .int 30])] }
private def mutTblP4NoRb : Model.TableData :=
  { mutTblP0 with rows := [(1, #[.int 1, .int 10]), (2, #[.int 2, .int 20]), (3, #[.int 3, .int 31])] }
private def mutTblP5NoRb : Model.TableData :=
  { mutTblP0 with rows := [(2, #[.int 2, .int 20]), (3, #[.int 3, .int 31])] }

private def mutNoRbS11 : Model.SqliteWorldState := mutMem 13 5 [("c", mutTblC1), ("p", mutTblP2)]
private def mutNoRbS12 : Model.SqliteWorldState := mutMem 16 6 [("c", mutTblC1), ("p", mutTblP3NoRb)]
private def mutNoRbS13 : Model.SqliteWorldState := mutMem 17 6 [("c", mutTblC1), ("p", mutTblP3NoRb)]
private def mutNoRbS14 : Model.SqliteWorldState := mutMem 18 6 [("c", mutTblC1), ("p", mutTblP3NoRb)]
private def mutNoRbS15 : Model.SqliteWorldState := mutMem 19 7 [("c", mutTblC1), ("p", mutTblP4NoRb)]
private def mutNoRbS16 : Model.SqliteWorldState := mutMem 20 8 [("p", mutTblP4NoRb), ("c", mutTblC0)]
private def mutNoRbS17 : Model.SqliteWorldState := mutMem 21 9 [("c", mutTblC0), ("p", mutTblP5NoRb)]
private def mutNoRbS18 : Model.SqliteWorldState := mutMem 22 9 [("c", mutTblC0), ("p", mutTblP5NoRb)]
private def mutNoRbS19 : Model.SqliteWorldState := { mutNoRbS18 with conns := [] }

private theorem mut_norb_h10a : Model.modelApi.exec { id := 1 } "BEGIN IMMEDIATE" #[] mutS10 =
    (.ok (), mutMem 11 4 [("p", mutTblP1), ("c", mutTblC1)]
      (.write 4 { tables := [("p", mutTblP1), ("c", mutTblC1)] })) := rfl
private theorem mut_norb_h10b : Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 20]
    (mutMem 11 4 [("p", mutTblP1), ("c", mutTblC1)]
      (.write 4 { tables := [("p", mutTblP1), ("c", mutTblC1)] })) =
    (.ok (), mutMem 12 4 [("p", mutTblP1), ("c", mutTblC1)]
      (.write 4 { tables := [("c", mutTblC1), ("p", mutTblP2)] }) true) := by with_unfolding_all rfl
private theorem mut_norb_h10c : Model.modelApi.exec { id := 1 } "COMMIT" #[]
    (mutMem 12 4 [("p", mutTblP1), ("c", mutTblC1)]
      (.write 4 { tables := [("c", mutTblC1), ("p", mutTblP2)] }) true) =
    (.ok (), mutNoRbS11) := rfl
private theorem mut_norb_h11a : Model.modelApi.exec { id := 1 } "BEGIN IMMEDIATE" #[] mutNoRbS11 =
    (.ok (), mutMem 14 5 [("c", mutTblC1), ("p", mutTblP2)]
      (.write 5 { tables := [("c", mutTblC1), ("p", mutTblP2)] })) := rfl
private theorem mut_norb_h11b : Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 3, .int 30]
    (mutMem 14 5 [("c", mutTblC1), ("p", mutTblP2)]
      (.write 5 { tables := [("c", mutTblC1), ("p", mutTblP2)] })) =
    (.ok (), mutMem 15 5 [("c", mutTblC1), ("p", mutTblP2)]
      (.write 5 { tables := [("c", mutTblC1), ("p", mutTblP3NoRb)] }) true) := by with_unfolding_all rfl
private theorem mut_norb_h11c : Model.modelApi.exec { id := 1 } "COMMIT" #[]
    (mutMem 15 5 [("c", mutTblC1), ("p", mutTblP2)]
      (.write 5 { tables := [("c", mutTblC1), ("p", mutTblP3NoRb)] }) true) =
    (.ok (), mutNoRbS12) := rfl
private theorem mut_norb_h12 :
    Model.modelApi.query { id := 1 } "SELECT id, u FROM p WHERE id >= ? ORDER BY id DESC LIMIT ?" #[.int 1, .int 2] mutNoRbS12 =
      (.ok #[#[.int 3, .int 30], #[.int 2, .int 20]], mutNoRbS13) := by with_unfolding_all rfl
private theorem mut_norb_h13 :
    Model.modelApi.queryOne { id := 1 } "SELECT tag FROM c WHERE id = ?" #[.int 4] mutNoRbS13 =
      (.ok (some #[.text "live"]), mutNoRbS14) := by with_unfolding_all rfl
private theorem mut_norb_h14 :
    Model.modelApi.exec { id := 1 } "UPDATE p SET u = ? WHERE id = ?" #[.int 31, .int 3] mutNoRbS14 =
      (.ok (), mutNoRbS15) := by with_unfolding_all rfl
private theorem mut_norb_h15 :
    Model.modelApi.exec { id := 1 } "DELETE FROM c WHERE pid = ?" #[.int 1] mutNoRbS15 =
      (.ok (), mutNoRbS16) := by with_unfolding_all rfl
private theorem mut_norb_h16 :
    Model.modelApi.exec { id := 1 } "DELETE FROM p WHERE id = ?" #[.int 1] mutNoRbS16 =
      (.ok (), mutNoRbS17) := by with_unfolding_all rfl
private theorem mut_norb_h17 :
    Model.modelApi.query { id := 1 } "SELECT id, u FROM p ORDER BY id ASC" #[] mutNoRbS17 =
      (.ok #[#[.int 2, .int 20], #[.int 3, .int 31]], mutNoRbS18) := by with_unfolding_all rfl
private theorem mut_norb_hClose :
    Model.modelRawOps.closeDb { id := 1 } mutNoRbS18 = (.ok (), mutNoRbS19) := rfl

private theorem mut_norb_run :
    (Model.modelApi.withDb ":memory:" {} fun db => do
      let _ ← Model.modelApi.exec db "CREATE TABLE p(id INTEGER PRIMARY KEY, u INT UNIQUE) STRICT" #[]
      let _ ← Model.modelApi.exec db "CREATE TABLE c(id INTEGER PRIMARY KEY, pid INT NOT NULL REFERENCES p(id), tag TEXT) STRICT" #[]
      let _ ← Model.modelApi.exec db "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 1, .int 10]
      let dupPk ← Model.modelApi.exec db "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 1, .int 20]
      let dupUk ← Model.modelApi.exec db "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 10]
      let fkErr ← Model.modelApi.exec db "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 1, .int 99, .text "bad"]
      let strictErr ← Model.modelApi.exec db "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 2, .int 1, .bytes ByteArray.empty]
      let nullErr ← Model.modelApi.exec db "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 3, .null, .text "ok"]
      let _ ← Model.modelApi.exec db "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 4, .int 1, .text "live"]
      let _ ← (do
        match ← Model.modelApi.exec db "BEGIN IMMEDIATE" #[] with
        | .error e => pure (Except.error e : Except SqliteError Unit)
        | .ok () =>
          let res : Except SqliteError Unit ← (do
            let _ ← Model.modelApi.exec db "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 20]
            pure (Except.error { kind := .constraint, message := "force rollback" } : Except SqliteError Unit))
          let _ ← Model.modelApi.exec db "COMMIT" #[]
          pure res)
      let _ ← (do
        match ← Model.modelApi.exec db "BEGIN IMMEDIATE" #[] with
        | .error e => pure (Except.error e : Except SqliteError Unit)
        | .ok () =>
          let res ← Model.modelApi.exec db "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 3, .int 30]
          let _ ← Model.modelApi.exec db "COMMIT" #[]
          pure res)
      let pRows ← Model.modelApi.query db "SELECT id, u FROM p WHERE id >= ? ORDER BY id DESC LIMIT ?" #[.int 1, .int 2]
      let cOne ← Model.modelApi.queryOne db "SELECT tag FROM c WHERE id = ?" #[.int 4]
      let _ ← Model.modelApi.exec db "UPDATE p SET u = ? WHERE id = ?" #[.int 31, .int 3]
      let _ ← Model.modelApi.exec db "DELETE FROM c WHERE pid = ?" #[.int 1]
      let _ ← Model.modelApi.exec db "DELETE FROM p WHERE id = ?" #[.int 1]
      let pAfter ← Model.modelApi.query db "SELECT id, u FROM p ORDER BY id ASC" #[]
      pure (Except.ok (dupPk, dupUk, fkErr, strictErr, nullErr, pRows, cOne, pAfter) : Except SqliteError _)) {} =
      (.ok (.error { kind := .constraint, sqliteCode := some 1555, message := "UNIQUE constraint failed: p" },
            .error { kind := .constraint, sqliteCode := some 2067, message := "UNIQUE constraint failed: p.u" },
            .error { kind := .constraint, sqliteCode := some 787, message := "FOREIGN KEY constraint failed" },
            .error { kind := .constraint, sqliteCode := some 3091, message := "cannot store value in STRICT column tag" },
            .error { kind := .constraint, sqliteCode := some 1299, message := "NOT NULL constraint failed: pid" },
            .ok #[#[.int 3, .int 30], #[.int 2, .int 20]],
            .ok (some #[.text "live"]),
            .ok #[#[.int 2, .int 20], #[.int 3, .int 31]]), mutNoRbS19) := by
  have h10 : (do
      match ← Model.modelApi.exec { id := 1 } "BEGIN IMMEDIATE" #[] with
      | .error e => pure (Except.error e : Except SqliteError Unit)
      | .ok () =>
        let res : Except SqliteError Unit ← (do
          let _ ← Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 20]
          pure (Except.error { kind := .constraint, message := "force rollback" } : Except SqliteError Unit))
        let _ ← Model.modelApi.exec { id := 1 } "COMMIT" #[]
        pure res) mutS10 = (.error { kind := .constraint, message := "force rollback" }, mutNoRbS11) := by
    have hInner : (do
          let _ ← Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 20]
          pure (Except.error { kind := .constraint, message := "force rollback" } : Except SqliteError Unit))
        (mutMem 11 4 [("p", mutTblP1), ("c", mutTblC1)]
          (.write 4 { tables := [("p", mutTblP1), ("c", mutTblC1)] })) =
        (.error { kind := .constraint, message := "force rollback" },
          mutMem 12 4 [("p", mutTblP1), ("c", mutTblC1)]
            (.write 4 { tables := [("c", mutTblC1), ("p", mutTblP2)] }) true) := by
      rw [mut_do_bind mut_norb_h10b]; rfl
    rw [mut_do_bind mut_norb_h10a]; dsimp only
    rw [mut_do_bind hInner]
    rw [mut_do_bind mut_norb_h10c]; rfl
  have h11 : (do
      match ← Model.modelApi.exec { id := 1 } "BEGIN IMMEDIATE" #[] with
      | .error e => pure (Except.error e : Except SqliteError Unit)
      | .ok () =>
        let res ← Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 3, .int 30]
        let _ ← Model.modelApi.exec { id := 1 } "COMMIT" #[]
        pure res) mutNoRbS11 = (.ok (), mutNoRbS12) := by
    rw [mut_do_bind mut_norb_h11a]; dsimp only
    rw [mut_do_bind mut_norb_h11b]
    rw [mut_do_bind mut_norb_h11c]; rfl
  exact mut_withDb_memory_step _ (by
    rw [mut_do_bind mut_h_1]
    rw [mut_do_bind mut_h_2]
    rw [mut_do_bind mut_h_3]
    rw [mut_do_bind mut_h_4]
    rw [mut_do_bind mut_h_5]
    rw [mut_do_bind mut_h_6]
    rw [mut_do_bind mut_h_7]
    rw [mut_do_bind mut_h_8]
    rw [mut_do_bind mut_h_9]
    rw [mut_do_bind h10]
    rw [mut_do_bind h11]
    rw [mut_do_bind mut_norb_h12]
    rw [mut_do_bind mut_norb_h13]
    rw [mut_do_bind mut_norb_h14]
    rw [mut_do_bind mut_norb_h15]
    rw [mut_do_bind mut_norb_h16]
    rw [mut_do_bind mut_norb_h17]; rfl) mut_norb_hClose

private theorem mut_not_allPass_of_not_crud (api : SqliteApiM (StateM Model.SqliteWorldState))
    (hNot : ¬ (match (modelApiCrudBlock api).1 with
      | .ok (.error ePk, .error eUk, .error eFk, .error eSt, .error eNu, .ok pRows, .ok cOne, .ok pAfter) =>
        ePk.kind == .constraint && eUk.kind == .constraint && eFk.kind == .constraint &&
        eSt.kind == .constraint && eNu.kind == .constraint &&
        pRows == #[#[.int 3, .int 30], #[.int 1, .int 10]] &&
        cOne == some #[.text "live"] &&
        pAfter == #[#[.int 3, .int 31]]
      | _ => false)) :
    ¬ Core.AllPass (test_sqlite_modelApi_relationalCrudConstraintsAndRollback api) := by
  intro h
  unfold test_sqlite_modelApi_relationalCrudConstraintsAndRollback Core.AllPass at h
  simp only [mut_allPass_assert_bind, mut_allPass_assert_end] at h
  exact hNot h.1

example : ¬ Core.AllPass (test_sqlite_modelApi_relationalCrudConstraintsAndRollback buggyModelNoRollbackApi) :=
  mut_not_allPass_of_not_crud buggyModelNoRollbackApi (by
    dsimp only [modelApiCrudBlock, buggyModelNoRollbackApi, StateT.run]
    rw [mut_norb_run]
    decide)

private def mutTblP3Eq : Model.TableData :=
  { mutTblP0 with rows := [(1, #[.int 1, .int 10]), (3, #[.int 3, .int 30])] }
private def mutTblP4Eq : Model.TableData :=
  { mutTblP0 with rows := [(1, #[.int 1, .int 10]), (3, #[.int 3, .int 31])] }
private def mutTblP5Eq : Model.TableData :=
  { mutTblP0 with rows := [(3, #[.int 3, .int 31])] }

private def mutEqS10a : Model.SqliteWorldState :=
  mutMem 11 4 [("p", mutTblP1), ("c", mutTblC1)] (.write 4 { tables := [("p", mutTblP1), ("c", mutTblC1)] })
private def mutEqS10b : Model.SqliteWorldState :=
  mutMem 12 4 [("p", mutTblP1), ("c", mutTblC1)] (.write 4 { tables := [("c", mutTblC1), ("p", mutTblP2)] }) true
private def mutEqS11 : Model.SqliteWorldState := mutMem 13 4 [("p", mutTblP1), ("c", mutTblC1)]
private def mutEqS11a : Model.SqliteWorldState :=
  mutMem 14 4 [("p", mutTblP1), ("c", mutTblC1)] (.write 4 { tables := [("p", mutTblP1), ("c", mutTblC1)] })
private def mutEqS11b : Model.SqliteWorldState :=
  mutMem 15 4 [("p", mutTblP1), ("c", mutTblC1)] (.write 4 { tables := [("c", mutTblC1), ("p", mutTblP3Eq)] }) true
private def mutEqS12 : Model.SqliteWorldState := mutMem 16 5 [("c", mutTblC1), ("p", mutTblP3Eq)]
private def mutEqS14 : Model.SqliteWorldState := mutMem 17 5 [("c", mutTblC1), ("p", mutTblP3Eq)]
private def mutEqS15 : Model.SqliteWorldState := mutMem 18 6 [("c", mutTblC1), ("p", mutTblP4Eq)]
private def mutEqS16 : Model.SqliteWorldState := mutMem 19 7 [("p", mutTblP4Eq), ("c", mutTblC0)]
private def mutEqS17 : Model.SqliteWorldState := mutMem 20 8 [("c", mutTblC0), ("p", mutTblP5Eq)]
private def mutEqS19 : Model.SqliteWorldState := { mutEqS17 with conns := [] }

private theorem mut_eq_h10b :
    Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 20] mutEqS10a =
      (.ok (), mutEqS10b) := by with_unfolding_all rfl
private theorem mut_eq_h10 :
    Model.modelApi.withTransaction { id := 1 } (fun txDb => do
      let _ ← Model.modelApi.exec txDb "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 20]
      pure (Except.error { kind := .constraint, message := "force rollback" } : Except SqliteError Unit)) mutS10 =
      (.error { kind := .constraint, message := "force rollback" }, mutEqS11) := by
  have hAct : (do
      let _ ← Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 20]
      pure (Except.error { kind := .constraint, message := "force rollback" } : Except SqliteError Unit))
      mutEqS10a =
      (.error { kind := .constraint, message := "force rollback" }, mutEqS10b) := by
    rw [mut_do_bind mut_eq_h10b]; rfl
  dsimp only [Model.modelApi] at hAct ⊢
  rw [mut_do_bind (s0 := mutS10) (s1 := mutEqS10a) (a := Except.ok ()) rfl]
  dsimp only
  rw [mut_do_bind (mut_state_tryFinally_step hAct (rfl : _ = (Except.ok (), mutEqS11)))]
  rfl
private theorem mut_eq_h11b :
    Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 3, .int 30] mutEqS11a =
      (.ok (), mutEqS11b) := by with_unfolding_all rfl
private theorem mut_eq_h11 :
    Model.modelApi.withTransaction { id := 1 } (fun txDb =>
      Model.modelApi.exec txDb "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 3, .int 30]) mutEqS11 =
      (.ok (), mutEqS12) := by
  have h11b := mut_eq_h11b
  dsimp only [Model.modelApi] at h11b ⊢
  rw [mut_do_bind (s0 := mutEqS11) (s1 := mutEqS11a) (a := Except.ok ()) rfl]
  dsimp only
  rw [mut_do_bind (mut_state_tryFinally_step h11b (rfl : _ = (Except.ok (), mutEqS12)))]
  rfl
private theorem mut_eq_h13 :
    Model.modelApi.queryOne { id := 1 } "SELECT tag FROM c WHERE id = ?" #[.int 4] mutEqS12 =
      (.ok (some #[.text "live"]), mutEqS14) := by with_unfolding_all rfl
private theorem mut_eq_h14 :
    Model.modelApi.exec { id := 1 } "UPDATE p SET u = ? WHERE id = ?" #[.int 31, .int 3] mutEqS14 =
      (.ok (), mutEqS15) := by with_unfolding_all rfl
private theorem mut_eq_h15 :
    Model.modelApi.exec { id := 1 } "DELETE FROM c WHERE pid = ?" #[.int 1] mutEqS15 =
      (.ok (), mutEqS16) := by with_unfolding_all rfl
private theorem mut_eq_h16 :
    Model.modelApi.exec { id := 1 } "DELETE FROM p WHERE id = ?" #[.int 1] mutEqS16 =
      (.ok (), mutEqS17) := by with_unfolding_all rfl
private theorem mut_eq_hClose :
    Model.modelRawOps.closeDb { id := 1 } mutEqS17 = (.ok (), mutEqS19) := rfl

private theorem mut_eq_run :
    (Model.modelApi.withDb ":memory:" {} fun db => do
      let _ ← Model.modelApi.exec db "CREATE TABLE p(id INTEGER PRIMARY KEY, u INT UNIQUE) STRICT" #[]
      let _ ← Model.modelApi.exec db "CREATE TABLE c(id INTEGER PRIMARY KEY, pid INT NOT NULL REFERENCES p(id), tag TEXT) STRICT" #[]
      let _ ← Model.modelApi.exec db "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 1, .int 10]
      let dupPk ← Model.modelApi.exec db "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 1, .int 20]
      let dupUk ← Model.modelApi.exec db "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 10]
      let fkErr ← Model.modelApi.exec db "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 1, .int 99, .text "bad"]
      let strictErr ← Model.modelApi.exec db "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 2, .int 1, .bytes ByteArray.empty]
      let nullErr ← Model.modelApi.exec db "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 3, .null, .text "ok"]
      let _ ← Model.modelApi.exec db "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 4, .int 1, .text "live"]
      let _ ← Model.modelApi.withTransaction db fun txDb => do
        let _ ← Model.modelApi.exec txDb "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 20]
        pure (Except.error { kind := .constraint, message := "force rollback" } : Except SqliteError Unit)
      let _ ← Model.modelApi.withTransaction db fun txDb =>
        Model.modelApi.exec txDb "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 3, .int 30]
      let pRows ← (pure (.ok #[]) : StateM Model.SqliteWorldState (Except SqliteError (Array SqliteRow)))
      let cOne ← Model.modelApi.queryOne db "SELECT tag FROM c WHERE id = ?" #[.int 4]
      let _ ← Model.modelApi.exec db "UPDATE p SET u = ? WHERE id = ?" #[.int 31, .int 3]
      let _ ← Model.modelApi.exec db "DELETE FROM c WHERE pid = ?" #[.int 1]
      let _ ← Model.modelApi.exec db "DELETE FROM p WHERE id = ?" #[.int 1]
      let pAfter ← (pure (.ok #[]) : StateM Model.SqliteWorldState (Except SqliteError (Array SqliteRow)))
      pure (Except.ok (dupPk, dupUk, fkErr, strictErr, nullErr, pRows, cOne, pAfter) : Except SqliteError _)) {} =
      (.ok (.error { kind := .constraint, sqliteCode := some 1555, message := "UNIQUE constraint failed: p" },
            .error { kind := .constraint, sqliteCode := some 2067, message := "UNIQUE constraint failed: p.u" },
            .error { kind := .constraint, sqliteCode := some 787, message := "FOREIGN KEY constraint failed" },
            .error { kind := .constraint, sqliteCode := some 3091, message := "cannot store value in STRICT column tag" },
            .error { kind := .constraint, sqliteCode := some 1299, message := "NOT NULL constraint failed: pid" },
            .ok #[],
            .ok (some #[.text "live"]),
            .ok #[]), mutEqS19) := by
  exact mut_withDb_memory_step _ (by
    rw [mut_do_bind mut_h_1]
    rw [mut_do_bind mut_h_2]
    rw [mut_do_bind mut_h_3]
    rw [mut_do_bind mut_h_4]
    rw [mut_do_bind mut_h_5]
    rw [mut_do_bind mut_h_6]
    rw [mut_do_bind mut_h_7]
    rw [mut_do_bind mut_h_8]
    rw [mut_do_bind mut_h_9]
    rw [mut_do_bind mut_eq_h10]
    rw [mut_do_bind mut_eq_h11]
    rw [mut_do_bind (rfl : (pure (.ok #[]) : StateM Model.SqliteWorldState (Except SqliteError (Array SqliteRow))) mutEqS12 = (.ok #[], mutEqS12))]
    rw [mut_do_bind mut_eq_h13]
    rw [mut_do_bind mut_eq_h14]
    rw [mut_do_bind mut_eq_h15]
    rw [mut_do_bind mut_eq_h16]
    rw [mut_do_bind (rfl : (pure (.ok #[]) : StateM Model.SqliteWorldState (Except SqliteError (Array SqliteRow))) mutEqS17 = (.ok #[], mutEqS17))]; rfl) mut_eq_hClose

example : ¬ Core.AllPass (test_sqlite_modelApi_relationalCrudConstraintsAndRollback buggyModelEmptyQueryApi) :=
  mut_not_allPass_of_not_crud buggyModelEmptyQueryApi (by
    dsimp only [modelApiCrudBlock, buggyModelEmptyQueryApi, StateT.run]
    rw [mut_eq_run]
    decide)

end LeanSwe.Sqlite
