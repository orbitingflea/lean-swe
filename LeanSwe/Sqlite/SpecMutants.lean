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

end LeanSwe.Sqlite
