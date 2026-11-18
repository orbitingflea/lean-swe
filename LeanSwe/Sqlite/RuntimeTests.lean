import Core.Assumptions
import LeanSwe.Sqlite.Interface
import LeanSwe.TempDir.Interface

namespace LeanSwe.Sqlite.RuntimeTests

open LeanSwe.Sqlite

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except SqliteError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def assertErrKind {α : Type} (res : Except SqliteError α) (expected : SqliteErrorKind)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")

private def withTempErr (action : String → IO Unit) : IO Unit := do
  let wrap ← LeanSwe.TempDir.withTempDir none "lean-swe-sqlite-rt-" fun tmp => do
    action tmp
    return .ok ()
  match wrap with
  | .error te => throw (IO.userError s!"TempDir failed: {repr te}")
  | .ok () => pure ()

private def testCrudWalFkAndBinding (dbPath : String) : IO Unit := do
  let res ← withDb dbPath {} fun db => do
    let jm ← assertOk (← queryOne db "PRAGMA journal_mode" #[]) "PRAGMA journal_mode"
    assertTrue (jm == some #[.text "wal"]) s!"expected WAL journal_mode, got {repr jm}"

    let fk ← assertOk (← queryOne db "PRAGMA foreign_keys" #[]) "PRAGMA foreign_keys"
    assertTrue (fk == some #[.int 1]) s!"expected foreign_keys = 1, got {repr fk}"

    assertOk (← exec db
      "CREATE TABLE parents(id INTEGER PRIMARY KEY, name TEXT NOT NULL)" #[]) "create parents"
    assertOk (← exec db
      "CREATE TABLE children(id INTEGER PRIMARY KEY, parent_id INTEGER NOT NULL REFERENCES parents(id), score REAL, tag TEXT, payload BLOB, note TEXT)"
      #[]) "create children"

    assertOk (← exec db "INSERT INTO parents(id, name) VALUES (?, ?)"
      #[.int 1, .text "root"]) "insert root parent"

    let orphanRes ← exec db
      "INSERT INTO children(id, parent_id, score, tag, payload, note) VALUES (?, ?, ?, ?, ?, ?)"
      #[.int 10, .int 999, .real 1.25, .text "orphan", .bytes ByteArray.empty, .null]
    assertErrKind orphanRes .constraint "foreign key orphan fails with .constraint"

    let inj := "'; DROP TABLE parents; --"
    let rawBytes := ByteArray.mk #[10, 0, 200, 255]
    assertOk (← exec db
      "INSERT INTO children(id, parent_id, score, tag, payload, note) VALUES (?, ?, ?, ?, ?, ?)"
      #[.int 1, .int 1, .real 2.5, .text inj, .bytes rawBytes, .null]) "insert parameterized child"

    let one? ← assertOk (← queryOne db
      "SELECT id, parent_id, score, tag, payload, note FROM children WHERE tag = ?" #[.text inj])
      "queryOne injection payload"
    assertTrue (one? == some #[.int 1, .int 1, .real 2.5, .text inj, .bytes rawBytes, .null])
      s!"parameterized injection payload roundtrip mismatch: {repr one?}"

    let parents ← assertOk (← query db "SELECT id, name FROM parents ORDER BY id" #[])
      "query parents"
    assertTrue (parents == #[#[.int 1, .text "root"]]) "parents table intact after SQL injection text"

    let emptyOne ← assertOk (← queryOne db "SELECT id FROM children WHERE id = ?" #[.int 404])
      "queryOne missing row"
    assertTrue (emptyOne == none) "queryOne missing returns none"
    return .ok ()

  assertOk res "CRUD/WAL/FK/binding block"
  assertTrue ((← activeDbCount) == 0 && (← activeStmtCount) == 0)
    "handles clean after CRUD block"

private def testTransactionsAndPersistence (dbPath : String) : IO Unit := do
  let txOk ← withDb dbPath {} fun db =>
    withTransaction db fun txDb => do
      if let .error e ← exec txDb "INSERT INTO parents(id, name) VALUES (?, ?)"
          #[.int 2, .text "committed"] then
        return .error e
      return .ok "committed"
  match txOk with
  | .ok "committed" => pure ()
  | _ => throw (IO.userError s!"ASSERTION FAILED: withTransaction commit failed: {repr txOk}")
  assertTrue ((← activeDbCount) == 0 && (← activeStmtCount) == 0) "handles clean after commit"

  let txErr ← withDb dbPath {} fun db =>
    withTransaction db (α := Unit) fun txDb => do
      if let .error e ← exec txDb "INSERT INTO parents(id, name) VALUES (?, ?)"
          #[.int 3, .text "should_rollback"] then
        return .error e
      return .error { kind := .constraint, message := "force rollback" }
  assertErrKind txErr .constraint "withTransaction propagates error after rollback"
  assertTrue ((← activeDbCount) == 0 && (← activeStmtCount) == 0) "handles clean after rollback"

  let rowsRes ← withDb dbPath { readOnly := true, createIfMissing := false } fun db =>
    query db "SELECT id, name FROM parents ORDER BY id" #[]
  let rows ← assertOk rowsRes "readOnly reopen check"
  assertTrue (rows == #[#[.int 1, .text "root"], #[.int 2, .text "committed"]])
    s!"unexpected persisted rows after commit+rollback: {repr rows}"
  assertTrue ((← activeDbCount) == 0 && (← activeStmtCount) == 0) "handles clean after readOnly check"

private def testErrorsAndBusyContention (tmp dbPath : String) : IO Unit := do
  assertErrKind (← withDb dbPath { readOnly := true, createIfMissing := true } (fun _ => pure (.ok ())))
    .invalidInput "invalid config fails before openDb"
  assertErrKind (← withDb dbPath { busyTimeoutMs := maxBusyTimeoutMs + 1 } (fun _ => pure (.ok ())))
    .invalidInput "excessive busyTimeoutMs rejected"
  assertErrKind (← withDb (tmp ++ "/absent/db.sqlite") { createIfMissing := false } (fun _ => pure (.ok ())))
    .notFound "missing parent dir fails with .notFound"

  let busyRes ← withDb dbPath {} fun db1 => do
    assertOk (← exec db1 "BEGIN IMMEDIATE" #[]) "db1 BEGIN IMMEDIATE"
    if let .error e ← exec db1 "INSERT INTO parents(id, name) VALUES (?, ?)" #[.int 99, .text "lock"] then
      let _ ← exec db1 "ROLLBACK" #[]
      return .error e
    let innerBusy ← withDb dbPath { busyTimeoutMs := 20 } fun db2 =>
      exec db2 "BEGIN IMMEDIATE" #[]
    assertErrKind innerBusy .busy "second writer hits .busy after busyTimeoutMs expires"
    let _ ← exec db1 "ROLLBACK" #[]
    return .ok ()
  assertOk busyRes "busy contention test"

  let bodyErrRes ← withDb dbPath {} fun _ =>
    pure (Except.error { kind := .invalidInput, message := "caller error" } : Except SqliteError Unit)
  assertErrKind bodyErrRes .invalidInput "withDb propagates body error"
  assertTrue ((← activeDbCount) == 0 && (← activeStmtCount) == 0)
    "all DB and stmt handles closed on every error path"

private def testExceptionSafety (dbPath : String) : IO Unit := do
  let mut caught := false
  try
    let _ ← withDb dbPath {} fun db =>
      withTransaction db (α := Unit) fun txDb => do
        assertOk (← exec txDb "INSERT INTO parents(id, name) VALUES (?, ?)"
          #[.int 999, .text "thrown"]) "insert before thrown IO.Error"
        throw (IO.userError "simulated exception")
  catch e =>
    caught := (toString e).endsWith "simulated exception"
  assertTrue caught "IO.Error propagated from withDb/withTransaction"
  assertTrue ((← activeDbCount) == 0 && (← activeStmtCount) == 0)
    "handles closed cleanly when action throws IO.Error"
  let rows ← assertOk (← withDb dbPath { readOnly := true, createIfMissing := false } fun db =>
    query db "SELECT id, name FROM parents ORDER BY id" #[]) "verify rollback after thrown IO.Error"
  assertTrue (rows == #[#[.int 1, .text "root"], #[.int 2, .text "committed"]])
    s!"unexpected persisted rows after thrown IO.Error: {repr rows}"
  assertTrue ((← activeDbCount) == 0 && (← activeStmtCount) == 0) "handles clean after check"

/-- Real error-coverage test for `validateConfig` returning `.invalidInput`. -/
def err_sqlite_validateConfig_invalidInput : IO Unit := do
  assertErrKind (validateConfig { readOnly := true, createIfMissing := true }) .invalidInput "ro+create"
  assertErrKind (validateConfig { busyTimeoutMs := maxBusyTimeoutMs + 1 }) .invalidInput "timeout"

/-- Real error-coverage test for `withDb` returning `.notFound`. -/
def err_sqlite_withDb_notFound : IO Unit :=
  withTempErr fun tmp => do
    assertErrKind (← withDb (tmp ++ "/missing/app.db") { createIfMissing := false } (fun _ => pure (.ok ())))
      .notFound "withDb .notFound"

/-- Real error-coverage test for `withDb` returning `.busy`. -/
def err_sqlite_withDb_busy : IO Unit :=
  withTempErr fun tmp => do
    let p := tmp ++ "/busy.db"
    let r ← withDb p { walMode := false } fun db1 => do
      assertOk (← exec db1 "BEGIN EXCLUSIVE" #[]) "lock"
      let r2 ← withDb p { walMode := true, busyTimeoutMs := 0 } (fun _ => pure (.ok ()))
      let _ ← exec db1 "ROLLBACK" #[]
      return .ok r2
    assertErrKind (← assertOk r "outer") .busy "withDb .busy"

/-- Real error-coverage test for `withDb` returning `.constraint`. -/
def err_sqlite_withDb_constraint : IO Unit :=
  withTempErr fun tmp => do
    let r ← withDb (tmp ++ "/c.db") {} fun db => do
      if let .error e ← exec db "CREATE TABLE pk(id INTEGER PRIMARY KEY)" #[] then return .error e
      if let .error e ← exec db "INSERT INTO pk VALUES (1)" #[] then return .error e
      exec db "INSERT INTO pk VALUES (1)" #[]
    assertErrKind r .constraint "withDb .constraint"

/-- Real error-coverage test for `withDb` returning `.misuse`. -/
def err_sqlite_withDb_misuse : IO Unit :=
  withTempErr fun tmp => do
    let r ← withDb (tmp ++ "/m.db") {} fun db => exec db "SELECT 1; SELECT 2" #[]
    assertErrKind r .misuse "withDb .misuse"

/-- Real error-coverage test for `withDb` returning `.invalidInput`. -/
def err_sqlite_withDb_invalidInput : IO Unit := do
  assertErrKind (← withDb "" {} (fun _ => pure (.ok ()))) .invalidInput "withDb .invalidInput"

/-- Real error-coverage test for `withDb` returning `.ioError`. -/
def err_sqlite_withDb_ioError : IO Unit :=
  withTempErr fun tmp => do
    let p := tmp ++ "/corrupt.db"
    IO.FS.writeBinFile p (ByteArray.mk (Array.replicate 128 0xAA))
    assertErrKind (← withDb p { walMode := true } (fun _ => pure (.ok ())))
      .ioError "withDb .ioError"

/-- Real error-coverage test for `withTransaction` returning `.notFound`. -/
def err_sqlite_withTransaction_notFound : IO Unit :=
  withTempErr fun tmp => do
    let r ← withDb (tmp ++ "/tx.db") {} fun db =>
      withTransaction db fun _ =>
        withDb (tmp ++ "/missing/sub.db") { createIfMissing := false } (fun _ => pure (.ok ()))
    assertErrKind r .notFound "withTransaction .notFound"

/-- Real error-coverage test for `withTransaction` returning `.busy`. -/
def err_sqlite_withTransaction_busy : IO Unit :=
  withTempErr fun tmp => do
    let p := tmp ++ "/tx_busy.db"
    let r ← withDb p { walMode := false } fun db1 => do
      assertOk (← exec db1 "BEGIN EXCLUSIVE" #[]) "lock"
      let r2 ← withDb p { walMode := false, busyTimeoutMs := 0 } fun db2 =>
        withTransaction db2 (fun _ => pure (.ok ()))
      let _ ← exec db1 "ROLLBACK" #[]
      return .ok r2
    assertErrKind (← assertOk r "outer") .busy "withTransaction .busy"

/-- Real error-coverage test for `withTransaction` returning `.constraint`. -/
def err_sqlite_withTransaction_constraint : IO Unit :=
  withTempErr fun tmp => do
    let r ← withDb (tmp ++ "/tx_c.db") {} fun db => do
      if let .error e ← exec db "CREATE TABLE pk(id INTEGER PRIMARY KEY)" #[] then return .error e
      if let .error e ← exec db "INSERT INTO pk VALUES (1)" #[] then return .error e
      withTransaction db fun txDb => exec txDb "INSERT INTO pk VALUES (1)" #[]
    assertErrKind r .constraint "withTransaction .constraint"

/-- Real error-coverage test for `withTransaction` returning `.misuse`. -/
def err_sqlite_withTransaction_misuse : IO Unit :=
  withTempErr fun tmp => do
    let r ← withDb (tmp ++ "/tx_m.db") {} fun db =>
      withTransaction db fun txDb => exec txDb "SELECT 1; SELECT 2" #[]
    assertErrKind r .misuse "withTransaction .misuse"

/-- Real error-coverage test for `withTransaction` returning `.invalidInput`. -/
def err_sqlite_withTransaction_invalidInput : IO Unit :=
  withTempErr fun tmp => do
    let r ← withDb (tmp ++ "/tx_i.db") {} fun db =>
      withTransaction db fun txDb => exec txDb "SELECT ?" #[]
    assertErrKind r .invalidInput "withTransaction .invalidInput"

/-- Real error-coverage test for `withTransaction` returning `.ioError`. -/
def err_sqlite_withTransaction_ioError : IO Unit :=
  withTempErr fun tmp => do
    let r ← withDb (tmp ++ "/tx_io.db") {} fun db =>
      withTransaction db fun txDb =>
        query txDb "SELECT CAST(X'FFFE80' AS TEXT)" #[]
    assertErrKind r .ioError "withTransaction .ioError"

/-- Real error-coverage test for `exec` returning `.notFound`. -/
def err_sqlite_exec_notFound : IO Unit :=
  withTempErr fun tmp => do
    let r ← withDb ":memory:" {} fun db =>
      exec db "VACUUM INTO ?" #[.text (tmp ++ "/missing_dir/out.db")]
    assertErrKind r .notFound "exec .notFound"

/-- Real error-coverage test for `exec` returning `.busy`. -/
def err_sqlite_exec_busy : IO Unit :=
  withTempErr fun tmp => do
    let p := tmp ++ "/ex_busy.db"
    let r ← withDb p { walMode := false } fun db1 => do
      assertOk (← exec db1 "CREATE TABLE t(x INTEGER)" #[]) "create"
      assertOk (← exec db1 "BEGIN EXCLUSIVE" #[]) "lock"
      let r2 ← withDb p { walMode := false, busyTimeoutMs := 0 } fun db2 =>
        exec db2 "INSERT INTO t VALUES (1)" #[]
      let _ ← exec db1 "ROLLBACK" #[]
      return .ok r2
    assertErrKind (← assertOk r "outer") .busy "exec .busy"

/-- Real error-coverage test for `exec` returning `.constraint`. -/
def err_sqlite_exec_constraint : IO Unit := do
  let r ← withDb ":memory:" {} fun db => do
    if let .error e ← exec db "CREATE TABLE pk(id INTEGER PRIMARY KEY)" #[] then return .error e
    if let .error e ← exec db "INSERT INTO pk VALUES (1)" #[] then return .error e
    exec db "INSERT INTO pk VALUES (1)" #[]
  assertErrKind r .constraint "exec .constraint"

/-- Real error-coverage test for `exec` returning `.misuse`. -/
def err_sqlite_exec_misuse : IO Unit := do
  let r ← withDb ":memory:" {} fun db => exec db "SELECT 1; SELECT 2" #[]
  assertErrKind r .misuse "exec .misuse"

/-- Real error-coverage test for `exec` returning `.invalidInput`. -/
def err_sqlite_exec_invalidInput : IO Unit := do
  let r ← withDb ":memory:" {} fun db => exec db "SELECT ?" #[]
  assertErrKind r .invalidInput "exec .invalidInput"

/-- Real error-coverage test for `exec` returning `.ioError`. -/
def err_sqlite_exec_ioError : IO Unit :=
  withTempErr fun tmp => do
    let r ← withDb (tmp ++ "/ex_io.db") { walMode := false, foreignKeys := false } fun db => do
      if let .error e ← exec db "CREATE TABLE t(x INTEGER)" #[] then return .error e
      if let .error e ← exec db "PRAGMA query_only = ON" #[] then return .error e
      exec db "INSERT INTO t VALUES (1)" #[]
    assertErrKind r .ioError "exec .ioError"

/-- Real error-coverage test for `query` returning `.notFound`. -/
def err_sqlite_query_notFound : IO Unit :=
  withTempErr fun tmp => do
    let r ← withDb ":memory:" {} fun db =>
      query db "VACUUM INTO ?" #[.text (tmp ++ "/missing_dir/out.db")]
    assertErrKind r .notFound "query .notFound"

/-- Real error-coverage test for `query` returning `.busy`. -/
def err_sqlite_query_busy : IO Unit :=
  withTempErr fun tmp => do
    let p := tmp ++ "/q_busy.db"
    let r ← withDb p { walMode := false } fun db1 => do
      assertOk (← exec db1 "CREATE TABLE t(x INTEGER)" #[]) "create"
      assertOk (← exec db1 "BEGIN EXCLUSIVE" #[]) "lock"
      let r2 ← withDb p { walMode := false, busyTimeoutMs := 0 } fun db2 =>
        query db2 "INSERT INTO t VALUES (1)" #[]
      let _ ← exec db1 "ROLLBACK" #[]
      return .ok r2
    assertErrKind (← assertOk r "outer") .busy "query .busy"

/-- Real error-coverage test for `query` returning `.constraint`. -/
def err_sqlite_query_constraint : IO Unit := do
  let r ← withDb ":memory:" {} fun db => do
    if let .error e ← exec db "CREATE TABLE pk(id INTEGER PRIMARY KEY)" #[] then return .error e
    if let .error e ← exec db "INSERT INTO pk VALUES (1)" #[] then return .error e
    query db "INSERT INTO pk VALUES (1)" #[]
  assertErrKind r .constraint "query .constraint"

/-- Real error-coverage test for `query` returning `.misuse`. -/
def err_sqlite_query_misuse : IO Unit := do
  let r ← withDb ":memory:" {} fun db => query db "SELECT 1; SELECT 2" #[]
  assertErrKind r .misuse "query .misuse"

/-- Real error-coverage test for `query` returning `.invalidInput`. -/
def err_sqlite_query_invalidInput : IO Unit := do
  let r ← withDb ":memory:" {} fun db => query db "SELECT ?" #[]
  assertErrKind r .invalidInput "query .invalidInput"

/-- Real error-coverage test for `query` returning `.ioError`. -/
def err_sqlite_query_ioError : IO Unit := do
  let r ← withDb ":memory:" {} fun db => query db "SELECT CAST(X'FFFE80' AS TEXT)" #[]
  assertErrKind r .ioError "query .ioError"

/-- Real error-coverage test for `queryOne` returning `.notFound`. -/
def err_sqlite_queryOne_notFound : IO Unit :=
  withTempErr fun tmp => do
    let r ← withDb ":memory:" {} fun db =>
      queryOne db "VACUUM INTO ?" #[.text (tmp ++ "/missing_dir/out.db")]
    assertErrKind r .notFound "queryOne .notFound"

/-- Real error-coverage test for `queryOne` returning `.busy`. -/
def err_sqlite_queryOne_busy : IO Unit :=
  withTempErr fun tmp => do
    let p := tmp ++ "/q1_busy.db"
    let r ← withDb p { walMode := false } fun db1 => do
      assertOk (← exec db1 "CREATE TABLE t(x INTEGER)" #[]) "create"
      assertOk (← exec db1 "BEGIN EXCLUSIVE" #[]) "lock"
      let r2 ← withDb p { walMode := false, busyTimeoutMs := 0 } fun db2 =>
        queryOne db2 "INSERT INTO t VALUES (1)" #[]
      let _ ← exec db1 "ROLLBACK" #[]
      return .ok r2
    assertErrKind (← assertOk r "outer") .busy "queryOne .busy"

/-- Real error-coverage test for `queryOne` returning `.constraint`. -/
def err_sqlite_queryOne_constraint : IO Unit := do
  let r ← withDb ":memory:" {} fun db => do
    if let .error e ← exec db "CREATE TABLE pk(id INTEGER PRIMARY KEY)" #[] then return .error e
    if let .error e ← exec db "INSERT INTO pk VALUES (1)" #[] then return .error e
    queryOne db "INSERT INTO pk VALUES (1)" #[]
  assertErrKind r .constraint "queryOne .constraint"

/-- Real error-coverage test for `queryOne` returning `.misuse`. -/
def err_sqlite_queryOne_misuse : IO Unit := do
  let r ← withDb ":memory:" {} fun db => queryOne db "SELECT 1; SELECT 2" #[]
  assertErrKind r .misuse "queryOne .misuse"

/-- Real error-coverage test for `queryOne` returning `.invalidInput`. -/
def err_sqlite_queryOne_invalidInput : IO Unit := do
  let r ← withDb ":memory:" {} fun db => queryOne db "SELECT ?" #[]
  assertErrKind r .invalidInput "queryOne .invalidInput"

/-- Real error-coverage test for `queryOne` returning `.ioError`. -/
def err_sqlite_queryOne_ioError : IO Unit := do
  let r ← withDb ":memory:" {} fun db => queryOne db "SELECT CAST(X'FFFE80' AS TEXT)" #[]
  assertErrKind r .ioError "queryOne .ioError"

/-- Registered error-coverage tests for `LeanSwe.Sqlite`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  #[ { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_validateConfig_invalidInput"
       mode := .real, run := err_sqlite_validateConfig_invalidInput }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_withDb_notFound"
       mode := .real, run := err_sqlite_withDb_notFound }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_withDb_busy"
       mode := .real, run := err_sqlite_withDb_busy }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_withDb_constraint"
       mode := .real, run := err_sqlite_withDb_constraint }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_withDb_misuse"
       mode := .real, run := err_sqlite_withDb_misuse }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_withDb_invalidInput"
       mode := .real, run := err_sqlite_withDb_invalidInput }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_withDb_ioError"
       mode := .real, run := err_sqlite_withDb_ioError }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_withTransaction_notFound"
       mode := .real, run := err_sqlite_withTransaction_notFound }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_withTransaction_busy"
       mode := .real, run := err_sqlite_withTransaction_busy }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_withTransaction_constraint"
       mode := .real, run := err_sqlite_withTransaction_constraint }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_withTransaction_misuse"
       mode := .real, run := err_sqlite_withTransaction_misuse }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_withTransaction_invalidInput"
       mode := .real, run := err_sqlite_withTransaction_invalidInput }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_withTransaction_ioError"
       mode := .real, run := err_sqlite_withTransaction_ioError }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_exec_notFound"
       mode := .real, run := err_sqlite_exec_notFound }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_exec_busy"
       mode := .real, run := err_sqlite_exec_busy }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_exec_constraint"
       mode := .real, run := err_sqlite_exec_constraint }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_exec_misuse"
       mode := .real, run := err_sqlite_exec_misuse }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_exec_invalidInput"
       mode := .real, run := err_sqlite_exec_invalidInput }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_exec_ioError"
       mode := .real, run := err_sqlite_exec_ioError }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_query_notFound"
       mode := .real, run := err_sqlite_query_notFound }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_query_busy"
       mode := .real, run := err_sqlite_query_busy }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_query_constraint"
       mode := .real, run := err_sqlite_query_constraint }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_query_misuse"
       mode := .real, run := err_sqlite_query_misuse }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_query_invalidInput"
       mode := .real, run := err_sqlite_query_invalidInput }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_query_ioError"
       mode := .real, run := err_sqlite_query_ioError }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_queryOne_notFound"
       mode := .real, run := err_sqlite_queryOne_notFound }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_queryOne_busy"
       mode := .real, run := err_sqlite_queryOne_busy }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_queryOne_constraint"
       mode := .real, run := err_sqlite_queryOne_constraint }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_queryOne_misuse"
       mode := .real, run := err_sqlite_queryOne_misuse }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_queryOne_invalidInput"
       mode := .real, run := err_sqlite_queryOne_invalidInput }
   , { testName := "LeanSwe.Sqlite.RuntimeTests.err_sqlite_queryOne_ioError"
       mode := .real, run := err_sqlite_queryOne_ioError } ]

/-- Execute end-to-end runtime tests for `LeanSwe.Sqlite` over real SQLite files. -/
def runAll : IO Unit := do
  let res ← LeanSwe.TempDir.withTempDir none "lean-swe-sqlite-rt-" fun tmp => do
    let dbPath := tmp ++ "/app.sqlite3"
    testCrudWalFkAndBinding dbPath
    testTransactionsAndPersistence dbPath
    testErrorsAndBusyContention tmp dbPath
    testExceptionSafety dbPath
    return .ok ()
  match res with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"Sqlite RuntimeTests failed unexpectedly: {repr e}")
  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.Sqlite runtime tests"

end LeanSwe.Sqlite.RuntimeTests
