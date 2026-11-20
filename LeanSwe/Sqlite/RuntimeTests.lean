import Core.Assumptions
import LeanSwe.Sqlite.Impl
import LeanSwe.Sqlite.Interface
import LeanSwe.Sqlite.Model
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

    let zeroBlob? ← assertOk (← queryOne db "SELECT X'', ?" #[.bytes ByteArray.empty])
      "queryOne empty blob"
    assertTrue (zeroBlob? == some #[.bytes ByteArray.empty, .bytes ByteArray.empty])
      s!"empty blob decoded as null/wrong value: {repr zeroBlob?}"

    let negZero := -0.0
    let negZero? ← assertOk (← queryOne db "SELECT ?" #[.real negZero])
      "queryOne negative zero"
    let negZeroOk := match negZero? with
      | some #[.real r] => r.toBits == negZero.toBits
      | _ => false
    assertTrue negZeroOk s!"negative zero roundtrip bit mismatch: {repr negZero?}"
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

private def testImplErrorPrecedenceAndRelationalModel : IO Unit := do
  let mkMockOps (stepFn : String → Except SqliteError Raw.StepResult)
      (finFn : String → Except SqliteError Unit)
      (closeFn : DbHandle → Except SqliteError Unit := fun _ => .ok ()) :
      RawSqliteOpsM (StateM (Array (UInt64 × String))) :=
    { mapRawError := Model.mapRawError
      openDb := fun _ _ => pure (.ok { id := 1 })
      closeDb := fun db => pure (closeFn db)
      prepare := fun _ sql => modifyGet fun log =>
        let sid := UInt64.ofNat (log.size + 1)
        (.ok { id := sid, dbId := 1 }, log.push (sid, sql))
      bind := fun _ _ => pure (.ok ())
      step := fun sh => do
        let log ← get
        let sql := ((log.find? fun p => p.1 == sh.id).map (·.2)).getD ""
        pure (stepFn sql)
      finalize := fun sh => do
        let log ← get
        let sql := ((log.find? fun p => p.1 == sh.id).map (·.2)).getD ""
        pure (finFn sql)
      activeDbCount := pure 0
      activeStmtCount := pure 0 }

  let apiStepOverFin := Internal.mkApiM (mkMockOps
    (fun _ => .error { kind := .constraint, sqliteCode := some 2067, message := "primary step err" })
    (fun _ => .error { kind := .ioError, sqliteCode := some 999, message := "secondary fin err" }))
  let (rExecPrec, _) := (apiStepOverFin.exec { id := 1 } "SELECT 1" #[]).run #[]
  assertTrue (match rExecPrec with | .error e => e.sqliteCode == some 2067 | .ok _ => false)
    s!"execOp must preserve primary step error over finalize error: {repr rExecPrec}"

  let apiFinErr := Internal.mkApiM (mkMockOps
    (fun sql => if sql == "SELECT 2" then .ok (.row #[.int 2]) else .ok .done)
    (fun _ => .error { kind := .ioError, sqliteCode := some 777, message := "finalize failed" }))
  let (rQueryFin, _) := (apiFinErr.query { id := 1 } "SELECT 1" #[]).run #[]
  assertTrue (match rQueryFin with | .error e => e.sqliteCode == some 777 | .ok _ => false)
    s!"queryOp must propagate finalize error: {repr rQueryFin}"
  let (rQueryOneFin, _) := (apiFinErr.queryOne { id := 1 } "SELECT 2" #[]).run #[]
  assertTrue (match rQueryOneFin with | .error e => e.sqliteCode == some 777 | .ok _ => false)
    s!"queryOneOp must propagate finalize error: {repr rQueryOneFin}"

  let apiCloseErr := Internal.mkApiM (mkMockOps
    (fun _ => .ok .done) (fun _ => .ok ())
    (fun _ => .error { kind := .busy, sqliteCode := some 5, message := "close busy" }))
  let (rWithDbClose, _) := (apiCloseErr.withDb ":memory:" {} fun _ => pure (.ok (42 : Nat))).run #[]
  assertTrue (match rWithDbClose with | .error e => e.kind == .busy && e.sqliteCode == some 5 | .ok _ => false)
    s!"withDbOp must propagate closeDb error on action ok: {repr rWithDbClose}"
  let (rWithDbActionErr, _) := (apiCloseErr.withDb ":memory:" {} fun _ =>
    pure (.error { kind := .constraint, sqliteCode := some 19, message := "action err" } : Except SqliteError Nat)).run #[]
  assertTrue (match rWithDbActionErr with | .error e => e.kind == .constraint && e.sqliteCode == some 19 | .ok _ => false)
    s!"withDbOp must preserve primary action error over closeDb error: {repr rWithDbActionErr}"

  let apiCommitFail := Internal.mkApiM (mkMockOps
    (fun sql =>
      if sql == "COMMIT" then .error { kind := .busy, sqliteCode := some 5, message := "commit busy" }
      else .ok .done)
    (fun _ => .ok ()))
  let (rCommitRbOk, logCommitRbOk) := (apiCommitFail.withTransaction { id := 1 } fun _ => pure (.ok ())).run #[]
  assertTrue ((match rCommitRbOk with | .error e => e.sqliteCode == some 5 | .ok _ => false) &&
    logCommitRbOk.map (·.2) == #["BEGIN IMMEDIATE", "COMMIT", "ROLLBACK"])
    s!"withTransactionOp must run ROLLBACK on COMMIT failure: res={repr rCommitRbOk} log={repr logCommitRbOk}"

  let apiCommitAndRbFail := Internal.mkApiM (mkMockOps
    (fun sql =>
      if sql == "COMMIT" then .error { kind := .busy, sqliteCode := some 5, message := "commit busy" }
      else if sql == "ROLLBACK" then .error { kind := .ioError, sqliteCode := some 516, message := "rb err" }
      else .ok .done)
    (fun _ => .ok ()))
  let (rCommitRbErr, _) := (apiCommitAndRbFail.withTransaction { id := 1 } fun _ => pure (.ok ())).run #[]
  assertTrue (match rCommitRbErr with | .error e => e.sqliteCode == some 5 | .ok _ => false)
    s!"withTransactionOp must preserve COMMIT error over ROLLBACK error: {repr rCommitRbErr}"

  let apiBodyAndRbFail := Internal.mkApiM (mkMockOps
    (fun sql =>
      if sql == "ROLLBACK" then .error { kind := .ioError, sqliteCode := some 516, message := "rb err" }
      else .ok .done)
    (fun _ => .ok ()))
  let (rBodyRbErr, _) := (apiBodyAndRbFail.withTransaction { id := 1 } fun _ =>
    pure (.error { kind := .busy, sqliteCode := some 5, message := "body err" } : Except SqliteError Unit)).run #[]
  assertTrue (match rBodyRbErr with | .error e => e.sqliteCode == some 5 | .ok _ => false)
    s!"withTransactionOp must preserve action error over ROLLBACK error: {repr rBodyRbErr}"

  assertTrue (Model.allowedSelectRows {} "BEGIN" #[] #[] &&
    Model.allowedSelectRows {} "COMMIT" #[] #[] &&
    Model.allowedQueryOneRow {} "ROLLBACK" #[] none)
    "allowedSelectRows and allowedQueryOneRow must accept empty result on transaction control SQL"

  let (.ok mdb, st0) := (Model.modelRawOps.openDb ":memory:" { walMode := false, foreignKeys := false }).run {}
    | throw (IO.userError "model openDb failed")
  let (.ok (), st1) := (Model.modelApi.exec mdb "CREATE TABLE t(id INTEGER PRIMARY KEY, x ANY) STRICT" #[]).run st0
    | throw (IO.userError "model CREATE TABLE failed")
  let (.ok (), st2) := (Model.modelApi.exec mdb "INSERT INTO t VALUES (1, ?)" #[.real 1.0]).run st1
    | throw (IO.userError "model INSERT 1 failed")
  let (.ok (), st3) := (Model.modelApi.exec mdb "INSERT INTO t VALUES (2, ?)" #[.real (-0.0)]).run st2
    | throw (IO.userError "model INSERT 2 failed")
  let (.ok ms, st4) := (Model.modelRawOps.prepare mdb "SELECT id, x FROM t").run st3
    | throw (IO.userError "model prepare failed")
  let (.ok (), st5) := (Model.modelRawOps.bind ms #[]).run st4
    | throw (IO.userError "model bind failed")
  let (_, some st6) := Model.stepRawRelational ms (.ok (.row #[.int 1, .real 1.0])) st5
    | throw (IO.userError "stepRawRelational step1 failed")
  let (.ok (), st7) := (Model.modelApi.exec mdb "UPDATE t SET x = ? WHERE id = 2" #[.real 0.0]).run st6
    | throw (IO.userError "model UPDATE +0.0 failed")
  let (_, stPosZero?) := Model.stepRawRelational ms (.ok (.row #[.int 2, .real 0.0])) st7
  let (_, stStaleNegZero?) := Model.stepRawRelational ms (.ok (.row #[.int 2, .real (-0.0)])) st7
  assertTrue (stPosZero?.isSome && stStaleNegZero?.isNone)
    "stepRawRelational must distinguish +0.0 from -0.0 across mid-scan UPDATE"

  let (.ok mdb2, u0) := (Model.modelRawOps.openDb ":memory:" { walMode := false, foreignKeys := false }).run {}
    | throw (IO.userError "model openDb 2 failed")
  let (.ok (), u1) := (Model.modelApi.exec mdb2 "CREATE TABLE u(id INTEGER PRIMARY KEY, k INT, ucol INT UNIQUE)" #[]).run u0
    | throw (IO.userError "model CREATE u failed")
  let mut uSt := u1
  for i in [1:18] do
    let idV := Int64.ofInt (Int.ofNat i)
    let uV := Int64.ofInt (Int.ofNat (18 - i))
    let (.ok (), uNext) := (Model.modelApi.exec mdb2 "INSERT INTO u VALUES (?, 0, ?)" #[.int idV, .int uV]).run uSt
      | throw (IO.userError "model INSERT u failed")
    uSt := uNext
  let (.ok us, uPrep) := (Model.modelRawOps.prepare mdb2 "SELECT k FROM u WHERE ucol > 0").run uSt
    | throw (IO.userError "model prepare u failed")
  let (.ok (), uBind) := (Model.modelRawOps.bind us #[]).run uPrep
    | throw (IO.userError "model bind u failed")
  let (_, some uStep1) := Model.stepRawRelational us (.ok (.row #[.int 0])) uBind
    | throw (IO.userError "stepRawRelational 17-row step1 failed")
  let (.ok (), uAfterDel) := (Model.modelApi.exec mdb2 "DELETE FROM u WHERE id <= 16" #[]).run uStep1
    | throw (IO.userError "model DELETE u failed")
  let (_, uDone?) := Model.stepRawRelational us (.ok .done) uAfterDel
  assertTrue uDone?.isSome "stepRawRelational must accept .done after 17th-row index visit and mid-scan DELETE"

  let pad := String.ofList (List.replicate (Model.maxCuratedSqlBytes + 16) ' ')
  let bigStrSql := pad ++ "SELECT 'a  b'"
  let (bigStrRes, _) := (Model.modelApi.query mdb2 bigStrSql #[]).run uAfterDel
  assertTrue (match bigStrRes with | .ok #[#[.text "a  b"]] => true | _ => false)
    s!"oversized SQL must preserve spaces in string literal: {repr bigStrRes}"
  let bigCmtSql := pad ++ "-- line comment\nSELECT 2"
  let (bigCmtRes, _) := (Model.modelApi.query mdb2 bigCmtSql #[]).run uAfterDel
  assertTrue (match bigCmtRes with | .ok #[#[.int 2]] => true | _ => false)
    s!"oversized SQL must preserve newline terminating line comment: {repr bigCmtRes}"

  let (.ok mdb3, r0) := (Model.modelRawOps.openDb ":memory:" { walMode := false, foreignKeys := false }).run {}
    | throw (IO.userError "model openDb 3 failed")
  let (.ok (), r1) := (Model.modelApi.exec mdb3 "CREATE TABLE rw(id INTEGER PRIMARY KEY, x TEXT)" #[]).run r0
    | throw (IO.userError "model CREATE rw failed")
  let (_, some r2) := Model.stepInsertRelational r1 mdb3 "INSERT INTO rw(id, x) VALUES (NULL, 'a')" #[] [#[.int (-999), .text "a"]]
    | throw (IO.userError "relational auto-rowid must accept arbitrary unused Int64 (-999)")
  let (_, badNegExp?) := Model.stepInsertRelational r2 mdb3 "INSERT INTO rw(id, x) VALUES (10, 'b')" #[] [#[.int (-999), .text "a"], #[.int 99, .text "b"]]
  assertTrue badNegExp?.isNone "relational insert must reject mismatch on explicit INTEGER PRIMARY KEY"
  let (_, some r3) := Model.stepInsertRelational r2 mdb3 "INSERT INTO rw(id, x) VALUES (10, 'b')" #[] [#[.int (-999), .text "a"], #[.int 10, .text "b"]]
    | throw (IO.userError "relational insert must accept exact explicit INTEGER PRIMARY KEY 10")
  let (_, badNonIpk?) := Model.stepInsertRelational r3 mdb3 "INSERT INTO rw(id, x) VALUES (NULL, 'c')" #[] [#[.int (-999), .text "a"], #[.int 10, .text "b"], #[.int 42, .text "wrong"]]
  assertTrue badNonIpk?.isNone "relational insert must reject non-rowid column mismatch"
  let (.ok (), ra1) := (Model.modelApi.exec mdb3 "CREATE TABLE rwa(id INTEGER PRIMARY KEY AUTOINCREMENT, x TEXT)" #[]).run r3
    | throw (IO.userError "model CREATE rwa failed")
  let (.ok (), ra2) := (Model.modelApi.exec mdb3 "INSERT INTO rwa(id, x) VALUES (10, 'p')" #[]).run ra1
    | throw (IO.userError "model INSERT rwa explicit 10 failed")
  let (_, badMono?) := Model.stepInsertRelational ra2 mdb3 "INSERT INTO rwa(id, x) VALUES (NULL, 'q')" #[] [#[.int 9, .text "q"], #[.int 10, .text "p"]]
  assertTrue badMono?.isNone "relational AUTOINCREMENT must reject auto-rowid <= maxAutoRowid"
  let (_, some ra3) := Model.stepInsertRelational ra2 mdb3 "INSERT INTO rwa(id, x) VALUES (NULL, 'q')" #[] [#[.int 10, .text "p"], #[.int 42, .text "q"]]
    | throw (IO.userError "relational AUTOINCREMENT must accept auto-rowid > maxAutoRowid")
  let (.ok (), ra4) := (Model.modelApi.exec mdb3 "INSERT INTO rwa(id, x) VALUES (9223372036854775807, 'top')" #[]).run ra3
    | throw (IO.userError "model INSERT rwa maxValue failed")
  let (raFull, _) := (Model.modelApi.exec mdb3 "INSERT INTO rwa(id, x) VALUES (NULL, 'full')" #[]).run ra4
  assertTrue (match raFull with | .error e => e.sqliteCode == some 13 | _ => false)
    "AUTOINCREMENT after Int64.maxValue must fail with SQLITE_FULL (13)"

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
  testImplErrorPrecedenceAndRelationalModel
  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.Sqlite runtime tests"

end LeanSwe.Sqlite.RuntimeTests
