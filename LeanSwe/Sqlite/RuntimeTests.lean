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
  IO.println "PASS: LeanSwe.Sqlite runtime tests"

end LeanSwe.Sqlite.RuntimeTests
