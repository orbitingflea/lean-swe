import LeanSwe.Sqlite.Raw.Interface
import LeanSwe.TempDir.Interface

namespace LeanSwe.Sqlite.Raw.RuntimeTests

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

/-- Execute primitive SQLite C-shim grounding tests for `LeanSwe.Sqlite.Raw`. -/
def runAll : IO Unit := do
  let res ← LeanSwe.TempDir.withTempDir none "lean-swe-sqlite-raw-rt-" fun tmp => do
    let dbBefore ← Raw.activeDbCount
    let stmtBefore ← Raw.activeStmtCount
    assertTrue (dbBefore == 0 && stmtBefore == 0) "initial handle counts zero"

    let missingPath := tmp ++ "/missing_dir/absent.db"
    assertErrKind (← Raw.openDb missingPath { createIfMissing := false }) .notFound
      "openDb missing parent fails with .notFound"
    assertTrue ((← Raw.activeDbCount) == 0) "activeDbCount unchanged after failed openDb"

    let dbPath := tmp ++ "/raw_test.db"
    let db ← assertOk (← Raw.openDb dbPath {}) "openDb creates file"
    assertTrue ((← Raw.activeDbCount) == 1) "activeDbCount increments to 1"

    let stCreate ← assertOk
      (← Raw.prepare db "CREATE TABLE kv(k INTEGER PRIMARY KEY, t TEXT, r REAL, b BLOB, n TEXT)")
      "prepare CREATE TABLE"
    assertTrue ((← Raw.activeStmtCount) == 1) "activeStmtCount increments to 1"
    let stepCreate ← assertOk (← Raw.step stCreate) "step CREATE TABLE"
    assertTrue (stepCreate == .done) "CREATE TABLE step done"
    assertOk (← Raw.finalize stCreate) "finalize CREATE TABLE"
    assertTrue ((← Raw.activeStmtCount) == 0) "activeStmtCount returns to 0"

    assertErrKind (← Raw.prepare db "SELECT 1; DROP TABLE kv;") .misuse
      "prepare rejects multi-statement SQL"
    assertTrue ((← Raw.activeStmtCount) == 0) "activeStmtCount unchanged after rejected prepare"

    let stIns ← assertOk (← Raw.prepare db "INSERT INTO kv(k, t, r, b, n) VALUES (?, ?, ?, ?, ?)")
      "prepare INSERT"
    let blob := ByteArray.mk #[0, 1, 255]
    assertOk (← Raw.bind stIns #[.int 7, .text "hello", .real 3.5, .bytes blob, .null])
      "bind all 5 SqliteValue variants"
    let stepIns ← assertOk (← Raw.step stIns) "step INSERT"
    assertTrue (stepIns == .done) "INSERT step done"
    assertOk (← Raw.finalize stIns) "finalize INSERT"

    let stDup ← assertOk (← Raw.prepare db "INSERT INTO kv(k, t, r, b, n) VALUES (?, ?, ?, ?, ?)")
      "prepare duplicate INSERT"
    assertOk (← Raw.bind stDup #[.int 7, .text "dup", .real 1.0, .bytes ByteArray.empty, .null])
      "bind duplicate INSERT"
    assertErrKind (← Raw.step stDup) .constraint "duplicate PRIMARY KEY yields .constraint"
    let _ ← Raw.finalize stDup
    assertTrue ((← Raw.activeStmtCount) == 0) "activeStmtCount zero after constraint finalize"

    let stSel ← assertOk (← Raw.prepare db "SELECT k, t, r, b, n FROM kv WHERE k = ?")
      "prepare SELECT"
    assertOk (← Raw.bind stSel #[.int 7]) "bind SELECT param"
    let rowStep ← assertOk (← Raw.step stSel) "step SELECT row"
    match rowStep with
    | .done => throw (IO.userError "ASSERTION FAILED: expected row, got done")
    | .row cols =>
      assertTrue (cols == #[.int 7, .text "hello", .real 3.5, .bytes blob, .null])
        s!"unexpected decoded columns: {repr cols}"
    let doneStep ← assertOk (← Raw.step stSel) "step SELECT done"
    assertTrue (doneStep == .done) "second step yields done"
    assertOk (← Raw.finalize stSel) "finalize SELECT"
    assertTrue ((← Raw.activeStmtCount) == 0) "activeStmtCount returns to 0"

    assertOk (← Raw.closeDb db) "closeDb"
    assertErrKind (← Raw.closeDb db) .misuse "double closeDb yields .misuse"
    assertTrue ((← Raw.activeDbCount) == 0 && (← Raw.activeStmtCount) == 0)
      "all handles cleaned up"
    return .ok ()
  match res with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"Sqlite.Raw RuntimeTests failed unexpectedly: {repr e}")
  IO.println "PASS: LeanSwe.Sqlite.Raw runtime tests"

end LeanSwe.Sqlite.Raw.RuntimeTests
