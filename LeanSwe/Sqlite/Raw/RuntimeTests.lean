import Core.Assumptions
import LeanSwe.Sqlite.Raw.Interface
import LeanSwe.Sqlite.Raw.Impl
import LeanSwe.Sqlite.Raw.SpecTests
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

private def withTempRawErr (action : String → IO Unit) : IO Unit := do
  let wrap ← LeanSwe.TempDir.withTempDir none "lean-swe-sqlite-raw-rt-" fun tmp => do
    action tmp
    return .ok ()
  match wrap with
  | .error te => throw (IO.userError s!"TempDir failed: {repr te}")
  | .ok () => pure ()

private def execOne (db : Raw.DbHandle) (sql : String) : IO Unit := do
  let st ← assertOk (← Raw.prepare db sql) s!"prepare {sql}"
  let stepRes ← Raw.step st
  let finRes ← Raw.finalize st
  let _ ← assertOk stepRes s!"step {sql}"
  assertOk finRes s!"finalize {sql}"

private def runMockWithFail {α : Type} (failStep : MockCFailStep) (s0 : MockCState)
    (act : RawSqliteOpsM (StateM MockCState) → StateM MockCState (Except SqliteError α)) :
    Except SqliteError α :=
  let ops := Raw.Internal.mkRawOps mockCOps
  let s : MockCState := { s0 with failStep := failStep }
  (act ops).run s |>.1

/-- Runtime check for `LeanSwe.Sqlite.Raw.assume_sqliteraw_openV2_honorsFlagsAndMemoryUri`. -/
def assume_sqliteraw_openV2_honorsFlagsAndMemoryUri : IO Unit :=
  withTempRawErr fun tmp => do
    let diskPath := tmp ++ "/flags.db"
    let db ← assertOk (← Raw.openDb diskPath { readOnly := false, createIfMissing := true }) "openDb create"
    execOne db "CREATE TABLE t(v INTEGER)"
    execOne db "INSERT INTO t VALUES (42)"
    assertOk (← Raw.closeDb db) "close writable"

    let dbRo ← assertOk (← Raw.openDb diskPath { readOnly := true, createIfMissing := false }) "openDb ro"
    let stIns ← assertOk (← Raw.prepare dbRo "INSERT INTO t VALUES (99)") "prepare ro write"
    assertErrKind (← Raw.step stIns) .ioError "readOnly open rejects writes with .ioError"
    let _ ← Raw.finalize stIns
    let stSel ← assertOk (← Raw.prepare dbRo "SELECT v FROM t") "prepare ro read"
    let row ← assertOk (← Raw.step stSel) "step ro read"
    assertTrue (row == .row #[.int 42]) "readOnly open sees existing data"
    assertOk (← Raw.finalize stSel) "finalize ro read"
    assertOk (← Raw.closeDb dbRo) "close ro"

    assertErrKind (← Raw.openDb (tmp ++ "/absent.db") { createIfMissing := false }) .notFound
      "missing db with createIfMissing=false yields .notFound"

    let memUri := "file:" ++ tmp ++ "/should_not_create.db?mode=memory"
    let dbMem ← assertOk (← Raw.openDb memUri {}) "openDb memory URI"
    execOne dbMem "CREATE TABLE m(x INTEGER)"
    assertOk (← Raw.closeDb dbMem) "close memory URI"
    let fileExists ← System.FilePath.pathExists (tmp ++ "/should_not_create.db")
    assertTrue (!fileExists) "mode=memory URI does not create on-disk file"
    assertTrue ((← Raw.activeDbCount) == 0 && (← Raw.activeStmtCount) == 0) "handles zero"

/-- Runtime check for `LeanSwe.Sqlite.Raw.assume_sqliteraw_close_releasesDbAndRejectsClosedOrPinnedHandle`. -/
def assume_sqliteraw_close_releasesDbAndRejectsClosedOrPinnedHandle : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  let st ← assertOk (← Raw.prepare db "SELECT 1") "prepare pinned stmt"
  assertErrKind (← Raw.closeDb db) .busy "closeDb rejects pinned handle with .busy"
  assertOk (← Raw.finalize st) "finalize pinned stmt"
  assertOk (← Raw.closeDb db) "closeDb succeeds after finalize"
  assertErrKind (← Raw.closeDb db) .misuse "closeDb rejects closed handle with .misuse"
  assertTrue ((← Raw.activeDbCount) == 0 && (← Raw.activeStmtCount) == 0) "handles zero"

/-- Runtime check for `LeanSwe.Sqlite.Raw.assume_sqliteraw_prepareV2_returnsConsumedPrefixByteLen`. -/
def assume_sqliteraw_prepareV2_returnsConsumedPrefixByteLen : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  let st ← assertOk (← Raw.prepare db "SELECT 1; -- trailing comment\n /* block */ ")
    "prepare single stmt with trailing comments"
  let row ← assertOk (← Raw.step st) "step single stmt"
  assertTrue (row == .row #[.int 1]) "single stmt returned 1"
  assertOk (← Raw.finalize st) "finalize single stmt"

  assertErrKind (← Raw.prepare db "SELECT 1; SELECT 2") .misuse "reject two statements"
  assertErrKind (← Raw.prepare db "SELECT 1; /* unclosed") .misuse "reject unclosed comment"
  assertErrKind (← Raw.prepare db "  \t\n ") .misuse "reject empty SQL"
  assertTrue ((← Raw.activeStmtCount) == 0) "stmt count zero after rejected prepares"
  assertOk (← Raw.closeDb db) "closeDb"

/-- Runtime check for `LeanSwe.Sqlite.Raw.assume_sqliteraw_bind_roundTripsAllFiveValueTypes`. -/
def assume_sqliteraw_bind_roundTripsAllFiveValueTypes : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  execOne db "CREATE TABLE vals(a INTEGER, b REAL, c TEXT, d BLOB, e TEXT)"
  let stIns ← assertOk (← Raw.prepare db "INSERT INTO vals(a, b, c, d, e) VALUES (?, ?, ?, ?, ?)")
    "prepare insert"
  assertErrKind (← Raw.bind stIns #[.int 1]) .invalidInput "bind count mismatch yields .invalidInput"
  let blob := ByteArray.mk #[0, 127, 255]
  let vals : Array SqliteValue := #[.int (-42), .real 3.25, .text "hello-λ", .bytes blob, .null]
  assertOk (← Raw.bind stIns vals) "bind 5 types"
  let stepInsRes ← assertOk (← Raw.step stIns) "step insert"
  assertTrue (stepInsRes == .done) "insert done"
  assertOk (← Raw.finalize stIns) "finalize insert"

  let stSel ← assertOk (← Raw.prepare db "SELECT a, b, c, d, e FROM vals") "prepare select"
  let row ← assertOk (← Raw.step stSel) "step select"
  assertTrue (row == .row vals) s!"roundtrip mismatch: {repr row}"
  assertOk (← Raw.finalize stSel) "finalize select"
  assertOk (← Raw.closeDb db) "closeDb"

/-- Runtime check for `LeanSwe.Sqlite.Raw.assume_sqliteraw_step_reportsRowAndDoneAccurately`. -/
def assume_sqliteraw_step_reportsRowAndDoneAccurately : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  let st ← assertOk (← Raw.prepare db "SELECT 1 UNION ALL SELECT 2 ORDER BY 1") "prepare union"
  assertTrue ((← assertOk (← Raw.step st) "step 1") == .row #[.int 1]) "row 1"
  assertTrue ((← assertOk (← Raw.step st) "step 2") == .row #[.int 2]) "row 2"
  assertTrue ((← assertOk (← Raw.step st) "step 3") == .done) "done"
  assertOk (← Raw.finalize st) "finalize"
  assertOk (← Raw.closeDb db) "closeDb"

/-- Runtime check for `LeanSwe.Sqlite.Raw.assume_sqliteraw_columns_preserveRawBytesAndRejectClosedStmt`. -/
def assume_sqliteraw_columns_preserveRawBytesAndRejectClosedStmt : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  let stBlob ← assertOk (← Raw.prepare db "SELECT CAST(X'FFFE80' AS BLOB)") "prepare blob"
  let rBlob ← assertOk (← Raw.step stBlob) "step blob"
  assertTrue (rBlob == .row #[.bytes (ByteArray.mk #[0xFF, 0xFE, 0x80])]) "blob preserves invalid UTF-8"
  assertOk (← Raw.finalize stBlob) "finalize blob"
  assertErrKind (← Raw.step stBlob) .misuse "step rejects finalized stmt"

  let stText ← assertOk (← Raw.prepare db "SELECT CAST(X'FFFE80' AS TEXT)") "prepare bad text"
  match ← Raw.step stText with
  | .ok _ => throw (IO.userError "expected .ioError for invalid UTF-8 TEXT column")
  | .error e =>
    assertTrue (e.kind == .ioError && e.sqliteCode == none && e.message != "")
      s!"unexpected error for bad UTF-8 TEXT: {repr e}"
  let _ ← Raw.finalize stText
  assertOk (← Raw.closeDb db) "closeDb"

  let db16 ← assertOk (← Raw.openDb ":memory:" {}) "open UTF-16le :memory:"
  execOne db16 "PRAGMA encoding = 'UTF-16le'"
  execOne db16 "CREATE TABLE t16(s TEXT)"
  let stIns16 ← assertOk (← Raw.prepare db16 "INSERT INTO t16 VALUES (?)") "prepare utf16 insert"
  assertOk (← Raw.bind stIns16 #[.text "hello-λ-Ω"]) "bind utf16 text"
  assertTrue ((← assertOk (← Raw.step stIns16) "step utf16 insert") == .done) "utf16 insert done"
  assertOk (← Raw.finalize stIns16) "finalize utf16 insert"
  let stSel16 ← assertOk (← Raw.prepare db16 "SELECT s FROM t16") "prepare utf16 select"
  assertTrue ((← assertOk (← Raw.step stSel16) "step utf16 select") == .row #[.text "hello-λ-Ω"])
    "UTF-16le TEXT roundtrip preserves UTF-8"
  assertOk (← Raw.finalize stSel16) "finalize utf16 select"
  assertOk (← Raw.closeDb db16) "closeDb UTF-16le"

/-- Runtime check for `LeanSwe.Sqlite.Raw.assume_sqliteraw_finalize_destroysStmtEvenOnStickyStepError`. -/
def assume_sqliteraw_finalize_destroysStmtEvenOnStickyStepError : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  execOne db "CREATE TABLE pk(id INTEGER PRIMARY KEY)"
  execOne db "INSERT INTO pk VALUES (1)"
  let stDup ← assertOk (← Raw.prepare db "INSERT INTO pk VALUES (1)") "prepare dup"
  assertErrKind (← Raw.step stDup) .constraint "step dup yields .constraint"
  assertErrKind (← Raw.finalize stDup) .constraint "finalize returns sticky .constraint"
  assertTrue ((← Raw.activeStmtCount) == 0) "stmt destroyed despite sticky error"
  assertErrKind (← Raw.finalize stDup) .misuse "double finalize rejected with .misuse"
  assertOk (← Raw.closeDb db) "closeDb succeeds after sticky finalize"

/-- Real error-coverage test for `openDb` returning `.notFound`. -/
def err_sqliteraw_openDb_notFound : IO Unit :=
  withTempRawErr fun tmp => do
    assertErrKind (← Raw.openDb (tmp ++ "/missing_parent/db.sqlite") { createIfMissing := false })
      .notFound "openDb missing parent"

/-- Real error-coverage test for `openDb` returning `.busy`. -/
def err_sqliteraw_openDb_busy : IO Unit :=
  withTempRawErr fun tmp => do
    let dbPath := tmp ++ "/busy_open.db"
    let db1 ← assertOk (← Raw.openDb dbPath { walMode := false }) "open db1"
    execOne db1 "BEGIN EXCLUSIVE"
    assertErrKind (← Raw.openDb dbPath { walMode := true, busyTimeoutMs := 0 }) .busy
      "openDb WAL upgrade hits .busy under exclusive lock"
    execOne db1 "ROLLBACK"
    assertOk (← Raw.closeDb db1) "close db1"

/-- Mocked error-coverage test for `openDb` returning `.constraint`. -/
def err_sqliteraw_openDb_constraint : IO Unit := do
  let res := runMockWithFail (.openV2 (.constraint 19 "mock open constraint")) {}
    (fun ops => ops.openDb "app.db" {})
  assertErrKind res .constraint "mocked openDb .constraint"

/-- Mocked error-coverage test for `openDb` returning `.misuse`. -/
def err_sqliteraw_openDb_misuse : IO Unit := do
  let res := runMockWithFail (.openV2 (.misuse 21 "mock open misuse")) {}
    (fun ops => ops.openDb "app.db" {})
  assertErrKind res .misuse "mocked openDb .misuse"

/-- Real error-coverage test for `openDb` returning `.invalidInput`. -/
def err_sqliteraw_openDb_invalidInput : IO Unit := do
  assertErrKind (← Raw.openDb "" {}) .invalidInput "empty path"
  assertErrKind (← Raw.openDb "a.db" { readOnly := true, createIfMissing := true }) .invalidInput
    "ro + create"

/-- Real error-coverage test for `openDb` returning `.ioError`. -/
def err_sqliteraw_openDb_ioError : IO Unit :=
  withTempRawErr fun tmp => do
    let bad := tmp ++ "/corrupt.db"
    IO.FS.writeBinFile bad (ByteArray.mk (Array.replicate 128 0xAA))
    match ← Raw.openDb bad { walMode := true } with
    | .ok db =>
      let _ ← Raw.closeDb db
      throw (IO.userError "ASSERTION FAILED: corrupt db header hits .ioError during setup (got ok)")
    | .error e =>
      assertErrKind (.error e : Except SqliteError DbHandle) .ioError
        "corrupt db header hits .ioError during setup"

/-- Mocked error-coverage test for `closeDb` returning `.notFound`. -/
def err_sqliteraw_closeDb_notFound : IO Unit := do
  let res := runMockWithFail (.close (.cantOpen (some "x.db") 14 "mock close notFound")) mockStateWithOpenDb
    (fun ops => ops.closeDb { id := 1 })
  assertErrKind res .notFound "mocked closeDb .notFound"

/-- Real error-coverage test for `closeDb` returning `.busy`. -/
def err_sqliteraw_closeDb_busy : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  let st ← assertOk (← Raw.prepare db "SELECT 1") "prepare"
  assertErrKind (← Raw.closeDb db) .busy "closeDb with active stmt"
  assertOk (← Raw.finalize st) "finalize"
  assertOk (← Raw.closeDb db) "closeDb"

/-- Mocked error-coverage test for `closeDb` returning `.constraint`. -/
def err_sqliteraw_closeDb_constraint : IO Unit := do
  let res := runMockWithFail (.close (.constraint 19 "mock close constraint")) mockStateWithOpenDb
    (fun ops => ops.closeDb { id := 1 })
  assertErrKind res .constraint "mocked closeDb .constraint"

/-- Real error-coverage test for `closeDb` returning `.misuse`. -/
def err_sqliteraw_closeDb_misuse : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  assertOk (← Raw.closeDb db) "closeDb"
  assertErrKind (← Raw.closeDb db) .misuse "double closeDb"

/-- Mocked error-coverage test for `closeDb` returning `.invalidInput`. -/
def err_sqliteraw_closeDb_invalidInput : IO Unit := do
  let res := runMockWithFail (.close (.invalidArgument "mock close invalidInput")) mockStateWithOpenDb
    (fun ops => ops.closeDb { id := 1 })
  assertErrKind res .invalidInput "mocked closeDb .invalidInput"

/-- Mocked error-coverage test for `closeDb` returning `.ioError`. -/
def err_sqliteraw_closeDb_ioError : IO Unit := do
  let res := runMockWithFail (.close (.ioFailure 10 "mock close ioError")) mockStateWithOpenDb
    (fun ops => ops.closeDb { id := 1 })
  assertErrKind res .ioError "mocked closeDb .ioError"

/-- Mocked error-coverage test for `prepare` returning `.notFound`. -/
def err_sqliteraw_prepare_notFound : IO Unit := do
  let res := runMockWithFail (.prepareV2At 0 (.cantOpen none 14 "mock prepare notFound")) mockStateWithOpenDb
    (fun ops => ops.prepare { id := 1 } "SELECT 1")
  assertErrKind res .notFound "mocked prepare .notFound"

/-- Real error-coverage test for `prepare` returning `.busy`. -/
def err_sqliteraw_prepare_busy : IO Unit :=
  withTempRawErr fun tmp => do
    let dbPath := tmp ++ "/busy_prep.db"
    let db1 ← assertOk (← Raw.openDb dbPath { walMode := false }) "open db1"
    execOne db1 "CREATE TABLE t(x INTEGER)"
    execOne db1 "BEGIN EXCLUSIVE"
    let db2 ← assertOk (← Raw.openDb dbPath { walMode := false, foreignKeys := false, busyTimeoutMs := 0 })
      "open db2"
    assertErrKind (← Raw.prepare db2 "SELECT * FROM t") .busy "prepare under exclusive lock hits .busy"
    assertOk (← Raw.closeDb db2) "close db2"
    execOne db1 "ROLLBACK"
    assertOk (← Raw.closeDb db1) "close db1"

/-- Mocked error-coverage test for `prepare` returning `.constraint`. -/
def err_sqliteraw_prepare_constraint : IO Unit := do
  let res := runMockWithFail (.prepareV2At 0 (.constraint 19 "mock prepare constraint")) mockStateWithOpenDb
    (fun ops => ops.prepare { id := 1 } "SELECT 1")
  assertErrKind res .constraint "mocked prepare .constraint"

/-- Real error-coverage test for `prepare` returning `.misuse`. -/
def err_sqliteraw_prepare_misuse : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  assertErrKind (← Raw.prepare db "SELECT 1; SELECT 2") .misuse "multi-stmt prepare"
  assertOk (← Raw.closeDb db) "closeDb"
  assertErrKind (← Raw.prepare db "SELECT 1") .misuse "prepare on closed db"

/-- Real error-coverage test for `prepare` returning `.invalidInput`. -/
def err_sqliteraw_prepare_invalidInput : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  let nulSql := "SELECT " ++ String.ofList [Char.ofNat 0] ++ "1"
  assertErrKind (← Raw.prepare db nulSql) .invalidInput "prepare with NUL byte"
  assertOk (← Raw.closeDb db) "closeDb"

/-- Real error-coverage test for `prepare` returning `.ioError`. -/
def err_sqliteraw_prepare_ioError : IO Unit :=
  withTempRawErr fun tmp => do
    let bad := tmp ++ "/corrupt_prep.db"
    IO.FS.writeBinFile bad (ByteArray.mk (Array.replicate 128 0xAA))
    let db ← assertOk (← Raw.openDb bad { walMode := false, foreignKeys := false }) "open corrupt lazily"
    assertErrKind (← Raw.prepare db "SELECT * FROM sqlite_master") .ioError "prepare corrupt db hits .ioError"
    assertOk (← Raw.closeDb db) "closeDb"

/-- Real error-coverage test for `bind` returning `.notFound`. -/
def err_sqliteraw_bind_notFound : IO Unit :=
  withTempRawErr fun tmp => do
    let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
    let st ← assertOk (← Raw.prepare db "VACUUM INTO ?") "prepare vacuum"
    assertOk (← Raw.bind st #[.text (tmp ++ "/missing_dir/out.db")]) "bind missing dir"
    assertErrKind (← Raw.step st) .notFound "step vacuum fails .notFound"
    assertErrKind (← Raw.bind st #[.text (tmp ++ "/other.db")]) .notFound "bind reset exposes sticky .notFound"
    let _ ← Raw.finalize st
    assertOk (← Raw.closeDb db) "closeDb"

/-- Real error-coverage test for `bind` returning `.busy`. -/
def err_sqliteraw_bind_busy : IO Unit :=
  withTempRawErr fun tmp => do
    let dbPath := tmp ++ "/busy_bind.db"
    let db1 ← assertOk (← Raw.openDb dbPath { walMode := false }) "open db1"
    execOne db1 "CREATE TABLE t(x INTEGER)"
    let db2 ← assertOk (← Raw.openDb dbPath { walMode := false, busyTimeoutMs := 0 }) "open db2"
    let st ← assertOk (← Raw.prepare db2 "INSERT INTO t VALUES (?)") "prepare insert"
    execOne db1 "BEGIN EXCLUSIVE"
    assertOk (← Raw.bind st #[.int 1]) "bind 1"
    assertErrKind (← Raw.step st) .busy "step hits .busy"
    assertErrKind (← Raw.bind st #[.int 2]) .busy "bind reset exposes sticky .busy"
    let _ ← Raw.finalize st
    assertOk (← Raw.closeDb db2) "close db2"
    execOne db1 "ROLLBACK"
    assertOk (← Raw.closeDb db1) "close db1"

/-- Real error-coverage test for `bind` returning `.constraint`. -/
def err_sqliteraw_bind_constraint : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  execOne db "CREATE TABLE pk(id INTEGER PRIMARY KEY)"
  execOne db "INSERT INTO pk VALUES (1)"
  let st ← assertOk (← Raw.prepare db "INSERT INTO pk VALUES (?)") "prepare insert"
  assertOk (← Raw.bind st #[.int 1]) "bind 1"
  assertErrKind (← Raw.step st) .constraint "step hits .constraint"
  assertErrKind (← Raw.bind st #[.int 2]) .constraint "bind reset exposes sticky .constraint"
  let _ ← Raw.finalize st
  assertOk (← Raw.closeDb db) "closeDb"

/-- Real error-coverage test for `bind` returning `.misuse`. -/
def err_sqliteraw_bind_misuse : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  let st ← assertOk (← Raw.prepare db "SELECT ?") "prepare"
  assertOk (← Raw.finalize st) "finalize"
  assertErrKind (← Raw.bind st #[.int 1]) .misuse "bind finalized stmt"
  assertOk (← Raw.closeDb db) "closeDb"

/-- Real error-coverage test for `bind` returning `.invalidInput`. -/
def err_sqliteraw_bind_invalidInput : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  let st ← assertOk (← Raw.prepare db "SELECT ?") "prepare"
  assertErrKind (← Raw.bind st #[]) .invalidInput "bind count mismatch"
  assertOk (← Raw.finalize st) "finalize"
  assertOk (← Raw.closeDb db) "closeDb"

/-- Real error-coverage test for `bind` returning `.ioError`. -/
def err_sqliteraw_bind_ioError : IO Unit :=
  withTempRawErr fun tmp => do
    let dbPath := tmp ++ "/ro_bind.db"
    let db ← assertOk (← Raw.openDb dbPath { walMode := false, foreignKeys := false }) "open"
    execOne db "CREATE TABLE t(x INTEGER)"
    execOne db "PRAGMA query_only = ON"
    let st ← assertOk (← Raw.prepare db "INSERT INTO t VALUES (?)") "prepare"
    assertOk (← Raw.bind st #[.int 1]) "bind"
    assertErrKind (← Raw.step st) .ioError "step query_only insert hits .ioError"
    assertErrKind (← Raw.bind st #[.int 2]) .ioError "bind reset exposes sticky .ioError"
    let _ ← Raw.finalize st
    assertOk (← Raw.closeDb db) "closeDb"

/-- Real error-coverage test for `step` returning `.notFound`. -/
def err_sqliteraw_step_notFound : IO Unit :=
  withTempRawErr fun tmp => do
    let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
    let st ← assertOk (← Raw.prepare db "VACUUM INTO ?") "prepare vacuum"
    assertOk (← Raw.bind st #[.text (tmp ++ "/missing_dir/out.db")]) "bind"
    assertErrKind (← Raw.step st) .notFound "step vacuum fails .notFound"
    let _ ← Raw.finalize st
    assertOk (← Raw.closeDb db) "closeDb"

/-- Real error-coverage test for `step` returning `.busy`. -/
def err_sqliteraw_step_busy : IO Unit :=
  withTempRawErr fun tmp => do
    let dbPath := tmp ++ "/busy_step.db"
    let db1 ← assertOk (← Raw.openDb dbPath { walMode := false }) "open db1"
    execOne db1 "CREATE TABLE t(x INTEGER)"
    let db2 ← assertOk (← Raw.openDb dbPath { walMode := false, busyTimeoutMs := 0 }) "open db2"
    let st ← assertOk (← Raw.prepare db2 "INSERT INTO t VALUES (1)") "prepare"
    execOne db1 "BEGIN EXCLUSIVE"
    assertErrKind (← Raw.step st) .busy "step hits .busy"
    let _ ← Raw.finalize st
    assertOk (← Raw.closeDb db2) "close db2"
    execOne db1 "ROLLBACK"
    assertOk (← Raw.closeDb db1) "close db1"

/-- Real error-coverage test for `step` returning `.constraint`. -/
def err_sqliteraw_step_constraint : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  execOne db "CREATE TABLE pk(id INTEGER PRIMARY KEY)"
  execOne db "INSERT INTO pk VALUES (1)"
  let st ← assertOk (← Raw.prepare db "INSERT INTO pk VALUES (1)") "prepare dup"
  assertErrKind (← Raw.step st) .constraint "step dup"
  let _ ← Raw.finalize st
  assertOk (← Raw.closeDb db) "closeDb"

/-- Real error-coverage test for `step` returning `.misuse`. -/
def err_sqliteraw_step_misuse : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  let st ← assertOk (← Raw.prepare db "SELECT 1") "prepare"
  assertOk (← Raw.finalize st) "finalize"
  assertErrKind (← Raw.step st) .misuse "step finalized stmt"
  assertOk (← Raw.closeDb db) "closeDb"

/-- Mocked error-coverage test for `step` returning `.invalidInput`. -/
def err_sqliteraw_step_invalidInput : IO Unit := do
  let res := runMockWithFail (.stepAt 0 (.invalidArgument "mock step invalidInput")) (mockStateWithOpenStmt 0)
    (fun ops => ops.step { id := 1, dbId := 1 })
  assertErrKind res .invalidInput "mocked step .invalidInput"

/-- Real error-coverage test for `step` returning `.ioError`. -/
def err_sqliteraw_step_ioError : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  let st ← assertOk (← Raw.prepare db "SELECT CAST(X'FFFE80' AS TEXT)") "prepare invalid utf8"
  assertErrKind (← Raw.step st) .ioError "step invalid utf8"
  let _ ← Raw.finalize st
  assertOk (← Raw.closeDb db) "closeDb"

/-- Real error-coverage test for `finalize` returning `.notFound`. -/
def err_sqliteraw_finalize_notFound : IO Unit :=
  withTempRawErr fun tmp => do
    let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
    let st ← assertOk (← Raw.prepare db "VACUUM INTO ?") "prepare vacuum"
    assertOk (← Raw.bind st #[.text (tmp ++ "/missing_dir/out.db")]) "bind"
    assertErrKind (← Raw.step st) .notFound "step"
    assertErrKind (← Raw.finalize st) .notFound "finalize sticky .notFound"
    assertOk (← Raw.closeDb db) "closeDb"

/-- Real error-coverage test for `finalize` returning `.busy`. -/
def err_sqliteraw_finalize_busy : IO Unit :=
  withTempRawErr fun tmp => do
    let dbPath := tmp ++ "/busy_fin.db"
    let db1 ← assertOk (← Raw.openDb dbPath { walMode := false }) "open db1"
    execOne db1 "CREATE TABLE t(x INTEGER)"
    let db2 ← assertOk (← Raw.openDb dbPath { walMode := false, busyTimeoutMs := 0 }) "open db2"
    let st ← assertOk (← Raw.prepare db2 "INSERT INTO t VALUES (1)") "prepare"
    execOne db1 "BEGIN EXCLUSIVE"
    assertErrKind (← Raw.step st) .busy "step"
    assertErrKind (← Raw.finalize st) .busy "finalize sticky .busy"
    assertOk (← Raw.closeDb db2) "close db2"
    execOne db1 "ROLLBACK"
    assertOk (← Raw.closeDb db1) "close db1"

/-- Real error-coverage test for `finalize` returning `.constraint`. -/
def err_sqliteraw_finalize_constraint : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  execOne db "CREATE TABLE pk(id INTEGER PRIMARY KEY)"
  execOne db "INSERT INTO pk VALUES (1)"
  let st ← assertOk (← Raw.prepare db "INSERT INTO pk VALUES (1)") "prepare"
  assertErrKind (← Raw.step st) .constraint "step"
  assertErrKind (← Raw.finalize st) .constraint "finalize sticky .constraint"
  assertOk (← Raw.closeDb db) "closeDb"

/-- Real error-coverage test for `finalize` returning `.misuse`. -/
def err_sqliteraw_finalize_misuse : IO Unit := do
  let db ← assertOk (← Raw.openDb ":memory:" {}) "open :memory:"
  let st ← assertOk (← Raw.prepare db "SELECT 1") "prepare"
  assertOk (← Raw.finalize st) "finalize 1"
  assertErrKind (← Raw.finalize st) .misuse "double finalize"
  assertOk (← Raw.closeDb db) "closeDb"

/-- Mocked error-coverage test for `finalize` returning `.invalidInput`. -/
def err_sqliteraw_finalize_invalidInput : IO Unit := do
  let res := runMockWithFail
    (.finalizeResult (.finalized (some (.invalidArgument "mock finalize invalidInput"))))
    (mockStateWithOpenStmt 0)
    (fun ops => ops.finalize { id := 1, dbId := 1 })
  assertErrKind res .invalidInput "mocked finalize .invalidInput"

/-- Real error-coverage test for `finalize` returning `.ioError`. -/
def err_sqliteraw_finalize_ioError : IO Unit :=
  withTempRawErr fun tmp => do
    let dbPath := tmp ++ "/ro_fin.db"
    let db ← assertOk (← Raw.openDb dbPath { walMode := false, foreignKeys := false }) "open"
    execOne db "CREATE TABLE t(x INTEGER)"
    execOne db "PRAGMA query_only = ON"
    let st ← assertOk (← Raw.prepare db "INSERT INTO t VALUES (1)") "prepare"
    assertErrKind (← Raw.step st) .ioError "step"
    assertErrKind (← Raw.finalize st) .ioError "finalize sticky .ioError"
    assertOk (← Raw.closeDb db) "closeDb"

/-- Registered external-world assumption checks for `LeanSwe.Sqlite.Raw`. -/
def registeredAssumptions : Array Core.RegisteredAssumption :=
  #[ { specName := "LeanSwe.Sqlite.Raw.assume_sqliteraw_openV2_honorsFlagsAndMemoryUri"
       run := assume_sqliteraw_openV2_honorsFlagsAndMemoryUri }
   , { specName := "LeanSwe.Sqlite.Raw.assume_sqliteraw_close_releasesDbAndRejectsClosedOrPinnedHandle"
       run := assume_sqliteraw_close_releasesDbAndRejectsClosedOrPinnedHandle }
   , { specName := "LeanSwe.Sqlite.Raw.assume_sqliteraw_prepareV2_returnsConsumedPrefixByteLen"
       run := assume_sqliteraw_prepareV2_returnsConsumedPrefixByteLen }
   , { specName := "LeanSwe.Sqlite.Raw.assume_sqliteraw_bind_roundTripsAllFiveValueTypes"
       run := assume_sqliteraw_bind_roundTripsAllFiveValueTypes }
   , { specName := "LeanSwe.Sqlite.Raw.assume_sqliteraw_step_reportsRowAndDoneAccurately"
       run := assume_sqliteraw_step_reportsRowAndDoneAccurately }
   , { specName := "LeanSwe.Sqlite.Raw.assume_sqliteraw_columns_preserveRawBytesAndRejectClosedStmt"
       run := assume_sqliteraw_columns_preserveRawBytesAndRejectClosedStmt }
   , { specName := "LeanSwe.Sqlite.Raw.assume_sqliteraw_finalize_destroysStmtEvenOnStickyStepError"
       run := assume_sqliteraw_finalize_destroysStmtEvenOnStickyStepError } ]

/-- Registered error-coverage tests for `LeanSwe.Sqlite.Raw`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  #[ { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_openDb_notFound"
       mode := .real, run := err_sqliteraw_openDb_notFound }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_openDb_busy"
       mode := .real, run := err_sqliteraw_openDb_busy }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_openDb_constraint"
       mode := .mocked, run := err_sqliteraw_openDb_constraint }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_openDb_misuse"
       mode := .mocked, run := err_sqliteraw_openDb_misuse }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_openDb_invalidInput"
       mode := .real, run := err_sqliteraw_openDb_invalidInput }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_openDb_ioError"
       mode := .real, run := err_sqliteraw_openDb_ioError }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_closeDb_notFound"
       mode := .mocked, run := err_sqliteraw_closeDb_notFound }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_closeDb_busy"
       mode := .real, run := err_sqliteraw_closeDb_busy }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_closeDb_constraint"
       mode := .mocked, run := err_sqliteraw_closeDb_constraint }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_closeDb_misuse"
       mode := .real, run := err_sqliteraw_closeDb_misuse }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_closeDb_invalidInput"
       mode := .mocked, run := err_sqliteraw_closeDb_invalidInput }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_closeDb_ioError"
       mode := .mocked, run := err_sqliteraw_closeDb_ioError }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_prepare_notFound"
       mode := .mocked, run := err_sqliteraw_prepare_notFound }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_prepare_busy"
       mode := .real, run := err_sqliteraw_prepare_busy }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_prepare_constraint"
       mode := .mocked, run := err_sqliteraw_prepare_constraint }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_prepare_misuse"
       mode := .real, run := err_sqliteraw_prepare_misuse }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_prepare_invalidInput"
       mode := .real, run := err_sqliteraw_prepare_invalidInput }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_prepare_ioError"
       mode := .real, run := err_sqliteraw_prepare_ioError }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_bind_notFound"
       mode := .real, run := err_sqliteraw_bind_notFound }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_bind_busy"
       mode := .real, run := err_sqliteraw_bind_busy }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_bind_constraint"
       mode := .real, run := err_sqliteraw_bind_constraint }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_bind_misuse"
       mode := .real, run := err_sqliteraw_bind_misuse }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_bind_invalidInput"
       mode := .real, run := err_sqliteraw_bind_invalidInput }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_bind_ioError"
       mode := .real, run := err_sqliteraw_bind_ioError }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_step_notFound"
       mode := .real, run := err_sqliteraw_step_notFound }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_step_busy"
       mode := .real, run := err_sqliteraw_step_busy }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_step_constraint"
       mode := .real, run := err_sqliteraw_step_constraint }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_step_misuse"
       mode := .real, run := err_sqliteraw_step_misuse }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_step_invalidInput"
       mode := .mocked, run := err_sqliteraw_step_invalidInput }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_step_ioError"
       mode := .real, run := err_sqliteraw_step_ioError }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_finalize_notFound"
       mode := .real, run := err_sqliteraw_finalize_notFound }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_finalize_busy"
       mode := .real, run := err_sqliteraw_finalize_busy }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_finalize_constraint"
       mode := .real, run := err_sqliteraw_finalize_constraint }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_finalize_misuse"
       mode := .real, run := err_sqliteraw_finalize_misuse }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_finalize_invalidInput"
       mode := .mocked, run := err_sqliteraw_finalize_invalidInput }
   , { testName := "LeanSwe.Sqlite.Raw.RuntimeTests.err_sqliteraw_finalize_ioError"
       mode := .real, run := err_sqliteraw_finalize_ioError } ]

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
  Core.runRegisteredAssumptions registeredAssumptions
  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.Sqlite.Raw runtime tests"

end LeanSwe.Sqlite.Raw.RuntimeTests
