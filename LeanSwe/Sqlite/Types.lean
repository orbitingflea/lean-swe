namespace LeanSwe.Sqlite

/-- Classification of SQLite and configuration errors. -/
inductive SqliteErrorKind where
  /-- Database file or parent directory cannot be opened or found. -/
  | notFound
  /-- Database or table is locked and busy timeout expired (`SQLITE_BUSY` / `SQLITE_LOCKED`). -/
  | busy
  /-- Integrity constraint failed (`SQLITE_CONSTRAINT`). -/
  | constraint
  /-- Invalid API state or misused handle (`SQLITE_MISUSE`). -/
  | misuse
  /-- Invalid configuration, SQL, path, or parameter value. -/
  | invalidInput
  /-- Other SQLite or underlying I/O failure. -/
  | ioError
  deriving Repr, BEq, DecidableEq

/-- Typed SQLite error returned by `LeanSwe.Sqlite` operations. -/
structure SqliteError where
  /-- Machine-checkable error category. -/
  kind : SqliteErrorKind
  /-- Raw SQLite result code, when available. -/
  sqliteCode : Option UInt32 := none
  /-- Database path associated with the error, when available. -/
  path : Option String := none
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq

/-- Pure representation of raw SQLite C-shim error inputs for total error-mapping specs. -/
inductive SqliteRawError where
  /-- Unable to open database file (`SQLITE_CANTOPEN`). -/
  | cantOpen (path? : Option String) (code : UInt32) (detail : String)
  /-- Database or table locked (`SQLITE_BUSY` / `SQLITE_LOCKED`). -/
  | busy (code : UInt32) (detail : String)
  /-- Constraint violation (`SQLITE_CONSTRAINT`). -/
  | constraint (code : UInt32) (detail : String)
  /-- Library misuse (`SQLITE_MISUSE`). -/
  | misuse (code : UInt32) (detail : String)
  /-- Invalid caller argument or configuration. -/
  | invalidArgument (detail : String)
  /-- Underlying OS or SQLite I/O failure (`SQLITE_IOERR` / `SQLITE_FULL` / `SQLITE_CORRUPT` / etc.). -/
  | ioFailure (code : UInt32) (detail : String)
  /-- Generic numeric SQLite result code and diagnostic string. -/
  | sqliteCodeError (code : UInt32) (detail : String)
  /-- Generic user-constructed error string. -/
  | userError (detail : String)
  deriving Repr, BEq, DecidableEq

/-- Typed parameter and column value for injection-safe SQLite binding and row decoding. -/
inductive SqliteValue where
  /-- SQL `NULL`. -/
  | null
  /-- 64-bit signed SQLite `INTEGER`. -/
  | int (value : Int64)
  /-- 64-bit IEEE-754 SQLite `REAL`. -/
  | real (value : Float)
  /-- UTF-8 SQLite `TEXT`. -/
  | text (value : String)
  /-- Binary SQLite `BLOB`. -/
  | bytes (value : ByteArray)
  deriving BEq

instance : Repr SqliteValue where
  reprPrec v _ :=
    match v with
    | .null => "SqliteValue.null"
    | .int n => s!"SqliteValue.int {repr n}"
    | .real f => s!"SqliteValue.real {repr f}"
    | .text s => s!"SqliteValue.text {repr s}"
    | .bytes b => s!"SqliteValue.bytes {repr b.toList}"

/-- Single decoded result row returned by `query` and `queryOne`. -/
abbrev SqliteRow := Array SqliteValue

/-- Maximum `busyTimeoutMs` accepted by `sqlite3_busy_timeout` (signed 32-bit `int` max). -/
def maxBusyTimeoutMs : Nat := 2147483647

/-- Maximum UTF-8 SQL byte length accepted by `sqlite3_prepare_v2` (signed 32-bit `int` max). -/
def maxSqlByteLen : Nat := 2147483647

/-- `SQLITE_OPEN_READONLY` (`0x00000001`) flag for `sqlite3_open_v2`. -/
def sqliteOpenReadOnly : UInt32 := 0x00000001

/-- `SQLITE_OPEN_READWRITE` (`0x00000002`) flag for `sqlite3_open_v2`. -/
def sqliteOpenReadWrite : UInt32 := 0x00000002

/-- `SQLITE_OPEN_CREATE` (`0x00000004`) flag for `sqlite3_open_v2`. -/
def sqliteOpenCreate : UInt32 := 0x00000004

/-- `SQLITE_OPEN_URI` (`0x00000040`) flag enabling `file:` URI interpretation in `sqlite3_open_v2`. -/
def sqliteOpenUri : UInt32 := 0x00000040

/-- `SQLITE_OPEN_FULLMUTEX` (`0x00010000`) flag for serialized connection thread safety in `sqlite3_open_v2`. -/
def sqliteOpenFullMutex : UInt32 := 0x00010000

/-- Connection configuration passed to `openDb` and `withDb`. -/
structure OpenConfig where
  /-- Open database in read-only mode. -/
  readOnly : Bool := false
  /-- Create the database file if missing when opening read-write. -/
  createIfMissing : Bool := true
  /-- Milliseconds to wait on lock contention before returning `.busy`. -/
  busyTimeoutMs : Nat := 5000
  /-- Enable WAL journal mode on writable file-backed connections. -/
  walMode : Bool := true
  /-- Enforce foreign-key constraints (`PRAGMA foreign_keys = ON`). -/
  foreignKeys : Bool := true
  deriving Repr, BEq, DecidableEq

/-- Opaque handle identifier for an open SQLite database connection. -/
structure DbHandle where
  /-- Unique handle identifier assigned by the backend. -/
  id : UInt64
  deriving Repr, BEq, DecidableEq

/-- Opaque handle identifier for a prepared SQLite statement. -/
structure StmtHandle where
  /-- Unique statement identifier assigned by the backend. -/
  id : UInt64
  /-- Owning database handle identifier. -/
  dbId : UInt64
  deriving Repr, BEq, DecidableEq

/-- Result of advancing a prepared statement by one step. -/
inductive StepResult where
  /-- A decoded result row (`SQLITE_ROW`). -/
  | row (columns : Array SqliteValue)
  /-- Statement execution completed (`SQLITE_DONE`). -/
  | done
  deriving Repr, BEq

private opaque RawDbHandlePointed : NonemptyType

/-- Opaque C `lean_external_object` wrapping a `sqlite3*` pointer with a per-handle mutex and `in_use`/`closed` guard. -/
def RawDbHandle : Type := RawDbHandlePointed.type

instance : Nonempty RawDbHandle := RawDbHandlePointed.property

private opaque RawStmtHandlePointed : NonemptyType

/-- Opaque C `lean_external_object` wrapping a `sqlite3_stmt*` pointer with a per-handle mutex and `in_use`/`closed` guard. -/
def RawStmtHandle : Type := RawStmtHandlePointed.type

instance : Nonempty RawStmtHandle := RawStmtHandlePointed.property

/-- Pure Lean registry mapping public `DbHandle` / `StmtHandle` identifiers to backend handles `(dbH, stmtH)`. -/
structure RawHandleTable (dbH stmtH : Type) where
  /-- Next monotonic database handle identifier (`1`-based). -/
  nextDbId : UInt64 := 1
  /-- Next monotonic statement handle identifier (`1`-based). -/
  nextStmtId : UInt64 := 1
  /-- Currently open `(dbId, rawDb)` entries. -/
  dbs : List (UInt64 × dbH) := []
  /-- Currently active `(stmtHandle, rawStmt)` entries. -/
  stmts : List (StmtHandle × stmtH) := []
  deriving Inhabited

/-- Outcome of a single thin `sqlite3_step` call before column decoding. -/
inductive RawStepTag where
  /-- `SQLITE_DONE` (`101`) indicating statement execution completed. -/
  | done
  /-- `SQLITE_ROW` (`100`) indicating a result row is ready for `column*` reads. -/
  | row
  deriving Repr, BEq, DecidableEq

/-- Outcome of a single thin `sqlite3_finalize` call on a raw statement handle. -/
inductive RawFinalizeResult where
  /-- `sqlite3_finalize` ran and destroyed the underlying `sqlite3_stmt*`, returning `none` on `SQLITE_OK`
      or `some stickyErr` when the preceding `sqlite3_step` failed. -/
  | finalized (stickyError? : Option SqliteRawError := none)
  /-- Handle was invalid, already finalized, or concurrently pinned (`in_use > 0`), so `sqlite3_finalize` did not run. -/
  | rejected (err : SqliteRawError)
  deriving Repr, BEq, DecidableEq

/-- Thin 1-call `sqlite3_*` C boundary hooks plus atomic Lean handle-table state access over effect monad `m`
    and raw handle types `(dbH, stmtH)`. -/
structure CSqliteOpsM (m : Type → Type) (dbH stmtH : Type) where
  /-- Atomically update the Lean-managed `RawHandleTable` and return a projected value. -/
  modifyTable : {α : Type} → (RawHandleTable dbH stmtH → α × RawHandleTable dbH stmtH) → m α
  /-- Thin wrapper around `sqlite3_open_v2(path, &db, flags, NULL)`. -/
  openV2 : String → UInt32 → m (Except SqliteRawError dbH)
  /-- Thin wrapper around `sqlite3_close(db)` returning `SQLITE_BUSY` on unfinalized statements or `in_use > 0`, and `SQLITE_MISUSE` when closed. -/
  close : dbH → m (Except SqliteRawError Unit)
  /-- Thin wrapper around `sqlite3_extended_result_codes(db, onoff)`. -/
  extendedResultCodes : dbH → Bool → m (Except SqliteRawError Unit)
  /-- Thin wrapper around `sqlite3_busy_timeout(db, ms)`. -/
  busyTimeout : dbH → UInt32 → m (Except SqliteRawError Unit)
  /-- Thin wrapper around `sqlite3_prepare_v2(db, sql, byteLen, &stmt, &tail)` returning `(stmt?, consumedByteLen)`. -/
  prepareV2 : dbH → String → m (Except SqliteRawError (Option stmtH × Nat))
  /-- Thin wrapper around `sqlite3_step(stmt)` returning `.done` or `.row`. -/
  step : stmtH → m (Except SqliteRawError RawStepTag)
  /-- Thin wrapper around `sqlite3_reset(stmt)`. -/
  reset : stmtH → m (Except SqliteRawError Unit)
  /-- Thin wrapper around `sqlite3_clear_bindings(stmt)`. -/
  clearBindings : stmtH → m (Except SqliteRawError Unit)
  /-- Thin wrapper around `sqlite3_finalize(stmt)` distinguishing statement destruction (`.finalized`) from pin/closed refusal (`.rejected`). -/
  finalize : stmtH → m RawFinalizeResult
  /-- Thin wrapper around `sqlite3_bind_parameter_count(stmt)`. -/
  bindParamCount : stmtH → m (Except SqliteRawError UInt32)
  /-- Thin wrapper around `sqlite3_bind_null(stmt, idx)`. -/
  bindNull : stmtH → UInt32 → m (Except SqliteRawError Unit)
  /-- Thin wrapper around `sqlite3_bind_int64(stmt, idx, val)`. -/
  bindInt64 : stmtH → UInt32 → Int64 → m (Except SqliteRawError Unit)
  /-- Thin wrapper around `sqlite3_bind_double(stmt, idx, val)`. -/
  bindDouble : stmtH → UInt32 → Float → m (Except SqliteRawError Unit)
  /-- Thin wrapper around `sqlite3_bind_text64(stmt, idx, ptr, len, SQLITE_TRANSIENT, SQLITE_UTF8)`. -/
  bindText : stmtH → UInt32 → String → m (Except SqliteRawError Unit)
  /-- Thin wrapper around `sqlite3_bind_blob64(stmt, idx, ptr, len, SQLITE_TRANSIENT)`. -/
  bindBlob : stmtH → UInt32 → ByteArray → m (Except SqliteRawError Unit)
  /-- Thin wrapper around `sqlite3_column_count(stmt)` returning `SQLITE_MISUSE` on closed/invalid handles. -/
  columnCount : stmtH → m (Except SqliteRawError UInt32)
  /-- Thin wrapper around `sqlite3_column_type(stmt, col)` returning `SQLITE_MISUSE` on closed/invalid handles. -/
  columnType : stmtH → UInt32 → m (Except SqliteRawError UInt32)
  /-- Thin wrapper around `sqlite3_column_int64(stmt, col)` returning `SQLITE_MISUSE` on closed/invalid handles. -/
  columnInt64 : stmtH → UInt32 → m (Except SqliteRawError Int64)
  /-- Thin wrapper around `sqlite3_column_double(stmt, col)` returning `SQLITE_MISUSE` on closed/invalid handles. -/
  columnDouble : stmtH → UInt32 → m (Except SqliteRawError Float)
  /-- Thin wrapper around `sqlite3_column_text(stmt, col)` + `sqlite3_column_bytes(stmt, col)` copying raw UTF-8
      column bytes without C UTF-8 validation and returning `SQLITE_MISUSE` on closed/invalid handles. -/
  columnTextBytes : stmtH → UInt32 → m (Except SqliteRawError ByteArray)
  /-- Thin wrapper around `sqlite3_column_blob(stmt, col)` + `sqlite3_column_bytes(stmt, col)` copying raw binary
      column bytes and returning `SQLITE_MISUSE` on closed/invalid handles. -/
  columnBlob : stmtH → UInt32 → m (Except SqliteRawError ByteArray)
  /-- Acquire the per-statement lock for `stmt`, returning `true` when `stmt` was active and locked. -/
  lockStmt : [Pure m] → StmtHandle → m Bool := fun _ => pure false
  /-- Release a previously acquired per-statement lock for `stmt`. -/
  unlockStmt : [Pure m] → StmtHandle → m Unit := fun _ => pure ()

/-- Concrete `IO` thin-C SQLite hooks backed by `c/sqlite_shim.c`. -/
abbrev CSqliteOps := CSqliteOpsM IO RawDbHandle RawStmtHandle

/-- Minimal single-step SQLite primitives parameterized over effect monad `m`. -/
structure RawSqliteOpsM (m : Type → Type) where
  /-- Convert a raw SQLite error record into a normalized `SqliteError` with non-empty message. -/
  mapRawError : SqliteRawError → SqliteError
  /-- Open a SQLite connection at `path` with `cfg`. -/
  openDb : String → OpenConfig → m (Except SqliteError DbHandle)
  /-- Close an open SQLite connection handle. -/
  closeDb : DbHandle → m (Except SqliteError Unit)
  /-- Prepare a single SQL statement on `db`. -/
  prepare : DbHandle → String → m (Except SqliteError StmtHandle)
  /-- Bind typed parameters to a prepared statement (`1`-indexed in SQLite). -/
  bind : StmtHandle → Array SqliteValue → m (Except SqliteError Unit)
  /-- Execute one step of a prepared statement. -/
  step : StmtHandle → m (Except SqliteError StepResult)
  /-- Finalize and release a prepared statement handle. -/
  finalize : StmtHandle → m (Except SqliteError Unit)
  /-- Return the number of currently open database handles. -/
  activeDbCount : m Nat
  /-- Return the number of currently active prepared statement handles. -/
  activeStmtCount : m Nat

/-- Concrete `IO` single-step SQLite API bundle. -/
abbrev RawSqliteOps := RawSqliteOpsM IO

/-- Public high-level operations exported by `LeanSwe.Sqlite`, parameterized over effect monad `m`. -/
structure SqliteApiM (m : Type → Type) where
  /-- Convert a raw SQLite error record into a normalized `SqliteError` with non-empty message. -/
  mapRawError : SqliteRawError → SqliteError
  /-- Validate an `OpenConfig` before opening a connection. -/
  validateConfig : OpenConfig → Except SqliteError Unit
  /-- Open a connection, run `action`, and always close the handle on both `.ok` and `.error`. -/
  withDb : {α : Type} → String → OpenConfig → (DbHandle → m (Except SqliteError α)) → m (Except SqliteError α)
  /-- Execute `action` inside an all-or-nothing transaction, committing on `.ok` and rolling back on `.error`. -/
  withTransaction : {α : Type} → DbHandle → (DbHandle → m (Except SqliteError α)) → m (Except SqliteError α)
  /-- Execute a parameterized SQL statement to completion without returning rows. -/
  exec : DbHandle → String → Array SqliteValue → m (Except SqliteError Unit)
  /-- Execute a parameterized SQL query and collect all result rows. -/
  query : DbHandle → String → Array SqliteValue → m (Except SqliteError (Array SqliteRow))
  /-- Execute a parameterized SQL query and return the first row, or `none` if empty. -/
  queryOne : DbHandle → String → Array SqliteValue → m (Except SqliteError (Option SqliteRow))
  /-- Return the number of currently open database handles. -/
  activeDbCount : m Nat
  /-- Return the number of currently active prepared statement handles. -/
  activeStmtCount : m Nat

/-- Concrete `IO` SQLite API bundle for `LeanSwe.Sqlite`. -/
abbrev SqliteApi := SqliteApiM IO

end LeanSwe.Sqlite
