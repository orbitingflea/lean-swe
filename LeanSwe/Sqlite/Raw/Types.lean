namespace LeanSwe.Sqlite.Raw

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

/-- Typed SQLite error returned by `LeanSwe.Sqlite.Raw` and `LeanSwe.Sqlite` operations. -/
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
  /-- Underlying OS or SQLite I/O failure (`SQLITE_IOERR` / `SQLITE_FULL` / etc.). -/
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

/-- Maximum `busyTimeoutMs` accepted by `sqlite3_busy_timeout` (signed 32-bit `int` max). -/
def maxBusyTimeoutMs : Nat := 2147483647

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
  /-- Unique handle identifier assigned by the raw backend. -/
  id : UInt64
  deriving Repr, BEq, DecidableEq

/-- Opaque handle identifier for a prepared SQLite statement. -/
structure StmtHandle where
  /-- Unique statement identifier assigned by the raw backend. -/
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

/-- Concrete `IO` thin-wrapper API bundle exported by `LeanSwe.Sqlite.Raw`. -/
abbrev RawSqliteOps := RawSqliteOpsM IO

end LeanSwe.Sqlite.Raw
