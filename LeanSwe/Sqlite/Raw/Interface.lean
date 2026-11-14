import LeanSwe.Sqlite.Raw.Types
import LeanSwe.Sqlite.Raw.Impl

namespace LeanSwe.Sqlite.Raw

@[extern "leanswe_sqlite_open_db"]
private opaque rawOpenDb : @& String → UInt8 → UInt8 → UInt32 → UInt8 → UInt8 →
    IO (UInt32 × String × UInt64)

@[extern "leanswe_sqlite_close_db"]
private opaque rawCloseDb : UInt64 → IO (UInt32 × String)

@[extern "leanswe_sqlite_prepare"]
private opaque rawPrepare : UInt64 → @& String → IO (UInt32 × String × UInt64)

@[extern "leanswe_sqlite_bind_param_count"]
private opaque rawBindParamCount : UInt64 → UInt64 → IO (UInt32 × String × UInt32)

@[extern "leanswe_sqlite_clear_and_reset"]
private opaque rawClearAndReset : UInt64 → UInt64 → IO (UInt32 × String)

@[extern "leanswe_sqlite_bind_null"]
private opaque rawBindNull : UInt64 → UInt64 → UInt32 → IO (UInt32 × String)

@[extern "leanswe_sqlite_bind_int64"]
private opaque rawBindInt64 : UInt64 → UInt64 → UInt32 → Int64 → IO (UInt32 × String)

@[extern "leanswe_sqlite_bind_double"]
private opaque rawBindDouble : UInt64 → UInt64 → UInt32 → Float → IO (UInt32 × String)

@[extern "leanswe_sqlite_bind_text"]
private opaque rawBindText : UInt64 → UInt64 → UInt32 → @& String → IO (UInt32 × String)

@[extern "leanswe_sqlite_bind_blob"]
private opaque rawBindBlob : UInt64 → UInt64 → UInt32 → @& ByteArray → IO (UInt32 × String)

@[extern "leanswe_sqlite_step"]
private opaque rawStep : UInt64 → UInt64 → IO (UInt32 × String × UInt8)

@[extern "leanswe_sqlite_column_count"]
private opaque rawColumnCount : UInt64 → UInt64 → IO UInt32

@[extern "leanswe_sqlite_column_type"]
private opaque rawColumnType : UInt64 → UInt64 → UInt32 → IO UInt32

@[extern "leanswe_sqlite_column_int64"]
private opaque rawColumnInt64 : UInt64 → UInt64 → UInt32 → IO Int64

@[extern "leanswe_sqlite_column_double"]
private opaque rawColumnDouble : UInt64 → UInt64 → UInt32 → IO Float

@[extern "leanswe_sqlite_column_text"]
private opaque rawColumnText : UInt64 → UInt64 → UInt32 → IO String

@[extern "leanswe_sqlite_column_blob"]
private opaque rawColumnBlob : UInt64 → UInt64 → UInt32 → IO ByteArray

@[extern "leanswe_sqlite_finalize"]
private opaque rawFinalize : UInt64 → UInt64 → IO (UInt32 × String)

@[extern "leanswe_sqlite_active_db_count"]
private opaque rawActiveDbCount : IO Nat

@[extern "leanswe_sqlite_active_stmt_count"]
private opaque rawActiveStmtCount : IO Nat

private def sqliteFfiOps : Internal.SqliteFfiOps :=
  { openDb := rawOpenDb
    closeDb := rawCloseDb
    prepare := rawPrepare
    bindParamCount := rawBindParamCount
    clearAndReset := rawClearAndReset
    bindNull := rawBindNull
    bindInt64 := rawBindInt64
    bindDouble := rawBindDouble
    bindText := rawBindText
    bindBlob := rawBindBlob
    step := rawStep
    columnCount := rawColumnCount
    columnType := rawColumnType
    columnInt64 := rawColumnInt64
    columnDouble := rawColumnDouble
    columnText := rawColumnText
    columnBlob := rawColumnBlob
    finalize := rawFinalize
    activeDbCount := rawActiveDbCount
    activeStmtCount := rawActiveStmtCount }

/-- Default single-step SQLite operations backed by `c/sqlite_shim.c` and vendored SQLite3. -/
def defaultOps : RawSqliteOps :=
  Internal.mkRawOps sqliteFfiOps

/-- Convert a raw SQLite error record into a normalized `SqliteError` with non-empty message. -/
@[inline] def mapRawError (err : SqliteRawError) : SqliteError :=
  defaultOps.mapRawError err

/-- Open a SQLite connection at `path` with `cfg`. -/
@[inline] def openDb (path : String) (cfg : OpenConfig := {}) : IO (Except SqliteError DbHandle) :=
  defaultOps.openDb path cfg

/-- Close an open SQLite connection handle. -/
@[inline] def closeDb (db : DbHandle) : IO (Except SqliteError Unit) :=
  defaultOps.closeDb db

/-- Prepare a single SQL statement on `db`. -/
@[inline] def prepare (db : DbHandle) (sql : String) : IO (Except SqliteError StmtHandle) :=
  defaultOps.prepare db sql

/-- Bind typed parameters to a prepared statement (`1`-indexed in SQLite). -/
@[inline] def bind (stmt : StmtHandle) (params : Array SqliteValue) : IO (Except SqliteError Unit) :=
  defaultOps.bind stmt params

/-- Execute one step of a prepared statement. -/
@[inline] def step (stmt : StmtHandle) : IO (Except SqliteError StepResult) :=
  defaultOps.step stmt

/-- Finalize and release a prepared statement handle. -/
@[inline] def finalize (stmt : StmtHandle) : IO (Except SqliteError Unit) :=
  defaultOps.finalize stmt

/-- Return the number of currently open SQLite database handles. -/
@[inline] def activeDbCount : IO Nat :=
  defaultOps.activeDbCount

/-- Return the number of currently active prepared SQLite statement handles. -/
@[inline] def activeStmtCount : IO Nat :=
  defaultOps.activeStmtCount

end LeanSwe.Sqlite.Raw
