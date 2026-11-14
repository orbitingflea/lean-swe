import LeanSwe.Sqlite.Types
import LeanSwe.Sqlite.Impl
import LeanSwe.Sqlite.Raw.Interface

namespace LeanSwe.Sqlite

/-- Default `SqliteApi` backed by `LeanSwe.Sqlite.Raw.defaultOps`. -/
def defaultApi : SqliteApi :=
  Internal.mkApiM Raw.defaultOps

/-- Convert a raw SQLite error record into a normalized `SqliteError` with non-empty message. -/
@[inline] def mapRawError (err : SqliteRawError) : SqliteError :=
  defaultApi.mapRawError err

/-- Validate an `OpenConfig` before opening a connection. -/
@[inline] def validateConfig (cfg : OpenConfig) : Except SqliteError Unit :=
  defaultApi.validateConfig cfg

/-- Open a connection, run `action`, and always close the handle on both `.ok` and `.error`. -/
@[inline] def withDb {α : Type} (path : String) (cfg : OpenConfig := {})
    (action : DbHandle → IO (Except SqliteError α)) : IO (Except SqliteError α) :=
  defaultApi.withDb path cfg action

/-- Execute `action` inside an all-or-nothing transaction, committing on `.ok` and rolling back on `.error`. -/
@[inline] def withTransaction {α : Type} (db : DbHandle)
    (action : DbHandle → IO (Except SqliteError α)) : IO (Except SqliteError α) :=
  defaultApi.withTransaction db action

/-- Execute a parameterized SQL statement to completion without returning rows. -/
@[inline] def exec (db : DbHandle) (sql : String) (params : Array SqliteValue := #[]) :
    IO (Except SqliteError Unit) :=
  defaultApi.exec db sql params

/-- Execute a parameterized SQL query and collect all result rows. -/
@[inline] def query (db : DbHandle) (sql : String) (params : Array SqliteValue := #[]) :
    IO (Except SqliteError (Array SqliteRow)) :=
  defaultApi.query db sql params

/-- Execute a parameterized SQL query and return the first row, or `none` if empty. -/
@[inline] def queryOne (db : DbHandle) (sql : String) (params : Array SqliteValue := #[]) :
    IO (Except SqliteError (Option SqliteRow)) :=
  defaultApi.queryOne db sql params

/-- Return the number of currently open SQLite database handles. -/
@[inline] def activeDbCount : IO Nat :=
  defaultApi.activeDbCount

/-- Return the number of currently active prepared SQLite statement handles. -/
@[inline] def activeStmtCount : IO Nat :=
  defaultApi.activeStmtCount

end LeanSwe.Sqlite
