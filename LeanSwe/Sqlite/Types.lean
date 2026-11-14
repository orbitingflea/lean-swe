import LeanSwe.Sqlite.Raw.Types

namespace LeanSwe.Sqlite

export LeanSwe.Sqlite.Raw
  (SqliteErrorKind SqliteError SqliteRawError SqliteValue maxBusyTimeoutMs OpenConfig
   DbHandle StmtHandle StepResult RawSqliteOpsM RawSqliteOps)

/-- Single decoded result row returned by `query` and `queryOne`. -/
abbrev SqliteRow := Array SqliteValue

/-- Public operations exported by `LeanSwe.Sqlite`, parameterized over effect monad `m`. -/
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
