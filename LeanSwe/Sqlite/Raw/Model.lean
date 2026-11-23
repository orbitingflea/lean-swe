import LeanSwe.Sqlite.Raw.Types

namespace LeanSwe.Sqlite.Raw.Model

open LeanSwe.Sqlite.Raw
  (SqliteError SqliteRawError SqliteValue
   OpenConfig DbHandle StmtHandle StepResult RawSqliteOpsM)

/-- Request sum representing single-step `RawSqliteOpsM` boundary transitions. -/
inductive RawStepReq where
  /-- Normalize a raw `SqliteRawError` into `SqliteError`. -/
  | mapRawError (err : SqliteRawError)
  /-- Open a connection at `path` with `cfg`. -/
  | openDb (path : String) (cfg : OpenConfig)
  /-- Close an existing connection handle. -/
  | closeDb (db : DbHandle)
  /-- Prepare one SQL statement on `db`. -/
  | prepare (db : DbHandle) (sql : String)
  /-- Bind typed parameters to a prepared statement. -/
  | bind (stmt : StmtHandle) (params : Array SqliteValue)
  /-- Step a prepared statement once. -/
  | step (stmt : StmtHandle)
  /-- Finalize and destroy a prepared statement handle. -/
  | finalize (stmt : StmtHandle)
  /-- Read the active database handle count. -/
  | activeDbCount
  /-- Read the active prepared statement handle count. -/
  | activeStmtCount

/-- Output sum for single-step `RawSqliteOpsM` boundary transitions. -/
inductive RawStepOut where
  /-- Result of `RawSqliteOpsM.mapRawError`. -/
  | mapRawError (err : SqliteError)
  /-- Result of `RawSqliteOpsM.openDb`. -/
  | openDb (res : Except SqliteError DbHandle)
  /-- Result of `RawSqliteOpsM.closeDb`. -/
  | closeDb (res : Except SqliteError Unit)
  /-- Result of `RawSqliteOpsM.prepare`. -/
  | prepare (res : Except SqliteError StmtHandle)
  /-- Result of `RawSqliteOpsM.bind`. -/
  | bind (res : Except SqliteError Unit)
  /-- Result of `RawSqliteOpsM.step`. -/
  | step (res : Except SqliteError StepResult)
  /-- Result of `RawSqliteOpsM.finalize`. -/
  | finalize (res : Except SqliteError Unit)
  /-- Result of `RawSqliteOpsM.activeDbCount`. -/
  | activeDbCount (n : Nat)
  /-- Result of `RawSqliteOpsM.activeStmtCount`. -/
  | activeStmtCount (n : Nat)

/-- Execute one `RawStepReq` against an arbitrary `RawSqliteOpsM (StateM W)`. -/
def execRawStep {W : Type} (ops : RawSqliteOpsM (StateM W)) : RawStepReq → StateM W RawStepOut
  | .mapRawError err => pure (.mapRawError (ops.mapRawError err))
  | .openDb path cfg => .openDb <$> ops.openDb path cfg
  | .closeDb db => .closeDb <$> ops.closeDb db
  | .prepare db sql => .prepare <$> ops.prepare db sql
  | .bind stmt params => .bind <$> ops.bind stmt params
  | .step stmt => .step <$> ops.step stmt
  | .finalize stmt => .finalize <$> ops.finalize stmt
  | .activeDbCount => .activeDbCount <$> ops.activeDbCount
  | .activeStmtCount => .activeStmtCount <$> ops.activeStmtCount

end LeanSwe.Sqlite.Raw.Model
