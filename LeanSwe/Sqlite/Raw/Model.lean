import LeanSwe.Sqlite.Raw.Types

namespace LeanSwe.Sqlite.Raw.Model

open LeanSwe.Sqlite.Raw
  (SqliteErrorKind SqliteError SqliteRawError SqliteValue maxSqlByteLen
   sqliteOpenReadOnly sqliteOpenReadWrite sqliteOpenCreate sqliteOpenUri sqliteOpenFullMutex
   OpenConfig DbHandle StmtHandle StepResult RawSqliteOpsM)

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsgModel (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Map a primary SQLite result code (`code &&& 0xFF`) into `SqliteErrorKind`. -/
def classifySqliteCodeModel (code : UInt32) (defaultKind : SqliteErrorKind) : SqliteErrorKind :=
  match (code &&& 0xFF).toNat with
  | 5 | 6 => .busy
  | 14 => .notFound
  | 19 => .constraint
  | 21 => .misuse
  | 25 => .invalidInput
  | _ => defaultKind

/-- Convert a numeric SQLite result code and diagnostic string into `SqliteRawError`. -/
def classifyRawCodeModel (path? : Option String) (code : UInt32) (detail : String) : SqliteRawError :=
  match (code &&& 0xFF).toNat with
  | 5 | 6 => .busy code detail
  | 14 => .cantOpen path? code detail
  | 19 => .constraint code detail
  | 21 => .misuse code detail
  | 8 | 10 | 11 | 13 | 26 => .ioFailure code detail
  | _ => .sqliteCodeError code detail

/-- Convert a pure `SqliteRawError` into a normalized `SqliteError` with non-empty message. -/
def mapRawErrorModel : SqliteRawError → SqliteError
  | .cantOpen path? code detail =>
    { kind := .notFound
      sqliteCode := some code
      path := path?
      message := nonEmptyMsgModel "unable to open sqlite database" detail }
  | .busy code detail =>
    { kind := .busy
      sqliteCode := some code
      message := nonEmptyMsgModel "sqlite database is busy" detail }
  | .constraint code detail =>
    { kind := .constraint
      sqliteCode := some code
      message := nonEmptyMsgModel "sqlite constraint failed" detail }
  | .misuse code detail =>
    { kind := .misuse
      sqliteCode := some code
      message := nonEmptyMsgModel "sqlite library misuse" detail }
  | .invalidArgument detail =>
    { kind := .invalidInput
      message := nonEmptyMsgModel "invalid sqlite argument" detail }
  | .ioFailure code detail =>
    { kind := .ioError
      sqliteCode := some code
      message := nonEmptyMsgModel s!"sqlite io failure ({code})" detail }
  | .sqliteCodeError code detail =>
    { kind := classifySqliteCodeModel code .ioError
      sqliteCode := some code
      message := nonEmptyMsgModel s!"sqlite error ({code})" detail }
  | .userError detail =>
    { kind := .ioError
      message := nonEmptyMsgModel "sqlite error" detail }

/-- Attach `some path` to `.cantOpen none ...` errors produced while opening `path`. -/
def attachOpenPathModel (path : String) : SqliteRawError → SqliteRawError
  | .cantOpen none code detail => .cantOpen (some path) code detail
  | other => other

/-- Compute the `sqlite3_open_v2` bitmask (`SQLITE_OPEN_FULLMUTEX | SQLITE_OPEN_URI | ...`) for `cfg`. -/
def computeOpenFlagsModel (cfg : OpenConfig) : UInt32 :=
  let base := sqliteOpenFullMutex ||| sqliteOpenUri
  if cfg.readOnly then
    base ||| sqliteOpenReadOnly
  else if cfg.createIfMissing then
    base ||| sqliteOpenReadWrite ||| sqliteOpenCreate
  else
    base ||| sqliteOpenReadWrite

/-- Return `true` iff `bs` contains an embedded NUL (`0x00`) byte. -/
def hasZeroByteModel (bs : ByteArray) : Bool :=
  bs.data.toList.contains 0

/-- Validate raw UTF-8 SQL byte length and embedded-NUL constraints matching `sqlite3_prepare_v2`. -/
def validateRawSqlInputModel (sql : String) : Except SqliteRawError Unit :=
  let bs := sql.toUTF8
  if bs.size > maxSqlByteLen then
    .error (.invalidArgument "SQL statement exceeds maximum byte length")
  else if hasZeroByteModel bs then
    .error (.invalidArgument "SQL string contains embedded NUL byte")
  else
    .ok ()

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
