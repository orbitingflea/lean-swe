import LeanSwe.Sqlite.Raw.Types

namespace LeanSwe.Sqlite.Raw.Internal

open LeanSwe.Sqlite.Raw
  (SqliteErrorKind SqliteError SqliteRawError SqliteValue maxBusyTimeoutMs OpenConfig
   DbHandle StmtHandle StepResult RawSqliteOpsM RawSqliteOps)

/-- SQLite C-ABI operations injected by `LeanSwe.Sqlite.Raw.Interface`. -/
structure SqliteFfiOps where
  /-- Open a SQLite connection via `sqlite3_open_v2`. -/
  openDb : String → UInt8 → UInt8 → UInt32 → UInt8 → UInt8 → IO (UInt32 × String × UInt64)
  /-- Close a SQLite connection handle. -/
  closeDb : UInt64 → IO (UInt32 × String)
  /-- Prepare a single SQL statement on a connection handle. -/
  prepare : UInt64 → String → IO (UInt32 × String × UInt64)
  /-- Query the number of bind parameters in a prepared statement. -/
  bindParamCount : UInt64 → UInt64 → IO (UInt32 × String × UInt32)
  /-- Reset a prepared statement and clear existing bindings. -/
  clearAndReset : UInt64 → UInt64 → IO (UInt32 × String)
  /-- Bind `NULL` at 1-based parameter index. -/
  bindNull : UInt64 → UInt64 → UInt32 → IO (UInt32 × String)
  /-- Bind 64-bit signed integer at 1-based parameter index. -/
  bindInt64 : UInt64 → UInt64 → UInt32 → Int64 → IO (UInt32 × String)
  /-- Bind 64-bit IEEE-754 float at 1-based parameter index. -/
  bindDouble : UInt64 → UInt64 → UInt32 → Float → IO (UInt32 × String)
  /-- Bind UTF-8 text at 1-based parameter index. -/
  bindText : UInt64 → UInt64 → UInt32 → String → IO (UInt32 × String)
  /-- Bind binary blob at 1-based parameter index. -/
  bindBlob : UInt64 → UInt64 → UInt32 → ByteArray → IO (UInt32 × String)
  /-- Step a prepared statement (`0` = done, `1` = row). -/
  step : UInt64 → UInt64 → IO (UInt32 × String × UInt8)
  /-- Return number of result columns for the current statement. -/
  columnCount : UInt64 → UInt64 → IO UInt32
  /-- Return SQLite column type tag for column `col`. -/
  columnType : UInt64 → UInt64 → UInt32 → IO UInt32
  /-- Decode 64-bit integer value for column `col`. -/
  columnInt64 : UInt64 → UInt64 → UInt32 → IO Int64
  /-- Decode 64-bit float value for column `col`. -/
  columnDouble : UInt64 → UInt64 → UInt32 → IO Float
  /-- Decode UTF-8 text value for column `col`. -/
  columnText : UInt64 → UInt64 → UInt32 → IO String
  /-- Decode binary blob value for column `col`. -/
  columnBlob : UInt64 → UInt64 → UInt32 → IO ByteArray
  /-- Finalize and release a prepared statement handle. -/
  finalize : UInt64 → UInt64 → IO (UInt32 × String)
  /-- Return count of currently open database handles tracked by the C shim. -/
  activeDbCount : IO Nat
  /-- Return count of currently active statement handles tracked by the C shim. -/
  activeStmtCount : IO Nat

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Map a primary SQLite result code (`code &&& 0xFF`) into `SqliteErrorKind`. -/
def classifySqliteCode (code : UInt32) (defaultKind : SqliteErrorKind) : SqliteErrorKind :=
  match (code &&& 0xFF).toNat with
  | 5 | 6 => .busy
  | 14 => .notFound
  | 19 => .constraint
  | 21 => .misuse
  | 25 => .invalidInput
  | _ => defaultKind

/-- Convert a numeric SQLite result code and diagnostic string into `SqliteRawError`. -/
def classifyRawCode (path? : Option String) (code : UInt32) (detail : String) : SqliteRawError :=
  match (code &&& 0xFF).toNat with
  | 5 | 6 => .busy code detail
  | 14 => .cantOpen path? code detail
  | 19 => .constraint code detail
  | 21 => .misuse code detail
  | 25 => .invalidArgument detail
  | 8 | 10 | 11 | 13 | 26 => .ioFailure code detail
  | _ => .sqliteCodeError code detail

/-- Convert a pure `SqliteRawError` into a normalized `SqliteError` with non-empty message. -/
def mapRawError : SqliteRawError → SqliteError
  | .cantOpen path? code detail =>
    { kind := .notFound
      sqliteCode := some code
      path := path?
      message := nonEmptyMsg "unable to open sqlite database" detail }
  | .busy code detail =>
    { kind := .busy
      sqliteCode := some code
      message := nonEmptyMsg "sqlite database is busy" detail }
  | .constraint code detail =>
    { kind := .constraint
      sqliteCode := some code
      message := nonEmptyMsg "sqlite constraint failed" detail }
  | .misuse code detail =>
    { kind := .misuse
      sqliteCode := some code
      message := nonEmptyMsg "sqlite library misuse" detail }
  | .invalidArgument detail =>
    { kind := .invalidInput
      message := nonEmptyMsg "invalid sqlite argument" detail }
  | .ioFailure code detail =>
    { kind := .ioError
      sqliteCode := some code
      message := nonEmptyMsg s!"sqlite io failure ({code})" detail }
  | .sqliteCodeError code detail =>
    { kind := classifySqliteCode code .ioError
      sqliteCode := some code
      message := nonEmptyMsg s!"sqlite error ({code})" detail }
  | .userError detail =>
    { kind := .ioError
      message := nonEmptyMsg "sqlite error" detail }

private def b2u8 (b : Bool) : UInt8 :=
  if b then 1 else 0

private def bindOneParam (ffi : SqliteFfiOps) (stmt : StmtHandle) (paramIdx : UInt32) :
    SqliteValue → IO (UInt32 × String)
  | .null => ffi.bindNull stmt.id stmt.dbId paramIdx
  | .int v => ffi.bindInt64 stmt.id stmt.dbId paramIdx v
  | .real d => ffi.bindDouble stmt.id stmt.dbId paramIdx d
  | .text s => ffi.bindText stmt.id stmt.dbId paramIdx s
  | .bytes b => ffi.bindBlob stmt.id stmt.dbId paramIdx b

private def bindLoop (ffi : SqliteFfiOps) (stmt : StmtHandle) (params : Array SqliteValue) :
    Nat → IO (Except SqliteError Unit)
  | 0 => return .ok ()
  | rem + 1 => do
    let idx := params.size - (rem + 1)
    let param := params.getD idx .null
    let (rc, msg) ← bindOneParam ffi stmt (UInt32.ofNat (idx + 1)) param
    if rc != 0 then
      return .error (mapRawError (classifyRawCode none rc msg))
    else
      bindLoop ffi stmt params rem

private def decodeColumns (ffi : SqliteFfiOps) (stmt : StmtHandle) (total : Nat) :
    Nat → Array SqliteValue → IO (Array SqliteValue)
  | 0, acc => return acc
  | rem + 1, acc => do
    let colIdx := total - (rem + 1)
    let colU := UInt32.ofNat colIdx
    let ty ← ffi.columnType stmt.id stmt.dbId colU
    let val ← match ty.toNat with
      | 1 => .int <$> ffi.columnInt64 stmt.id stmt.dbId colU
      | 2 => .real <$> ffi.columnDouble stmt.id stmt.dbId colU
      | 3 => .text <$> ffi.columnText stmt.id stmt.dbId colU
      | 4 => .bytes <$> ffi.columnBlob stmt.id stmt.dbId colU
      | _ => pure .null
    decodeColumns ffi stmt total rem (acc.push val)

/-- Build the concrete `RawSqliteOps` bundle backed by injected C-ABI FFI primitives. -/
def mkRawOps (ffi : SqliteFfiOps) : RawSqliteOps :=
  { mapRawError := mapRawError
    openDb := fun path cfg => do
      if path.isEmpty then
        return .error (mapRawError (.invalidArgument "database path must not be empty"))
      if cfg.readOnly && cfg.createIfMissing then
        return .error (mapRawError (.invalidArgument "cannot combine readOnly with createIfMissing"))
      if cfg.busyTimeoutMs > maxBusyTimeoutMs then
        return .error (mapRawError (.invalidArgument
          s!"busyTimeoutMs {cfg.busyTimeoutMs} exceeds maxBusyTimeoutMs ({maxBusyTimeoutMs})"))
      let (rc, msg, dbId) ← ffi.openDb
        path (b2u8 cfg.readOnly) (b2u8 cfg.createIfMissing)
        (UInt32.ofNat cfg.busyTimeoutMs) (b2u8 cfg.walMode) (b2u8 cfg.foreignKeys)
      if rc != 0 then
        return .error (mapRawError (classifyRawCode (some path) rc msg))
      else
        return .ok { id := dbId }
    closeDb := fun db => do
      let (rc, msg) ← ffi.closeDb db.id
      if rc != 0 then
        return .error (mapRawError (classifyRawCode none rc msg))
      else
        return .ok ()
    prepare := fun db sql => do
      let (rc, msg, stmtId) ← ffi.prepare db.id sql
      if rc != 0 then
        return .error (mapRawError (classifyRawCode none rc msg))
      else
        return .ok { id := stmtId, dbId := db.id }
    bind := fun stmt params => do
      let (rcReset, msgReset) ← ffi.clearAndReset stmt.id stmt.dbId
      if rcReset != 0 then
        return .error (mapRawError (classifyRawCode none rcReset msgReset))
      let (rcCnt, msgCnt, expectedCount) ← ffi.bindParamCount stmt.id stmt.dbId
      if rcCnt != 0 then
        return .error (mapRawError (classifyRawCode none rcCnt msgCnt))
      if params.size != expectedCount.toNat then
        return .error (mapRawError (.invalidArgument
          s!"parameter count mismatch: expected {expectedCount}, got {params.size}"))
      bindLoop ffi stmt params params.size
    step := fun stmt => do
      let (rc, msg, tag) ← ffi.step stmt.id stmt.dbId
      if rc != 0 then
        return .error (mapRawError (classifyRawCode none rc msg))
      else if tag == 0 then
        return .ok .done
      else
        let cnt ← ffi.columnCount stmt.id stmt.dbId
        let cols ← decodeColumns ffi stmt cnt.toNat cnt.toNat #[]
        return .ok (.row cols)
    finalize := fun stmt => do
      let (rc, msg) ← ffi.finalize stmt.id stmt.dbId
      if rc != 0 then
        return .error (mapRawError (classifyRawCode none rc msg))
      else
        return .ok ()
    activeDbCount := ffi.activeDbCount
    activeStmtCount := ffi.activeStmtCount }

end LeanSwe.Sqlite.Raw.Internal
