import LeanSwe.Sqlite.Types
import LeanSweProofs.Sqlite.Model.PureSpec
import LeanSweProofs.Sqlite.Model.World

namespace LeanSwe.Sqlite.Model

open LeanSwe.Sqlite
  (SqliteError SqliteRawError SqliteValue maxBusyTimeoutMs maxSqlByteLen
   OpenConfig DbHandle StmtHandle StepResult
   RawStepTag RawFinalizeResult CSqliteOpsM RawSqliteOpsM)

/-- Step a prepared `PRAGMA` statement until `.done` with bounded fuel. -/
def stepPragmaLoopModel {m : Type → Type} [Monad m] (cops : CSqliteOpsM m UInt64 UInt64)
    (rawStmt : UInt64) : Nat → m (Except SqliteRawError Unit)
  | 0 => pure (.error (.userError "sqlite pragma step limit exceeded"))
  | fuel + 1 => do
    match ← cops.step rawStmt with
    | .error e => pure (.error e)
    | .ok .done => pure (.ok ())
    | .ok .row => stepPragmaLoopModel cops rawStmt fuel

/-- Prepare, step to completion, and always finalize a connection-setup `PRAGMA` statement. -/
def runSetupPragmaModel {m : Type → Type} [Monad m] [MonadFinally m] (cops : CSqliteOpsM m UInt64 UInt64)
    (rawDb : UInt64) (pragmaSql : String) : m (Except SqliteRawError Unit) := do
  match ← cops.prepareV2 rawDb pragmaSql with
  | .error e => pure (.error e)
  | .ok (none, _) => pure (.error (.misuse 21 "empty pragma SQL statement"))
  | .ok (some rawStmt, _) =>
    let (stepRes, finOut) ← tryFinally' (stepPragmaLoopModel cops rawStmt 4)
      (fun _ => cops.finalize rawStmt)
    match stepRes with
    | .error e => pure (.error e)
    | .ok () =>
      match finOut with
      | .finalized none => pure (.ok ())
      | .finalized (some e) => pure (.error e)
      | .rejected e => pure (.error e)

/-- Run post-`openV2` connection setup in the model. -/
def setupConnectionModel {m : Type → Type} [Monad m] [MonadFinally m] (cops : CSqliteOpsM m UInt64 UInt64)
    (path : String) (cfg : OpenConfig) (rawDb : UInt64) : m (Except SqliteRawError Unit) := do
  match ← cops.extendedResultCodes rawDb true with
  | .error e => pure (.error e)
  | .ok () =>
    match ← cops.busyTimeout rawDb (UInt32.ofNat cfg.busyTimeoutMs) with
    | .error e => pure (.error e)
    | .ok () =>
      let fkRes : Except SqliteRawError Unit ←
        if cfg.foreignKeys then
          runSetupPragmaModel cops rawDb "PRAGMA foreign_keys = ON;"
        else
          pure (.ok ())
      match fkRes with
      | .error e => pure (.error e)
      | .ok () =>
        if shouldEnableWalModel path cfg then
          runSetupPragmaModel cops rawDb "PRAGMA journal_mode = WAL;"
        else
          pure (.ok ())

/-- Bind a single `SqliteValue` at 1-based parameter index `paramIdx`. -/
def bindOneParamModel {m : Type → Type} (cops : CSqliteOpsM m UInt64 UInt64) (rawStmt : UInt64)
    (paramIdx : UInt32) : SqliteValue → m (Except SqliteRawError Unit)
  | .null => cops.bindNull rawStmt paramIdx
  | .int v => cops.bindInt64 rawStmt paramIdx v
  | .real d => cops.bindDouble rawStmt paramIdx d
  | .text s => cops.bindText rawStmt paramIdx s
  | .bytes b => cops.bindBlob rawStmt paramIdx b

/-- Bind all parameters in `params` (`1`-indexed in SQLite) sequentially. -/
def bindLoopModel {m : Type → Type} [Monad m] (cops : CSqliteOpsM m UInt64 UInt64) (rawStmt : UInt64)
    (params : Array SqliteValue) : Nat → m (Except SqliteError Unit)
  | 0 => pure (.ok ())
  | rem + 1 => do
    let idx := params.size - (rem + 1)
    let param := params.getD idx .null
    match ← bindOneParamModel cops rawStmt (UInt32.ofNat (idx + 1)) param with
    | .error rawErr => pure (.error (mapRawError rawErr))
    | .ok () => bindLoopModel cops rawStmt params rem

/-- Decode result columns `0 ..< total` (`rem` columns remaining) from `rawStmt`. -/
def decodeColumnsModel {m : Type → Type} [Monad m] (cops : CSqliteOpsM m UInt64 UInt64)
    (rawStmt : UInt64) (total : Nat) :
    Nat → Array SqliteValue → m (Except SqliteError (Array SqliteValue))
  | 0, acc => pure (.ok acc)
  | rem + 1, acc => do
    let colIdx := total - (rem + 1)
    let colU := UInt32.ofNat colIdx
    match ← cops.columnType rawStmt colU with
    | .error rawErr => pure (.error (mapRawError rawErr))
    | .ok ty =>
      let valRes : Except SqliteError SqliteValue ←
        match ty.toNat with
        | 1 => do
          match ← cops.columnInt64 rawStmt colU with
          | .error rawErr => pure (.error (mapRawError rawErr))
          | .ok v => pure (.ok (.int v))
        | 2 => do
          match ← cops.columnDouble rawStmt colU with
          | .error rawErr => pure (.error (mapRawError rawErr))
          | .ok d => pure (.ok (.real d))
        | 3 => do
          match ← cops.columnTextBytes rawStmt colU with
          | .error rawErr => pure (.error (mapRawError rawErr))
          | .ok bs =>
            match String.fromUTF8? bs with
            | some s => pure (.ok (.text s))
            | none => pure (.error (mapRawError (.userError "invalid UTF-8 in SQLite TEXT column")))
        | 4 => do
          match ← cops.columnBlob rawStmt colU with
          | .error rawErr => pure (.error (mapRawError rawErr))
          | .ok bs => pure (.ok (.bytes bs))
        | _ => pure (.ok .null)
      match valRes with
      | .error err => pure (.error err)
      | .ok val => decodeColumnsModel cops rawStmt total rem (acc.push val)

/-- Run `act` under `cops.lockStmt stmt`, always releasing via `cops.unlockStmt stmt` when acquired. -/
def withStmtLockModel {m : Type → Type} [Monad m] [MonadFinally m] (cops : CSqliteOpsM m UInt64 UInt64)
    {α : Type} (stmt : StmtHandle) (act : m α) : m α := do
  let locked ← cops.lockStmt stmt
  let (res, _) ← tryFinally' act (fun _ => if locked then cops.unlockStmt stmt else pure ())
  pure res

/-- Pure model specification of `RawSqliteOpsM m` built over `CSqliteOpsM m UInt64 UInt64`. -/
def mkRawOpsModel {m : Type → Type} [Monad m] [MonadFinally m]
    (cops : CSqliteOpsM m UInt64 UInt64) : RawSqliteOpsM m :=
  { mapRawError := mapRawError
    openDb := fun path cfg => do
      let pathBytes := path.toUTF8
      if pathBytes.size == 0 then
        pure (.error (mapRawError (.invalidArgument "database path must not be empty")))
      else if hasZeroByteBaModel pathBytes 0 then
        pure (.error (mapRawError (.invalidArgument "database path contains embedded NUL byte")))
      else if cfg.readOnly && cfg.createIfMissing then
        pure (.error (mapRawError (.invalidArgument
          "cannot combine readOnly = true with createIfMissing = true")))
      else if cfg.busyTimeoutMs > maxBusyTimeoutMs then
        pure (.error (mapRawError (.invalidArgument
          s!"busyTimeoutMs {cfg.busyTimeoutMs} exceeds maxBusyTimeoutMs ({maxBusyTimeoutMs})")))
      else
        let flags := computeOpenFlagsModel cfg
        match ← cops.openV2 path flags with
        | .error rawErr =>
          pure (.error (mapRawError (attachOpenPathModel path rawErr)))
        | .ok rawDb =>
          let (setupRes, _) ← tryFinally' (setupConnectionModel cops path cfg rawDb) fun
            | some (.ok ()) => pure ()
            | _ => do
              let _ ← cops.close rawDb
              pure ()
          match setupRes with
          | .error rawErr =>
            pure (.error (mapRawError (attachOpenPathModel path rawErr)))
          | .ok () =>
            let db ← cops.modifyTable (tableInsertDb rawDb)
            pure (.ok db)
    closeDb := fun db => do
      let lookupRes ← cops.modifyTable (tableCheckCloseDb db.id)
      match lookupRes with
      | .error rawErr => pure (.error (mapRawError rawErr))
      | .ok rawDb =>
        match ← cops.close rawDb with
        | .error rawErr => pure (.error (mapRawError rawErr))
        | .ok () =>
          cops.modifyTable (tableEraseDb db.id)
          pure (.ok ())
    prepare := fun db sql => do
      if sql.utf8ByteSize > maxSqlByteLen then
        pure (.error (mapRawError (.invalidArgument "SQL statement exceeds maximum byte length")))
      else
        let sqlBytes := sql.toUTF8
        if hasZeroByteBaModel sqlBytes 0 then
          pure (.error (mapRawError (.invalidArgument "SQL string contains embedded NUL byte")))
        else
          let rawDb? ← cops.modifyTable (tableLookupDb db.id)
          match rawDb? with
          | none => pure (.error (mapRawError (.misuse 21 "invalid or closed database handle")))
          | some rawDb =>
            match ← cops.prepareV2 rawDb sql with
            | .error rawErr => pure (.error (mapRawError rawErr))
            | .ok (none, _) => pure (.error (mapRawError (.misuse 21 "empty SQL statement")))
            | .ok (some rawStmt, consumedByteLen) =>
              let totalBytes := sqlBytes.size
              let tailOk := consumedByteLen ≤ totalBytes &&
                scanSqlTailBaModel .normal sqlBytes consumedByteLen
              if !tailOk then
                let _ ← cops.finalize rawStmt
                pure (.error (mapRawError (.misuse 21
                  "multiple SQL statements are not allowed in prepare")))
              else
                let sh ← cops.modifyTable (tableInsertStmt db.id rawStmt)
                pure (.ok sh)
    bind := fun stmt params =>
      withStmtLockModel cops stmt do
        let rawStmt? ← cops.modifyTable (tableLookupStmt stmt)
        match rawStmt? with
        | none => pure (.error (mapRawError (.misuse 21 "invalid or finalized statement handle")))
        | some rawStmt =>
          match ← cops.reset rawStmt with
          | .error rawErr => pure (.error (mapRawError rawErr))
          | .ok () =>
            match ← cops.clearBindings rawStmt with
            | .error rawErr => pure (.error (mapRawError rawErr))
            | .ok () =>
              match ← cops.bindParamCount rawStmt with
              | .error rawErr => pure (.error (mapRawError rawErr))
              | .ok expectedCount =>
                if params.size != expectedCount.toNat then
                  pure (.error (mapRawError (.invalidArgument
                    s!"parameter count mismatch: expected {expectedCount}, got {params.size}")))
                else
                  bindLoopModel cops rawStmt params params.size
    step := fun stmt =>
      withStmtLockModel cops stmt do
        let rawStmt? ← cops.modifyTable (tableLookupStmt stmt)
        match rawStmt? with
        | none => pure (.error (mapRawError (.misuse 21 "invalid or finalized statement handle")))
        | some rawStmt =>
          match ← cops.step rawStmt with
          | .error rawErr => pure (.error (mapRawError rawErr))
          | .ok .done => pure (.ok .done)
          | .ok .row =>
            match ← cops.columnCount rawStmt with
            | .error rawErr => pure (.error (mapRawError rawErr))
            | .ok cnt =>
              let colsRes ← decodeColumnsModel cops rawStmt cnt.toNat cnt.toNat #[]
              match colsRes with
              | .error err => pure (.error err)
              | .ok cols => pure (.ok (.row cols))
    finalize := fun stmt =>
      withStmtLockModel cops stmt do
        let rawStmt? ← cops.modifyTable (tableLookupStmt stmt)
        match rawStmt? with
        | none => pure (.error (mapRawError (.misuse 21 "invalid or already finalized statement handle")))
        | some rawStmt =>
          match ← cops.finalize rawStmt with
          | .finalized stickyErr? =>
            cops.modifyTable (tableEraseStmt stmt)
            match stickyErr? with
            | none => pure (.ok ())
            | some rawErr => pure (.error (mapRawError rawErr))
          | .rejected rawErr =>
            pure (.error (mapRawError rawErr))
    activeDbCount := cops.modifyTable tableActiveDbCount
    activeStmtCount := cops.modifyTable tableActiveStmtCount }

/-- Canonical deterministic `RawSqliteOpsM (StateM SqliteRawState)` behavior model. -/
def modelRawSqliteOps : RawSqliteOpsM (StateM SqliteRawState) :=
  mkRawOpsModel modelCSqliteOps

/-- Request algebra for thin `CSqliteOpsM` primitives and `RawHandleTable` transitions. -/
inductive CStepReq where
  /-- Read active database count from `RawHandleTable`. -/
  | tableActiveDbCount
  /-- Read active statement count from `RawHandleTable`. -/
  | tableActiveStmtCount
  /-- Allocate a new `DbHandle` in `RawHandleTable`. -/
  | tableInsertDb (rawDb : UInt64)
  /-- Validate `dbId` prior to `closeDb`. -/
  | tableCheckCloseDb (dbId : UInt64)
  /-- Erase closed `dbId` from `RawHandleTable`. -/
  | tableEraseDb (dbId : UInt64)
  /-- Look up `dbId` in `RawHandleTable`. -/
  | tableLookupDb (dbId : UInt64)
  /-- Allocate a new `StmtHandle` on `dbId` in `RawHandleTable`. -/
  | tableInsertStmt (dbId : UInt64) (rawStmt : UInt64)
  /-- Look up `stmt` in `RawHandleTable`. -/
  | tableLookupStmt (stmt : StmtHandle)
  /-- Erase finalized `stmt` from `RawHandleTable`. -/
  | tableEraseStmt (stmt : StmtHandle)
  /-- Thin `sqlite3_open_v2(path, flags)`. -/
  | openV2 (path : String) (flags : UInt32)
  /-- Thin `sqlite3_close(rawDb)`. -/
  | close (rawDb : UInt64)
  /-- Thin `sqlite3_extended_result_codes(rawDb, onoff)`. -/
  | extendedResultCodes (rawDb : UInt64) (onoff : Bool)
  /-- Thin `sqlite3_busy_timeout(rawDb, ms)`. -/
  | busyTimeout (rawDb : UInt64) (ms : UInt32)
  /-- Thin `sqlite3_prepare_v2(rawDb, sql)`. -/
  | prepareV2 (rawDb : UInt64) (sql : String)
  /-- Thin `sqlite3_step(rawStmt)`. -/
  | step (rawStmt : UInt64)
  /-- Thin `sqlite3_reset(rawStmt)`. -/
  | reset (rawStmt : UInt64)
  /-- Thin `sqlite3_clear_bindings(rawStmt)`. -/
  | clearBindings (rawStmt : UInt64)
  /-- Thin `sqlite3_finalize(rawStmt)`. -/
  | finalize (rawStmt : UInt64)
  /-- Thin `sqlite3_bind_parameter_count(rawStmt)`. -/
  | bindParamCount (rawStmt : UInt64)
  /-- Thin `sqlite3_bind_null(rawStmt, idx)`. -/
  | bindNull (rawStmt : UInt64) (idx : UInt32)
  /-- Thin `sqlite3_bind_int64(rawStmt, idx, val)`. -/
  | bindInt64 (rawStmt : UInt64) (idx : UInt32) (val : Int64)
  /-- Thin `sqlite3_bind_double(rawStmt, idx, val)`. -/
  | bindDouble (rawStmt : UInt64) (idx : UInt32) (val : Float)
  /-- Thin `sqlite3_bind_text64(rawStmt, idx, val)`. -/
  | bindText (rawStmt : UInt64) (idx : UInt32) (val : String)
  /-- Thin `sqlite3_bind_blob64(rawStmt, idx, val)`. -/
  | bindBlob (rawStmt : UInt64) (idx : UInt32) (val : ByteArray)
  /-- Thin `sqlite3_column_count(rawStmt)`. -/
  | columnCount (rawStmt : UInt64)
  /-- Thin `sqlite3_column_type(rawStmt, col)`. -/
  | columnType (rawStmt : UInt64) (col : UInt32)
  /-- Thin `sqlite3_column_int64(rawStmt, col)`. -/
  | columnInt64 (rawStmt : UInt64) (col : UInt32)
  /-- Thin `sqlite3_column_double(rawStmt, col)`. -/
  | columnDouble (rawStmt : UInt64) (col : UInt32)
  /-- Thin `sqlite3_column_text_bytes(rawStmt, col)`. -/
  | columnTextBytes (rawStmt : UInt64) (col : UInt32)
  /-- Thin `sqlite3_column_blob(rawStmt, col)`. -/
  | columnBlob (rawStmt : UInt64) (col : UInt32)
  /-- Acquire per-statement lock for `stmt`. -/
  | lockStmt (stmt : StmtHandle)
  /-- Release per-statement lock for `stmt`. -/
  | unlockStmt (stmt : StmtHandle)
  deriving Inhabited

/-- Output algebra for `CStepReq` transitions. -/
inductive CStepOut where
  /-- Count returned by `tableActiveDbCount` or `tableActiveStmtCount`. -/
  | count (n : Nat)
  /-- Boolean result returned by `lockStmt`. -/
  | boolRes (b : Bool)
  /-- Allocated `DbHandle` from `tableInsertDb`. -/
  | dbHandle (db : DbHandle)
  /-- Validated `UInt64` or raw error from `tableCheckCloseDb` or `openV2`. -/
  | rawDbRes (res : Except SqliteRawError UInt64)
  /-- Unit table update result from `tableEraseDb` or `tableEraseStmt`. -/
  | tableUnit
  /-- Optional `UInt64` from `tableLookupDb`. -/
  | rawDbOpt (res : Option UInt64)
  /-- Allocated `StmtHandle` from `tableInsertStmt`. -/
  | stmtHandle (sh : StmtHandle)
  /-- Optional `UInt64` from `tableLookupStmt`. -/
  | rawStmtOpt (res : Option UInt64)
  /-- Fallible `Unit` result from `close`, `extendedResultCodes`, `busyTimeout`, `reset`, `clearBindings`, or `bind*`. -/
  | unitRes (res : Except SqliteRawError Unit)
  /-- Fallible `(stmt?, consumedByteLen)` result from `prepareV2`. -/
  | prepRes (res : Except SqliteRawError (Option UInt64 × Nat))
  /-- Fallible `RawStepTag` result from `step`. -/
  | stepTagRes (res : Except SqliteRawError RawStepTag)
  /-- `RawFinalizeResult` from `finalize`. -/
  | finRes (res : RawFinalizeResult)
  /-- Fallible `UInt32` result from `bindParamCount`, `columnCount`, or `columnType`. -/
  | u32Res (res : Except SqliteRawError UInt32)
  /-- Fallible `Int64` result from `columnInt64`. -/
  | i64Res (res : Except SqliteRawError Int64)
  /-- Fallible `Float` result from `columnDouble`. -/
  | floatRes (res : Except SqliteRawError Float)
  /-- Fallible `ByteArray` result from `columnTextBytes` or `columnBlob`. -/
  | bytesRes (res : Except SqliteRawError ByteArray)
  deriving Inhabited

/-- Execute one `CStepReq` against an arbitrary `CSqliteOpsM (StateM W) UInt64 UInt64`. -/
def execCStep {W : Type} (cops : CSqliteOpsM (StateM W) UInt64 UInt64) : CStepReq → StateM W CStepOut
  | .tableActiveDbCount => .count <$> cops.modifyTable tableActiveDbCount
  | .tableActiveStmtCount => .count <$> cops.modifyTable tableActiveStmtCount
  | .tableInsertDb rawDb => .dbHandle <$> cops.modifyTable (tableInsertDb rawDb)
  | .tableCheckCloseDb dbId => .rawDbRes <$> cops.modifyTable (tableCheckCloseDb dbId)
  | .tableEraseDb dbId => (fun _ => CStepOut.tableUnit) <$> cops.modifyTable (tableEraseDb dbId)
  | .tableLookupDb dbId => .rawDbOpt <$> cops.modifyTable (tableLookupDb dbId)
  | .tableInsertStmt dbId rawStmt => .stmtHandle <$> cops.modifyTable (tableInsertStmt dbId rawStmt)
  | .tableLookupStmt stmt => .rawStmtOpt <$> cops.modifyTable (tableLookupStmt stmt)
  | .tableEraseStmt stmt => (fun _ => CStepOut.tableUnit) <$> cops.modifyTable (tableEraseStmt stmt)
  | .openV2 path flags => .rawDbRes <$> cops.openV2 path flags
  | .close rawDb => .unitRes <$> cops.close rawDb
  | .extendedResultCodes rawDb onoff => .unitRes <$> cops.extendedResultCodes rawDb onoff
  | .busyTimeout rawDb ms => .unitRes <$> cops.busyTimeout rawDb ms
  | .prepareV2 rawDb sql => .prepRes <$> cops.prepareV2 rawDb sql
  | .step rawStmt => .stepTagRes <$> cops.step rawStmt
  | .reset rawStmt => .unitRes <$> cops.reset rawStmt
  | .clearBindings rawStmt => .unitRes <$> cops.clearBindings rawStmt
  | .finalize rawStmt => .finRes <$> cops.finalize rawStmt
  | .bindParamCount rawStmt => .u32Res <$> cops.bindParamCount rawStmt
  | .bindNull rawStmt idx => .unitRes <$> cops.bindNull rawStmt idx
  | .bindInt64 rawStmt idx val => .unitRes <$> cops.bindInt64 rawStmt idx val
  | .bindDouble rawStmt idx val => .unitRes <$> cops.bindDouble rawStmt idx val
  | .bindText rawStmt idx val => .unitRes <$> cops.bindText rawStmt idx val
  | .bindBlob rawStmt idx val => .unitRes <$> cops.bindBlob rawStmt idx val
  | .columnCount rawStmt => .u32Res <$> cops.columnCount rawStmt
  | .columnType rawStmt col => .u32Res <$> cops.columnType rawStmt col
  | .columnInt64 rawStmt col => .i64Res <$> cops.columnInt64 rawStmt col
  | .columnDouble rawStmt col => .floatRes <$> cops.columnDouble rawStmt col
  | .columnTextBytes rawStmt col => .bytesRes <$> cops.columnTextBytes rawStmt col
  | .columnBlob rawStmt col => .bytesRes <$> cops.columnBlob rawStmt col
  | .lockStmt stmt => .boolRes <$> cops.lockStmt stmt
  | .unlockStmt stmt => (fun _ => CStepOut.tableUnit) <$> cops.unlockStmt stmt

/-- Well-formedness guard on `SqliteRawState` for low-level `CSqliteOpsM` transitions. -/
def cStepWf (_ : SqliteRawState) : Bool := true

/-- Well-formedness guard on `SqliteRawState` for `RawSqliteOpsM` transitions requiring balanced statement locks. -/
def rawOpsStepWf (s : SqliteRawState) : Bool := s.heldStmtLocks.isEmpty

/-- Allowed single-step transition relation for `CSqliteOpsM` over `SqliteRawState`. -/
def allowedCStep (s : SqliteRawState) (req : CStepReq) (out : CStepOut)
    (s' : SqliteRawState) : Prop :=
  let r := (execCStep modelCSqliteOps req).run s
  out = r.1 ∧ s' = r.2

/-- Allowed single-step transition relation for `RawSqliteOpsM` over `SqliteRawState`,
    enforcing deterministic output/state refinement and balanced statement-lock release (`rawOpsStepWf s' = true`). -/
def allowedRawOpsStep (s : SqliteRawState) (req : RawStepReq) (out : RawStepOut)
    (s' : SqliteRawState) : Prop :=
  let r := (execRawStep modelRawSqliteOps req).run s
  out = r.1 ∧ s' = r.2 ∧ rawOpsStepWf s' = true

end LeanSwe.Sqlite.Model
