import Std.Sync.Mutex
import LeanSwe.Sqlite.Types
import LeanSwe.Sqlite.Impl

namespace LeanSwe.Sqlite

@[extern "leanswe_sqlite_open_v2"]
private opaque rawOpenV2 : @& String → UInt32 → BaseIO (UInt32 × String × Option RawDbHandle)

@[extern "leanswe_sqlite_close"]
private opaque rawClose : @& RawDbHandle → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_extended_result_codes"]
private opaque rawExtendedResultCodes : @& RawDbHandle → UInt8 → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_busy_timeout"]
private opaque rawBusyTimeout : @& RawDbHandle → UInt32 → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_prepare_v2"]
private opaque rawPrepareV2 : @& RawDbHandle → @& String → BaseIO (UInt32 × String × Option RawStmtHandle × Nat)

@[extern "leanswe_sqlite_step"]
private opaque rawStep : @& RawStmtHandle → BaseIO (UInt32 × String × UInt8)

@[extern "leanswe_sqlite_reset"]
private opaque rawReset : @& RawStmtHandle → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_clear_bindings"]
private opaque rawClearBindings : @& RawStmtHandle → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_finalize"]
private opaque rawFinalize : @& RawStmtHandle → BaseIO (UInt8 × UInt32 × String)

@[extern "leanswe_sqlite_bind_param_count"]
private opaque rawBindParamCount : @& RawStmtHandle → BaseIO (UInt32 × String × UInt32)

@[extern "leanswe_sqlite_bind_null"]
private opaque rawBindNull : @& RawStmtHandle → UInt32 → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_bind_int64"]
private opaque rawBindInt64 : @& RawStmtHandle → UInt32 → Int64 → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_bind_double"]
private opaque rawBindDouble : @& RawStmtHandle → UInt32 → Float → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_bind_text"]
private opaque rawBindText : @& RawStmtHandle → UInt32 → @& String → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_bind_blob"]
private opaque rawBindBlob : @& RawStmtHandle → UInt32 → @& ByteArray → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_column_count"]
private opaque rawColumnCount : @& RawStmtHandle → BaseIO (UInt32 × String × UInt32)

@[extern "leanswe_sqlite_column_type"]
private opaque rawColumnType : @& RawStmtHandle → UInt32 → BaseIO (UInt32 × String × UInt32)

@[extern "leanswe_sqlite_column_int64"]
private opaque rawColumnInt64 : @& RawStmtHandle → UInt32 → BaseIO (UInt32 × String × Int64)

@[extern "leanswe_sqlite_column_double"]
private opaque rawColumnDouble : @& RawStmtHandle → UInt32 → BaseIO (UInt32 × String × Float)

@[extern "leanswe_sqlite_column_text_bytes"]
private opaque rawColumnTextBytes : @& RawStmtHandle → UInt32 → BaseIO (UInt32 × String × ByteArray)

@[extern "leanswe_sqlite_column_blob"]
private opaque rawColumnBlob : @& RawStmtHandle → UInt32 → BaseIO (UInt32 × String × ByteArray)

private structure StmtLockSlot where
  sh : StmtHandle
  mu : Std.BaseMutex
  pins : Nat

private structure RawHandleState where
  table : RawHandleTable RawDbHandle RawStmtHandle := {}
  stmtLocks : List StmtLockSlot := []
  deriving Inhabited

private initialize gHandleTable : Std.Mutex RawHandleState ← Std.Mutex.new {}

private def pinExistingStmtLock (sh : StmtHandle) (acc : List StmtLockSlot) :
    List StmtLockSlot → Option (Std.BaseMutex × List StmtLockSlot)
  | [] => none
  | slot :: rest =>
    if slot.sh == sh then
      some (slot.mu, acc.reverse ++ ({ slot with pins := slot.pins + 1 } :: rest))
    else
      pinExistingStmtLock sh (slot :: acc) rest

private def unpinStmtLockAux (live : List (StmtHandle × RawStmtHandle))
    (sh : StmtHandle) (acc : List StmtLockSlot) :
    List StmtLockSlot → Option Std.BaseMutex × List StmtLockSlot
  | [] => (none, acc.reverse)
  | slot :: rest =>
    if slot.sh == sh then
      let pins' := slot.pins - 1
      let keep := pins' > 0 || (Internal.lookupRawStmt sh live).isSome
      let locks' :=
        if keep then acc.reverse ++ ({ slot with pins := pins' } :: rest)
        else acc.reverse ++ rest
      (some slot.mu, locks')
    else
      unpinStmtLockAux live sh (slot :: acc) rest

private def filterLiveLocksAux (live : List (StmtHandle × RawStmtHandle))
    (acc : List StmtLockSlot) : List StmtLockSlot → List StmtLockSlot
  | [] => acc.reverse
  | slot :: rest =>
    if slot.pins > 0 || (Internal.lookupRawStmt slot.sh live).isSome then
      filterLiveLocksAux live (slot :: acc) rest
    else
      filterLiveLocksAux live acc rest

private def acquireStmtLock (sh : StmtHandle) : IO Bool := do
  let fastRes ← gHandleTable.atomically do
    let st ← get
    match pinExistingStmtLock sh [] st.stmtLocks with
    | some (mu, locks') =>
      set { st with stmtLocks := locks' }
      return some (some mu)
    | none =>
      if (Internal.lookupRawStmt sh st.table.stmts).isSome then
        return some none
      else
        return none
  let mu? ←
    match fastRes with
    | none => pure none
    | some (some mu) => pure (some mu)
    | some none =>
      let newMu ← liftM (m := BaseIO) Std.BaseMutex.new
      gHandleTable.atomically do
        let st ← get
        match pinExistingStmtLock sh [] st.stmtLocks with
        | some (mu, locks') =>
          set { st with stmtLocks := locks' }
          return some mu
        | none =>
          if (Internal.lookupRawStmt sh st.table.stmts).isSome then
            set { st with stmtLocks := { sh := sh, mu := newMu, pins := 1 } :: st.stmtLocks }
            return some newMu
          else
            return none
  match mu? with
  | some mu =>
    liftM (m := BaseIO) mu.lock
    return true
  | none =>
    return false

private def releaseStmtLock (sh : StmtHandle) : IO Unit := do
  let mu? ← gHandleTable.atomically do
    let st ← get
    let (mu?, locks') := unpinStmtLockAux st.table.stmts sh [] st.stmtLocks
    set { st with stmtLocks := locks' }
    return mu?
  match mu? with
  | some mu => liftM (m := BaseIO) mu.unlock
  | none => pure ()

private def mapUnitRc (act : BaseIO (UInt32 × String)) : IO (Except SqliteRawError Unit) :=
  liftM do
    let (rc, msg) ← act
    if rc == 0 then
      return .ok ()
    else
      return .error (Internal.classifyRawCode none rc msg)

private def mapValRc {α : Type} (act : BaseIO (UInt32 × String × α)) : IO (Except SqliteRawError α) :=
  liftM do
    let (rc, msg, val) ← act
    if rc == 0 then
      return .ok val
    else
      return .error (Internal.classifyRawCode none rc msg)

private def cSqliteOps : CSqliteOps :=
  { modifyTable := fun f =>
      liftM (m := BaseIO) <| gHandleTable.atomically do
        let s ← get
        let (a, t') := f s.table
        let locks' := filterLiveLocksAux t'.stmts [] s.stmtLocks
        set ({ table := t', stmtLocks := locks' } : RawHandleState)
        return a
    openV2 := fun path flags =>
      liftM do
        let (rc, msg, ptr?) ← rawOpenV2 path flags
        if rc != 0 then
          return .error (Internal.classifyRawCode (some path) rc msg)
        else
          match ptr? with
          | some ptr => return .ok ptr
          | none => return .error (Internal.classifyRawCode (some path) 14 "sqlite3_open_v2 returned null handle")
    close := fun db => mapUnitRc (rawClose db)
    extendedResultCodes := fun db onoff => mapUnitRc (rawExtendedResultCodes db (if onoff then 1 else 0))
    busyTimeout := fun db ms => mapUnitRc (rawBusyTimeout db ms)
    prepareV2 := fun db sql =>
      liftM do
        let (rc, msg, stmtPtr?, consumed) ← rawPrepareV2 db sql
        if rc != 0 then
          return .error (Internal.classifyRawCode none rc msg)
        else
          return .ok (stmtPtr?, consumed)
    step := fun stmt =>
      liftM do
        let (rc, msg, tag) ← rawStep stmt
        if rc != 0 then
          return .error (Internal.classifyRawCode none rc msg)
        else if tag == 0 then
          return .ok .done
        else
          return .ok .row
    reset := fun stmt => mapUnitRc (rawReset stmt)
    clearBindings := fun stmt => mapUnitRc (rawClearBindings stmt)
    finalize := fun stmt =>
      liftM do
        let (consumedFlag, rc, msg) ← rawFinalize stmt
        if consumedFlag == 0 then
          return .rejected (Internal.classifyRawCode none rc msg)
        else if rc == 0 then
          return .finalized none
        else
          return .finalized (some (Internal.classifyRawCode none rc msg))
    bindParamCount := fun stmt => mapValRc (rawBindParamCount stmt)
    bindNull := fun stmt idx => mapUnitRc (rawBindNull stmt idx)
    bindInt64 := fun stmt idx v => mapUnitRc (rawBindInt64 stmt idx v)
    bindDouble := fun stmt idx d => mapUnitRc (rawBindDouble stmt idx d)
    bindText := fun stmt idx s => mapUnitRc (rawBindText stmt idx s)
    bindBlob := fun stmt idx b => mapUnitRc (rawBindBlob stmt idx b)
    columnCount := fun stmt => mapValRc (rawColumnCount stmt)
    columnType := fun stmt col => mapValRc (rawColumnType stmt col)
    columnInt64 := fun stmt col => mapValRc (rawColumnInt64 stmt col)
    columnDouble := fun stmt col => mapValRc (rawColumnDouble stmt col)
    columnTextBytes := fun stmt col => mapValRc (rawColumnTextBytes stmt col)
    columnBlob := fun stmt col => mapValRc (rawColumnBlob stmt col)
    lockStmt := fun {_} sh => acquireStmtLock sh
    unlockStmt := fun {_} sh => releaseStmtLock sh }

/-- Default single-step SQLite operations backed by `c/sqlite_shim.c` and vendored SQLite3. -/
def defaultOps : RawSqliteOps :=
  Internal.mkRawOps cSqliteOps

/-- Default high-level `SqliteApi` backed by `defaultOps`. -/
def defaultApi : SqliteApi :=
  Internal.mkApiM defaultOps

/-- Convert a raw SQLite error record into a normalized `SqliteError` with non-empty message. -/
@[inline] def mapRawError (err : SqliteRawError) : SqliteError :=
  defaultApi.mapRawError err

/-- Validate an `OpenConfig` before opening a connection. -/
@[inline] def validateConfig (cfg : OpenConfig) : Except SqliteError Unit :=
  defaultApi.validateConfig cfg

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
