import Std.Sync.Mutex
import LeanSwe.Sqlite.Raw.Types
import LeanSwe.Sqlite.Raw.Impl

namespace LeanSwe.Sqlite.Raw

@[extern "leanswe_sqlite_open_v2"]
private opaque rawOpenV2 : @& String → UInt32 → BaseIO (UInt32 × String × Option RawDbExt)

@[extern "leanswe_sqlite_close"]
private opaque rawClose : @& RawDbExt → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_extended_result_codes"]
private opaque rawExtendedResultCodes : @& RawDbExt → UInt8 → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_busy_timeout"]
private opaque rawBusyTimeout : @& RawDbExt → UInt32 → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_prepare_v2"]
private opaque rawPrepareV2 : @& RawDbExt → @& String → BaseIO (UInt32 × String × Option RawStmtExt × Nat)

@[extern "leanswe_sqlite_step"]
private opaque rawStep : @& RawStmtExt → BaseIO (UInt32 × String × UInt8)

@[extern "leanswe_sqlite_reset"]
private opaque rawReset : @& RawStmtExt → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_clear_bindings"]
private opaque rawClearBindings : @& RawStmtExt → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_finalize"]
private opaque rawFinalize : @& RawStmtExt → BaseIO (UInt8 × UInt32 × String)

@[extern "leanswe_sqlite_bind_param_count"]
private opaque rawBindParamCount : @& RawStmtExt → BaseIO (UInt32 × String × UInt32)

@[extern "leanswe_sqlite_bind_null"]
private opaque rawBindNull : @& RawStmtExt → UInt32 → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_bind_int64"]
private opaque rawBindInt64 : @& RawStmtExt → UInt32 → Int64 → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_bind_double"]
private opaque rawBindDouble : @& RawStmtExt → UInt32 → Float → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_bind_text"]
private opaque rawBindText : @& RawStmtExt → UInt32 → @& String → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_bind_blob"]
private opaque rawBindBlob : @& RawStmtExt → UInt32 → @& ByteArray → BaseIO (UInt32 × String)

@[extern "leanswe_sqlite_column_count"]
private opaque rawColumnCount : @& RawStmtExt → BaseIO (UInt32 × String × UInt32)

@[extern "leanswe_sqlite_column_type"]
private opaque rawColumnType : @& RawStmtExt → UInt32 → BaseIO (UInt32 × String × UInt32)

@[extern "leanswe_sqlite_column_int64"]
private opaque rawColumnInt64 : @& RawStmtExt → UInt32 → BaseIO (UInt32 × String × Int64)

@[extern "leanswe_sqlite_column_double"]
private opaque rawColumnDouble : @& RawStmtExt → UInt32 → BaseIO (UInt32 × String × Float)

@[extern "leanswe_sqlite_column_text_bytes"]
private opaque rawColumnTextBytes : @& RawStmtExt → UInt32 → BaseIO (UInt32 × String × ByteArray)

@[extern "leanswe_sqlite_column_blob"]
private opaque rawColumnBlob : @& RawStmtExt → UInt32 → BaseIO (UInt32 × String × ByteArray)

private structure StmtLockSlot where
  sh : StmtHandle
  mu : Std.BaseMutex
  pins : Nat

private structure RawHandleState where
  table : RawHandleTable := {}
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

private def withDbExt {α : Type} (h : RawDbHandle)
    (k : RawDbExt → BaseIO (Except SqliteRawError α)) : IO (Except SqliteRawError α) :=
  match h with
  | .ext ptr => liftM (k ptr)
  | .mock _ => pure (.error (.misuse 21 "invalid raw database handle"))

private def withStmtExt {α : Type} (h : RawStmtHandle)
    (k : RawStmtExt → BaseIO (Except SqliteRawError α)) : IO (Except SqliteRawError α) :=
  match h with
  | .ext ptr => liftM (k ptr)
  | .mock _ => pure (.error (.misuse 21 "invalid raw statement handle"))

private def mapUnitRc (act : BaseIO (UInt32 × String)) : BaseIO (Except SqliteRawError Unit) := do
  let (rc, msg) ← act
  if rc == 0 then
    return .ok ()
  else
    return .error (Internal.classifyRawCode none rc msg)

private def mapValRc {α : Type} (act : BaseIO (UInt32 × String × α)) : BaseIO (Except SqliteRawError α) := do
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
          | some ptr => return .ok (.ext ptr)
          | none => return .error (Internal.classifyRawCode (some path) 14 "sqlite3_open_v2 returned null handle")
    close := fun db => withDbExt db fun ptr => mapUnitRc (rawClose ptr)
    extendedResultCodes := fun db onoff =>
      withDbExt db fun ptr => mapUnitRc (rawExtendedResultCodes ptr (if onoff then 1 else 0))
    busyTimeout := fun db ms =>
      withDbExt db fun ptr => mapUnitRc (rawBusyTimeout ptr ms)
    prepareV2 := fun db sql =>
      withDbExt db fun ptr => do
        let (rc, msg, stmtPtr?, consumed) ← rawPrepareV2 ptr sql
        if rc != 0 then
          return .error (Internal.classifyRawCode none rc msg)
        else
          return .ok (stmtPtr?.map RawStmtHandle.ext, consumed)
    step := fun stmt =>
      withStmtExt stmt fun ptr => do
        let (rc, msg, tag) ← rawStep ptr
        if rc != 0 then
          return .error (Internal.classifyRawCode none rc msg)
        else if tag == 0 then
          return .ok .done
        else
          return .ok .row
    reset := fun stmt => withStmtExt stmt fun ptr => mapUnitRc (rawReset ptr)
    clearBindings := fun stmt => withStmtExt stmt fun ptr => mapUnitRc (rawClearBindings ptr)
    finalize := fun stmt =>
      match stmt with
      | .mock _ => pure (.rejected (.misuse 21 "invalid raw statement handle"))
      | .ext ptr =>
        liftM do
          let (consumedFlag, rc, msg) ← rawFinalize ptr
          if consumedFlag == 0 then
            return .rejected (Internal.classifyRawCode none rc msg)
          else if rc == 0 then
            return .finalized none
          else
            return .finalized (some (Internal.classifyRawCode none rc msg))
    bindParamCount := fun stmt => withStmtExt stmt fun ptr => mapValRc (rawBindParamCount ptr)
    bindNull := fun stmt idx => withStmtExt stmt fun ptr => mapUnitRc (rawBindNull ptr idx)
    bindInt64 := fun stmt idx v => withStmtExt stmt fun ptr => mapUnitRc (rawBindInt64 ptr idx v)
    bindDouble := fun stmt idx d => withStmtExt stmt fun ptr => mapUnitRc (rawBindDouble ptr idx d)
    bindText := fun stmt idx s => withStmtExt stmt fun ptr => mapUnitRc (rawBindText ptr idx s)
    bindBlob := fun stmt idx b => withStmtExt stmt fun ptr => mapUnitRc (rawBindBlob ptr idx b)
    columnCount := fun stmt => withStmtExt stmt fun ptr => mapValRc (rawColumnCount ptr)
    columnType := fun stmt col => withStmtExt stmt fun ptr => mapValRc (rawColumnType ptr col)
    columnInt64 := fun stmt col => withStmtExt stmt fun ptr => mapValRc (rawColumnInt64 ptr col)
    columnDouble := fun stmt col => withStmtExt stmt fun ptr => mapValRc (rawColumnDouble ptr col)
    columnTextBytes := fun stmt col => withStmtExt stmt fun ptr => mapValRc (rawColumnTextBytes ptr col)
    columnBlob := fun stmt col => withStmtExt stmt fun ptr => mapValRc (rawColumnBlob ptr col)
    lockStmt := fun {_} sh => acquireStmtLock sh
    unlockStmt := fun {_} sh => releaseStmtLock sh }

/-- Default single-step SQLite operations backed by `c/sqlite_shim.c` and vendored SQLite3. -/
def defaultOps : RawSqliteOps :=
  Internal.mkRawOps cSqliteOps

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
