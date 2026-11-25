import LeanSwe.Sqlite.Raw.Types
import LeanSwe.Sqlite.Raw.Impl.UriAndSql

namespace LeanSwe.Sqlite.Raw.Internal

open LeanSwe.Sqlite.Raw
  (SqliteError SqliteRawError SqliteValue maxBusyTimeoutMs maxSqlByteLen
   OpenConfig DbHandle StmtHandle StepResult RawDbHandle RawStmtHandle RawHandleTable
   RawStepTag RawFinalizeResult CSqliteOpsM RawSqliteOpsM)

/-- Look up `dbId` in `dbs`. -/
def lookupRawDb (dbId : UInt64) : List (UInt64 × RawDbHandle) → Option RawDbHandle
  | [] => none
  | (id, h) :: rest => if id == dbId then some h else lookupRawDb dbId rest

/-- Tail-recursive helper for `eraseRawDb`. -/
def eraseRawDbAux (dbId : UInt64) (acc : List (UInt64 × RawDbHandle)) :
    List (UInt64 × RawDbHandle) → List (UInt64 × RawDbHandle)
  | [] => acc.reverse
  | (id, h) :: rest =>
    if id == dbId then acc.reverse ++ rest
    else eraseRawDbAux dbId ((id, h) :: acc) rest

/-- Remove the first entry matching `dbId` from `dbs`. -/
def eraseRawDb (dbId : UInt64) (dbs : List (UInt64 × RawDbHandle)) : List (UInt64 × RawDbHandle) :=
  eraseRawDbAux dbId [] dbs

/-- Allocate a fresh `DbHandle` for `rawDb` in `t`. -/
def insertRawDb (rawDb : RawDbHandle) (t : RawHandleTable) : DbHandle × RawHandleTable :=
  let id := t.nextDbId
  ({ id := id }, { t with nextDbId := id + 1, dbs := (id, rawDb) :: t.dbs })

/-- Look up `stmt` (matching both `id` and `dbId`) in `stmts`. -/
def lookupRawStmt (stmt : StmtHandle) : List (StmtHandle × RawStmtHandle) → Option RawStmtHandle
  | [] => none
  | (sh, h) :: rest => if sh == stmt then some h else lookupRawStmt stmt rest

/-- Tail-recursive helper for `eraseRawStmt`. -/
def eraseRawStmtAux (stmt : StmtHandle) (acc : List (StmtHandle × RawStmtHandle)) :
    List (StmtHandle × RawStmtHandle) → List (StmtHandle × RawStmtHandle)
  | [] => acc.reverse
  | (sh, h) :: rest =>
    if sh == stmt then acc.reverse ++ rest
    else eraseRawStmtAux stmt ((sh, h) :: acc) rest

/-- Remove the first entry matching `stmt` from `stmts`. -/
def eraseRawStmt (stmt : StmtHandle) (stmts : List (StmtHandle × RawStmtHandle)) : List (StmtHandle × RawStmtHandle) :=
  eraseRawStmtAux stmt [] stmts

/-- Allocate a fresh `StmtHandle` associated with `dbId` for `rawStmt` in `t`. -/
def insertRawStmt (dbId : UInt64) (rawStmt : RawStmtHandle) (t : RawHandleTable) : StmtHandle × RawHandleTable :=
  let id := t.nextStmtId
  let sh : StmtHandle := { id := id, dbId := dbId }
  (sh, { t with nextStmtId := id + 1, stmts := (sh, rawStmt) :: t.stmts })

/-- Return `true` iff `stmts` contains an active statement belonging to `dbId`. -/
def hasActiveStmtForDb (dbId : UInt64) : List (StmtHandle × RawStmtHandle) → Bool
  | [] => false
  | (sh, _) :: rest => sh.dbId == dbId || hasActiveStmtForDb dbId rest

/-- Step a prepared `PRAGMA` statement until `.done` with bounded fuel. -/
def stepPragmaLoop {m : Type → Type} [Monad m] (cops : CSqliteOpsM m) (rawStmt : RawStmtHandle) :
    Nat → m (Except SqliteRawError Unit)
  | 0 => pure (.error (.userError "sqlite pragma step limit exceeded"))
  | fuel + 1 => do
    match ← cops.step rawStmt with
    | .error e => pure (.error e)
    | .ok .done => pure (.ok ())
    | .ok .row => stepPragmaLoop cops rawStmt fuel

/-- Prepare, step to completion, and always finalize a connection-setup `PRAGMA` statement. -/
def runSetupPragma {m : Type → Type} [Monad m] [MonadFinally m] (cops : CSqliteOpsM m)
    (rawDb : RawDbHandle) (pragmaSql : String) : m (Except SqliteRawError Unit) := do
  match ← cops.prepareV2 rawDb pragmaSql with
  | .error e => pure (.error e)
  | .ok (none, _) => pure (.error (.misuse 21 "empty pragma SQL statement"))
  | .ok (some rawStmt, _) =>
    let (stepRes, finOut) ← tryFinally' (stepPragmaLoop cops rawStmt 4) (fun _ => cops.finalize rawStmt)
    match stepRes with
    | .error e => pure (.error e)
    | .ok () =>
      match finOut with
      | .finalized none => pure (.ok ())
      | .finalized (some e) => pure (.error e)
      | .rejected e => pure (.error e)

/-- Run post-`openV2` connection setup (`extendedResultCodes`, `busyTimeout`, `foreign_keys`, and conditional `WAL`). -/
def setupConnection {m : Type → Type} [Monad m] [MonadFinally m] (cops : CSqliteOpsM m)
    (path : String) (cfg : OpenConfig) (rawDb : RawDbHandle) : m (Except SqliteRawError Unit) := do
  match ← cops.extendedResultCodes rawDb true with
  | .error e => pure (.error e)
  | .ok () =>
    match ← cops.busyTimeout rawDb (UInt32.ofNat cfg.busyTimeoutMs) with
    | .error e => pure (.error e)
    | .ok () =>
      let fkRes : Except SqliteRawError Unit ←
        if cfg.foreignKeys then
          runSetupPragma cops rawDb "PRAGMA foreign_keys = ON;"
        else
          pure (.ok ())
      match fkRes with
      | .error e => pure (.error e)
      | .ok () =>
        if shouldEnableWal path cfg then
          runSetupPragma cops rawDb "PRAGMA journal_mode = WAL;"
        else
          pure (.ok ())

/-- Bind a single `SqliteValue` at 1-based parameter index `paramIdx`. -/
def bindOneParam {m : Type → Type} (cops : CSqliteOpsM m) (rawStmt : RawStmtHandle) (paramIdx : UInt32) :
    SqliteValue → m (Except SqliteRawError Unit)
  | .null => cops.bindNull rawStmt paramIdx
  | .int v => cops.bindInt64 rawStmt paramIdx v
  | .real d => cops.bindDouble rawStmt paramIdx d
  | .text s => cops.bindText rawStmt paramIdx s
  | .bytes b => cops.bindBlob rawStmt paramIdx b

/-- Bind all parameters in `params` (`1`-indexed in SQLite) sequentially. -/
def bindLoop {m : Type → Type} [Monad m] (cops : CSqliteOpsM m) (rawStmt : RawStmtHandle)
    (params : Array SqliteValue) : Nat → m (Except SqliteError Unit)
  | 0 => pure (.ok ())
  | rem + 1 => do
    let idx := params.size - (rem + 1)
    let param := params.getD idx .null
    match ← bindOneParam cops rawStmt (UInt32.ofNat (idx + 1)) param with
    | .error rawErr => pure (.error (mapRawError rawErr))
    | .ok () => bindLoop cops rawStmt params rem

/-- Decode result columns `0 ..< total` (`rem` columns remaining) from `rawStmt`,
    validating `SQLITE_TEXT` (`ty == 3`) bytes strictly via `String.fromUTF8?`. -/
def decodeColumns {m : Type → Type} [Monad m] (cops : CSqliteOpsM m)
    (rawStmt : RawStmtHandle) (total : Nat) :
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
      | .ok val => decodeColumns cops rawStmt total rem (acc.push val)

/-- Run `act` under `cops.lockStmt stmt`, always releasing via `cops.unlockStmt stmt` when acquired. -/
def withStmtLock {m : Type → Type} [Monad m] [MonadFinally m] (cops : CSqliteOpsM m)
    {α : Type} (stmt : StmtHandle) (act : m α) : m α := do
  let locked ← cops.lockStmt stmt
  let (res, _) ← tryFinally' act (fun _ => if locked then cops.unlockStmt stmt else pure ())
  pure res

/-- Construct a monad-generic `RawSqliteOpsM m` over thin 1-call `CSqliteOpsM m` hooks,
    enforcing all open-flag, URI, PRAGMA, single-statement comment/tail, handle-table, and UTF-8 policies in Lean. -/
def mkRawOps {m : Type → Type} [Monad m] [MonadFinally m] (cops : CSqliteOpsM m) : RawSqliteOpsM m :=
  { mapRawError := mapRawError
    openDb := fun path cfg => do
      let pathBytes := path.toUTF8
      if pathBytes.size == 0 then
        pure (.error (mapRawError (.invalidArgument "database path must not be empty")))
      else if hasZeroByteBa pathBytes 0 then
        pure (.error (mapRawError (.invalidArgument "database path contains embedded NUL byte")))
      else if cfg.readOnly && cfg.createIfMissing then
        pure (.error (mapRawError (.invalidArgument "cannot combine readOnly = true with createIfMissing = true")))
      else if cfg.busyTimeoutMs > maxBusyTimeoutMs then
        pure (.error (mapRawError (.invalidArgument
          s!"busyTimeoutMs {cfg.busyTimeoutMs} exceeds maxBusyTimeoutMs ({maxBusyTimeoutMs})")))
      else
        let flags := computeOpenFlags cfg
        match ← cops.openV2 path flags with
        | .error rawErr =>
          pure (.error (mapRawError (attachOpenPath path rawErr)))
        | .ok rawDb =>
          let (setupRes, _) ← tryFinally' (setupConnection cops path cfg rawDb) fun
            | some (.ok ()) => pure ()
            | _ => do
              let _ ← cops.close rawDb
              pure ()
          match setupRes with
          | .error rawErr =>
            pure (.error (mapRawError (attachOpenPath path rawErr)))
          | .ok () =>
            let db ← cops.modifyTable (insertRawDb rawDb)
            pure (.ok db)
    closeDb := fun db => do
      let lookupRes ← cops.modifyTable fun t =>
        match lookupRawDb db.id t.dbs with
        | none => (Except.error (.misuse 21 "invalid or closed database handle"), t)
        | some rawDb =>
          if hasActiveStmtForDb db.id t.stmts then
            (Except.error (.busy 5 "unable to close database due to unfinalized statements"), t)
          else
            (Except.ok rawDb, t)
      match lookupRes with
      | .error rawErr => pure (.error (mapRawError rawErr))
      | .ok rawDb =>
        match ← cops.close rawDb with
        | .error rawErr => pure (.error (mapRawError rawErr))
        | .ok () =>
          cops.modifyTable (fun t => ((), { t with dbs := eraseRawDb db.id t.dbs }))
          pure (.ok ())
    prepare := fun db sql => do
      if sql.utf8ByteSize > maxSqlByteLen then
        pure (.error (mapRawError (.invalidArgument "SQL statement exceeds maximum byte length")))
      else
        let sqlBytes := sql.toUTF8
        if hasZeroByteBa sqlBytes 0 then
          pure (.error (mapRawError (.invalidArgument "SQL string contains embedded NUL byte")))
        else
          let rawDb? ← cops.modifyTable (fun t => (lookupRawDb db.id t.dbs, t))
          match rawDb? with
          | none => pure (.error (mapRawError (.misuse 21 "invalid or closed database handle")))
          | some rawDb =>
            match ← cops.prepareV2 rawDb sql with
            | .error rawErr => pure (.error (mapRawError rawErr))
            | .ok (none, _) => pure (.error (mapRawError (.misuse 21 "empty SQL statement")))
            | .ok (some rawStmt, consumedByteLen) =>
              let totalBytes := sqlBytes.size
              let tailOk := consumedByteLen ≤ totalBytes &&
                scanSqlTailBa .normal sqlBytes consumedByteLen
              if !tailOk then
                let _ ← cops.finalize rawStmt
                pure (.error (mapRawError (.misuse 21 "multiple SQL statements are not allowed in prepare")))
              else
                let sh ← cops.modifyTable (insertRawStmt db.id rawStmt)
                pure (.ok sh)
    bind := fun stmt params =>
      withStmtLock cops stmt do
        let rawStmt? ← cops.modifyTable (fun t => (lookupRawStmt stmt t.stmts, t))
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
                  bindLoop cops rawStmt params params.size
    step := fun stmt =>
      withStmtLock cops stmt do
        let rawStmt? ← cops.modifyTable (fun t => (lookupRawStmt stmt t.stmts, t))
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
              let colsRes ← decodeColumns cops rawStmt cnt.toNat cnt.toNat #[]
              match colsRes with
              | .error err => pure (.error err)
              | .ok cols => pure (.ok (.row cols))
    finalize := fun stmt =>
      withStmtLock cops stmt do
        let rawStmt? ← cops.modifyTable (fun t => (lookupRawStmt stmt t.stmts, t))
        match rawStmt? with
        | none => pure (.error (mapRawError (.misuse 21 "invalid or already finalized statement handle")))
        | some rawStmt =>
          match ← cops.finalize rawStmt with
          | .finalized stickyErr? =>
            cops.modifyTable (fun t => ((), { t with stmts := eraseRawStmt stmt t.stmts }))
            match stickyErr? with
            | none => pure (.ok ())
            | some rawErr => pure (.error (mapRawError rawErr))
          | .rejected rawErr =>
            pure (.error (mapRawError rawErr))
    activeDbCount := cops.modifyTable (fun t => (t.dbs.length, t))
    activeStmtCount := cops.modifyTable (fun t => (t.stmts.length, t)) }

end LeanSwe.Sqlite.Raw.Internal
