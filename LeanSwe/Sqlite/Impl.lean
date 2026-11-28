import LeanSwe.Sqlite.Types
import LeanSwe.Sqlite.Impl.UriAndSql

namespace LeanSwe.Sqlite.Internal

open LeanSwe.Sqlite
  (SqliteError SqliteRawError SqliteValue SqliteRow maxBusyTimeoutMs maxSqlByteLen
   OpenConfig DbHandle StmtHandle StepResult RawHandleTable
   RawStepTag RawFinalizeResult CSqliteOpsM RawSqliteOpsM SqliteApiM)

/-- Look up `dbId` in `dbs`. -/
def lookupRawDb {dbH : Type} (dbId : UInt64) : List (UInt64 × dbH) → Option dbH
  | [] => none
  | (id, h) :: rest => if id == dbId then some h else lookupRawDb dbId rest

/-- Tail-recursive helper for `eraseRawDb`. -/
def eraseRawDbAux {dbH : Type} (dbId : UInt64) (acc : List (UInt64 × dbH)) :
    List (UInt64 × dbH) → List (UInt64 × dbH)
  | [] => acc.reverse
  | (id, h) :: rest =>
    if id == dbId then acc.reverse ++ rest
    else eraseRawDbAux dbId ((id, h) :: acc) rest

/-- Remove the first entry matching `dbId` from `dbs`. -/
def eraseRawDb {dbH : Type} (dbId : UInt64) (dbs : List (UInt64 × dbH)) : List (UInt64 × dbH) :=
  eraseRawDbAux dbId [] dbs

/-- Allocate a fresh `DbHandle` for `rawDb` in `t`. -/
def insertRawDb {dbH stmtH : Type} (rawDb : dbH) (t : RawHandleTable dbH stmtH) :
    DbHandle × RawHandleTable dbH stmtH :=
  let id := t.nextDbId
  ({ id := id }, { t with nextDbId := id + 1, dbs := (id, rawDb) :: t.dbs })

/-- Look up `stmt` (matching both `id` and `dbId`) in `stmts`. -/
def lookupRawStmt {stmtH : Type} (stmt : StmtHandle) : List (StmtHandle × stmtH) → Option stmtH
  | [] => none
  | (sh, h) :: rest => if sh == stmt then some h else lookupRawStmt stmt rest

/-- Tail-recursive helper for `eraseRawStmt`. -/
def eraseRawStmtAux {stmtH : Type} (stmt : StmtHandle) (acc : List (StmtHandle × stmtH)) :
    List (StmtHandle × stmtH) → List (StmtHandle × stmtH)
  | [] => acc.reverse
  | (sh, h) :: rest =>
    if sh == stmt then acc.reverse ++ rest
    else eraseRawStmtAux stmt ((sh, h) :: acc) rest

/-- Remove the first entry matching `stmt` from `stmts`. -/
def eraseRawStmt {stmtH : Type} (stmt : StmtHandle) (stmts : List (StmtHandle × stmtH)) :
    List (StmtHandle × stmtH) :=
  eraseRawStmtAux stmt [] stmts

/-- Allocate a fresh `StmtHandle` associated with `dbId` for `rawStmt` in `t`. -/
def insertRawStmt {dbH stmtH : Type} (dbId : UInt64) (rawStmt : stmtH)
    (t : RawHandleTable dbH stmtH) : StmtHandle × RawHandleTable dbH stmtH :=
  let id := t.nextStmtId
  let sh : StmtHandle := { id := id, dbId := dbId }
  (sh, { t with nextStmtId := id + 1, stmts := (sh, rawStmt) :: t.stmts })

/-- Return `true` iff `stmts` contains an active statement belonging to `dbId`. -/
def hasActiveStmtForDb {stmtH : Type} (dbId : UInt64) : List (StmtHandle × stmtH) → Bool
  | [] => false
  | (sh, _) :: rest => sh.dbId == dbId || hasActiveStmtForDb dbId rest

/-- Step a prepared `PRAGMA` statement until `.done` with bounded fuel. -/
def stepPragmaLoop {m : Type → Type} [Monad m] {dbH stmtH : Type}
    (cops : CSqliteOpsM m dbH stmtH) (rawStmt : stmtH) :
    Nat → m (Except SqliteRawError Unit)
  | 0 => pure (.error (.userError "sqlite pragma step limit exceeded"))
  | fuel + 1 => do
    match ← cops.step rawStmt with
    | .error e => pure (.error e)
    | .ok .done => pure (.ok ())
    | .ok .row => stepPragmaLoop cops rawStmt fuel

/-- Prepare, step to completion, and always finalize a connection-setup `PRAGMA` statement. -/
def runSetupPragma {m : Type → Type} [Monad m] [MonadFinally m] {dbH stmtH : Type}
    (cops : CSqliteOpsM m dbH stmtH) (rawDb : dbH) (pragmaSql : String) :
    m (Except SqliteRawError Unit) := do
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
def setupConnection {m : Type → Type} [Monad m] [MonadFinally m] {dbH stmtH : Type}
    (cops : CSqliteOpsM m dbH stmtH) (path : String) (cfg : OpenConfig) (rawDb : dbH) :
    m (Except SqliteRawError Unit) := do
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
def bindOneParam {m : Type → Type} {dbH stmtH : Type}
    (cops : CSqliteOpsM m dbH stmtH) (rawStmt : stmtH) (paramIdx : UInt32) :
    SqliteValue → m (Except SqliteRawError Unit)
  | .null => cops.bindNull rawStmt paramIdx
  | .int v => cops.bindInt64 rawStmt paramIdx v
  | .real d => cops.bindDouble rawStmt paramIdx d
  | .text s => cops.bindText rawStmt paramIdx s
  | .bytes b => cops.bindBlob rawStmt paramIdx b

/-- Bind all parameters in `params` (`1`-indexed in SQLite) sequentially. -/
def bindLoop {m : Type → Type} [Monad m] {dbH stmtH : Type}
    (cops : CSqliteOpsM m dbH stmtH) (rawStmt : stmtH)
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
def decodeColumns {m : Type → Type} [Monad m] {dbH stmtH : Type}
    (cops : CSqliteOpsM m dbH stmtH) (rawStmt : stmtH) (total : Nat) :
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
def withStmtLock {m : Type → Type} [Monad m] [MonadFinally m] {dbH stmtH : Type}
    (cops : CSqliteOpsM m dbH stmtH) {α : Type} (stmt : StmtHandle) (act : m α) : m α := do
  let locked ← cops.lockStmt stmt
  let (res, _) ← tryFinally' act (fun _ => if locked then cops.unlockStmt stmt else pure ())
  pure res

/-- Construct a monad-generic `RawSqliteOpsM m` over thin 1-call `CSqliteOpsM m dbH stmtH` hooks,
    enforcing all open-flag, URI, PRAGMA, single-statement comment/tail, handle-table, and UTF-8 policies in Lean. -/
def mkRawOps {m : Type → Type} [Monad m] [MonadFinally m] {dbH stmtH : Type}
    (cops : CSqliteOpsM m dbH stmtH) : RawSqliteOpsM m :=
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

/-- Maximum statement step iterations before reporting step limit failure. -/
def maxStepFuel : Nat := 100000000

/-- Validate `OpenConfig` using `mapRaw` to produce typed `SqliteError` diagnostics. -/
def validateConfigWith (mapRaw : SqliteRawError → SqliteError) (cfg : OpenConfig) :
    Except SqliteError Unit :=
  if cfg.readOnly && cfg.createIfMissing then
    .error (mapRaw (.invalidArgument "cannot combine readOnly = true with createIfMissing = true"))
  else if cfg.busyTimeoutMs > maxBusyTimeoutMs then
    .error (mapRaw (.invalidArgument
      s!"busyTimeoutMs {cfg.busyTimeoutMs} exceeds maxBusyTimeoutMs ({maxBusyTimeoutMs})"))
  else
    .ok ()

/-- Step a prepared statement to completion, ignoring yielded rows. -/
def execLoop {m : Type → Type} [Monad m] (ops : RawSqliteOpsM m) (stmt : StmtHandle) :
    Nat → m (Except SqliteError Unit)
  | 0 => pure (.error (ops.mapRawError (.ioFailure 0 "sqlite statement step limit exceeded")))
  | fuel + 1 => do
    match ← ops.step stmt with
    | .error e => pure (.error e)
    | .ok .done => pure (.ok ())
    | .ok (.row _) => execLoop ops stmt fuel

/-- Prepare, optionally bind `params?`, step to completion, and always finalize a statement. -/
def execMaybeBindOp {m : Type → Type} [Monad m] [MonadFinally m] (ops : RawSqliteOpsM m)
    (db : DbHandle) (sql : String) (params? : Option (Array SqliteValue)) :
    m (Except SqliteError Unit) := do
  match ← ops.prepare db sql with
  | .error e => pure (.error e)
  | .ok stmt =>
    let (res, finRes) ← tryFinally' (do
      match params? with
      | none => execLoop ops stmt maxStepFuel
      | some params =>
        match ← ops.bind stmt params with
        | .error e => pure (.error e)
        | .ok () => execLoop ops stmt maxStepFuel) (fun _ => ops.finalize stmt)
    match res with
    | .error e => pure (.error e)
    | .ok () =>
      match finRes with
      | .error e => pure (.error e)
      | .ok () => pure (.ok ())

/-- Prepare, bind, step to completion, and always finalize a non-query statement. -/
def execOp {m : Type → Type} [Monad m] [MonadFinally m] (ops : RawSqliteOpsM m)
    (db : DbHandle) (sql : String) (params : Array SqliteValue) : m (Except SqliteError Unit) :=
  execMaybeBindOp ops db sql (some params)

/-- Step a prepared query statement, collecting decoded rows in order. -/
def queryLoop {m : Type → Type} [Monad m] (ops : RawSqliteOpsM m)
    (stmt : StmtHandle) (acc : Array SqliteRow) :
    Nat → m (Except SqliteError (Array SqliteRow))
  | 0 => pure (.error (ops.mapRawError (.ioFailure 0 "sqlite query row limit exceeded")))
  | fuel + 1 => do
    match ← ops.step stmt with
    | .error e => pure (.error e)
    | .ok .done => pure (.ok acc)
    | .ok (.row cols) => queryLoop ops stmt (acc.push cols) fuel

/-- Prepare, bind, collect all rows, and always finalize a query statement. -/
def queryOp {m : Type → Type} [Monad m] [MonadFinally m] (ops : RawSqliteOpsM m)
    (db : DbHandle) (sql : String) (params : Array SqliteValue) :
    m (Except SqliteError (Array SqliteRow)) := do
  match ← ops.prepare db sql with
  | .error e => pure (.error e)
  | .ok stmt =>
    let (res, finRes) ← tryFinally' (do
      match ← ops.bind stmt params with
      | .error e => pure (.error e)
      | .ok () => queryLoop ops stmt #[] maxStepFuel) (fun _ => ops.finalize stmt)
    match res with
    | .error e => pure (.error e)
    | .ok rows =>
      match finRes with
      | .error e => pure (.error e)
      | .ok () => pure (.ok rows)

/-- Prepare, bind, read at most one row, and always finalize a query statement. -/
def queryOneOp {m : Type → Type} [Monad m] [MonadFinally m] (ops : RawSqliteOpsM m)
    (db : DbHandle) (sql : String) (params : Array SqliteValue) :
    m (Except SqliteError (Option SqliteRow)) := do
  match ← ops.prepare db sql with
  | .error e => pure (.error e)
  | .ok stmt =>
    let (res, finRes) ← tryFinally' (do
      match ← ops.bind stmt params with
      | .error e => pure (Except.error e)
      | .ok () =>
        match ← ops.step stmt with
        | .error e => pure (Except.error e)
        | .ok .done => pure (Except.ok none)
        | .ok (.row cols) => pure (Except.ok (some cols))) (fun _ => ops.finalize stmt)
    match res with
    | .error e => pure (.error e)
    | .ok row? =>
      match finRes with
      | .error e => pure (.error e)
      | .ok () => pure (.ok row?)

/-- Open a database after config validation, run `action`, and always close the handle. -/
def withDbOp {m : Type → Type} [Monad m] [MonadFinally m] (ops : RawSqliteOpsM m) {α : Type}
    (path : String) (cfg : OpenConfig) (action : DbHandle → m (Except SqliteError α)) :
    m (Except SqliteError α) := do
  match validateConfigWith ops.mapRawError cfg with
  | .error e => pure (.error e)
  | .ok () =>
    match ← ops.openDb path cfg with
    | .error e => pure (.error e)
    | .ok db =>
      let (res, closeRes) ← tryFinally' (action db) (fun _ => ops.closeDb db)
      match res with
      | .error e => pure (.error e)
      | .ok a =>
        match closeRes with
        | .error e => pure (.error e)
        | .ok () => pure (.ok a)

/-- Run `action` inside `BEGIN IMMEDIATE` / `COMMIT`, rolling back on action or commit error. -/
def withTransactionOp {m : Type → Type} [Monad m] [MonadFinally m] (ops : RawSqliteOpsM m) {α : Type}
    (db : DbHandle) (action : DbHandle → m (Except SqliteError α)) :
    m (Except SqliteError α) := do
  match ← execMaybeBindOp ops db "BEGIN IMMEDIATE" none with
  | .error e => pure (.error e)
  | .ok () =>
    let (res, finRes) ← tryFinally' (action db) fun
      | some (.ok _) => execMaybeBindOp ops db "COMMIT" none
      | _ => execMaybeBindOp ops db "ROLLBACK" none
    match res with
    | .error e => pure (.error e)
    | .ok a =>
      match finRes with
      | .ok () => pure (.ok a)
      | .error e =>
        let _ ← execMaybeBindOp ops db "ROLLBACK" none
        pure (.error e)

/-- Construct a monad-generic `SqliteApiM m` over `ops : RawSqliteOpsM m`. -/
def mkApiM {m : Type → Type} [Monad m] [MonadFinally m] (ops : RawSqliteOpsM m) : SqliteApiM m :=
  { mapRawError := ops.mapRawError
    validateConfig := validateConfigWith ops.mapRawError
    withDb := fun path cfg action => withDbOp ops path cfg action
    withTransaction := fun db action => withTransactionOp ops db action
    exec := execOp ops
    query := queryOp ops
    queryOne := queryOneOp ops
    activeDbCount := ops.activeDbCount
    activeStmtCount := ops.activeStmtCount }

end LeanSwe.Sqlite.Internal
