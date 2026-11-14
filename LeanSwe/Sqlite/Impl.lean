import LeanSwe.Sqlite.Types

namespace LeanSwe.Sqlite.Internal

open LeanSwe.Sqlite
  (SqliteError SqliteRawError SqliteValue maxBusyTimeoutMs OpenConfig
   DbHandle StmtHandle RawSqliteOpsM SqliteRow SqliteApiM)

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
