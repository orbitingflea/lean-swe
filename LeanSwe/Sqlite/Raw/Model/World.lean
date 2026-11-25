import LeanSwe.Sqlite.Raw.Types

namespace LeanSwe.Sqlite.Raw.Model

open LeanSwe.Sqlite.Raw
  (SqliteRawError DbHandle StmtHandle RawDbHandle RawStmtHandle RawHandleTable
   RawStepTag RawFinalizeResult CSqliteOpsM)

/-- Look up `dbId` in `dbs`. -/
def lookupRawDbModel (dbId : UInt64) : List (UInt64 × RawDbHandle) → Option RawDbHandle
  | [] => none
  | (id, h) :: rest => if id == dbId then some h else lookupRawDbModel dbId rest

/-- Tail-recursive helper for `eraseRawDbModel`. -/
def eraseRawDbAuxModel (dbId : UInt64) (acc : List (UInt64 × RawDbHandle)) :
    List (UInt64 × RawDbHandle) → List (UInt64 × RawDbHandle)
  | [] => acc.reverse
  | (id, h) :: rest =>
    if id == dbId then acc.reverse ++ rest
    else eraseRawDbAuxModel dbId ((id, h) :: acc) rest

/-- Remove the first entry matching `dbId` from `dbs`. -/
def eraseRawDbModel (dbId : UInt64) (dbs : List (UInt64 × RawDbHandle)) : List (UInt64 × RawDbHandle) :=
  eraseRawDbAuxModel dbId [] dbs

/-- Allocate a fresh `DbHandle` for `rawDb` in `t`. -/
def insertRawDbModel (rawDb : RawDbHandle) (t : RawHandleTable) : DbHandle × RawHandleTable :=
  let id := t.nextDbId
  ({ id := id }, { t with nextDbId := id + 1, dbs := (id, rawDb) :: t.dbs })

/-- Look up `stmt` in `stmts`. -/
def lookupRawStmtModel (stmt : StmtHandle) : List (StmtHandle × RawStmtHandle) → Option RawStmtHandle
  | [] => none
  | (sh, h) :: rest => if sh == stmt then some h else lookupRawStmtModel stmt rest

/-- Tail-recursive helper for `eraseRawStmtModel`. -/
def eraseRawStmtAuxModel (stmt : StmtHandle) (acc : List (StmtHandle × RawStmtHandle)) :
    List (StmtHandle × RawStmtHandle) → List (StmtHandle × RawStmtHandle)
  | [] => acc.reverse
  | (sh, h) :: rest =>
    if sh == stmt then acc.reverse ++ rest
    else eraseRawStmtAuxModel stmt ((sh, h) :: acc) rest

/-- Remove the first entry matching `stmt` from `stmts`. -/
def eraseRawStmtModel (stmt : StmtHandle) (stmts : List (StmtHandle × RawStmtHandle)) :
    List (StmtHandle × RawStmtHandle) :=
  eraseRawStmtAuxModel stmt [] stmts

/-- Allocate a fresh `StmtHandle` associated with `dbId` for `rawStmt` in `t`. -/
def insertRawStmtModel (dbId : UInt64) (rawStmt : RawStmtHandle) (t : RawHandleTable) :
    StmtHandle × RawHandleTable :=
  let id := t.nextStmtId
  let sh : StmtHandle := { id := id, dbId := dbId }
  (sh, { t with nextStmtId := id + 1, stmts := (sh, rawStmt) :: t.stmts })

/-- Return `true` iff `stmts` contains an active statement belonging to `dbId`. -/
def hasActiveStmtForDbModel (dbId : UInt64) : List (StmtHandle × RawStmtHandle) → Bool
  | [] => false
  | (sh, _) :: rest => sh.dbId == dbId || hasActiveStmtForDbModel dbId rest

/-- Table transition allocating a new `DbHandle` for `rawDb`. -/
def tableInsertDb (rawDb : RawDbHandle) (t : RawHandleTable) : DbHandle × RawHandleTable :=
  insertRawDbModel rawDb t

/-- Table transition validating that `dbId` is open and has no active statements prior to `close`. -/
def tableCheckCloseDb (dbId : UInt64) (t : RawHandleTable) :
    Except SqliteRawError RawDbHandle × RawHandleTable :=
  match lookupRawDbModel dbId t.dbs with
  | none => (.error (.misuse 21 "invalid or closed database handle"), t)
  | some rawDb =>
    if hasActiveStmtForDbModel dbId t.stmts then
      (.error (.busy 5 "unable to close database due to unfinalized statements"), t)
    else
      (.ok rawDb, t)

/-- Table transition erasing closed `dbId`. -/
def tableEraseDb (dbId : UInt64) (t : RawHandleTable) : Unit × RawHandleTable :=
  ((), { t with dbs := eraseRawDbModel dbId t.dbs })

/-- Table transition looking up `dbId`. -/
def tableLookupDb (dbId : UInt64) (t : RawHandleTable) : Option RawDbHandle × RawHandleTable :=
  (lookupRawDbModel dbId t.dbs, t)

/-- Table transition allocating a new `StmtHandle` on `dbId`. -/
def tableInsertStmt (dbId : UInt64) (rawStmt : RawStmtHandle) (t : RawHandleTable) :
    StmtHandle × RawHandleTable :=
  insertRawStmtModel dbId rawStmt t

/-- Table transition looking up `stmt`. -/
def tableLookupStmt (stmt : StmtHandle) (t : RawHandleTable) : Option RawStmtHandle × RawHandleTable :=
  (lookupRawStmtModel stmt t.stmts, t)

/-- Table transition erasing finalized `stmt`. -/
def tableEraseStmt (stmt : StmtHandle) (t : RawHandleTable) : Unit × RawHandleTable :=
  ((), { t with stmts := eraseRawStmtModel stmt t.stmts })

/-- Table transition reading active DB handle count. -/
def tableActiveDbCount (t : RawHandleTable) : Nat × RawHandleTable :=
  (t.dbs.length, t)

/-- Table transition reading active statement handle count. -/
def tableActiveStmtCount (t : RawHandleTable) : Nat × RawHandleTable :=
  (t.stmts.length, t)

/-- Extract the deterministic token from `RawDbHandle` (`0` for `.ext`). -/
def rawDbTokenModel : RawDbHandle → UInt64
  | .mock tok => tok
  | .ext _ => 0

/-- Extract the deterministic token from `RawStmtHandle` (`0` for `.ext`). -/
def rawStmtTokenModel : RawStmtHandle → UInt64
  | .mock tok => tok
  | .ext _ => 0

/-- Raw C column cell stored in `SqliteRawState` for `column*` hooks. -/
inductive RawModelColumn where
  /-- `SQLITE_NULL` (`5`). -/
  | sqlNull
  /-- `SQLITE_INTEGER` (`1`) with 64-bit signed integer. -/
  | sqlInt (val : Int64)
  /-- `SQLITE_FLOAT` (`2`) with IEEE-754 double. -/
  | sqlDouble (val : Float)
  /-- `SQLITE_TEXT` (`3`) with raw unvalidated bytes. -/
  | sqlTextBytes (raw : ByteArray)
  /-- `SQLITE_BLOB` (`4`) with raw binary bytes. -/
  | sqlBlobBytes (raw : ByteArray)
  deriving BEq, Inhabited

/-- Deterministic state for single-step `CSqliteOpsM` and `RawSqliteOpsM` transitions. -/
structure SqliteRawState where
  /-- Lean-managed handle registry updated via `CSqliteOpsM.modifyTable`. -/
  table : RawHandleTable := {}
  /-- Next deterministic raw DB token (`100`-based). -/
  nextRawDbTok : UInt64 := 100
  /-- Next deterministic raw statement token (`200`-based). -/
  nextRawStmtTok : UInt64 := 200
  /-- Currently live C `sqlite3*` tokens allocated by `openV2` and not yet closed. -/
  liveRawDbs : List UInt64 := []
  /-- Currently live C `(dbTok, stmtTok)` pairs allocated by `prepareV2` and not yet finalized. -/
  liveRawStmts : List (UInt64 × UInt64) := []
  /-- Queued `RawStepTag` outcomes consumed sequentially by `step` (`.done` when empty). -/
  stepQueue : List RawStepTag := []
  /-- Expected `1`-based parameter count reported by `bindParamCount`. -/
  expectedBindParams : UInt32 := 0
  /-- Raw C columns exposed to `column*` hooks when `step` yields `.row`. -/
  columns : Array RawModelColumn := #[]
  /-- Currently held per-statement locks acquired by `lockStmt` and not yet released by `unlockStmt`. -/
  heldStmtLocks : List StmtHandle := []
  deriving Inhabited

/-- Remove the first occurrence of `sh` from `locks`. -/
def eraseStmtLockModel (sh : StmtHandle) : List StmtHandle → List StmtHandle
  | [] => []
  | k :: rest => if k == sh then rest else k :: eraseStmtLockModel sh rest

/-- Compute the byte count up to and including the first `';'` (`0x3B`) in `bs`, or `bs.length` if absent. -/
def consumedBytesUpToSemiModel : List UInt8 → Nat
  | [] => 0
  | b :: bs => if b == 0x3B then 1 else 1 + consumedBytesUpToSemiModel bs

/-- Return `true` iff `stmts` contains a live statement with raw statement token `stTok`. -/
def hasLiveRawStmtModel (stTok : UInt64) : List (UInt64 × UInt64) → Bool
  | [] => false
  | (_, s) :: rest => s == stTok || hasLiveRawStmtModel stTok rest

/-- Return `true` iff `stmts` contains a live statement belonging to raw DB token `dbTok`. -/
def hasLiveRawStmtForDbModel (dbTok : UInt64) : List (UInt64 × UInt64) → Bool
  | [] => false
  | (d, _) :: rest => d == dbTok || hasLiveRawStmtForDbModel dbTok rest

/-- Deterministic pure `CSqliteOpsM (StateM SqliteRawState)` model of thin `sqlite3_*` hooks. -/
def modelCSqliteOps : CSqliteOpsM (StateM SqliteRawState) :=
  { modifyTable := fun f s =>
      let (a, t') := f s.table
      (a, { s with table := t' })
    openV2 := fun _ _ s =>
      let tok := s.nextRawDbTok
      (.ok (.mock tok), { s with nextRawDbTok := tok + 1, liveRawDbs := s.liveRawDbs ++ [tok] })
    close := fun rawDb s =>
      let tok := rawDbTokenModel rawDb
      if !(s.liveRawDbs.contains tok) then
        (.error (.misuse 21 "raw database handle not open"), s)
      else if hasLiveRawStmtForDbModel tok s.liveRawStmts then
        (.error (.busy 5 "unable to close due to unfinalized statements"), s)
      else
        (.ok (), { s with liveRawDbs := s.liveRawDbs.filter (· != tok) })
    extendedResultCodes := fun rawDb _ s =>
      let tok := rawDbTokenModel rawDb
      if !(s.liveRawDbs.contains tok) then
        (.error (.misuse 21 "raw database handle not open"), s)
      else
        (.ok (), s)
    busyTimeout := fun rawDb _ s =>
      let tok := rawDbTokenModel rawDb
      if !(s.liveRawDbs.contains tok) then
        (.error (.misuse 21 "raw database handle not open"), s)
      else
        (.ok (), s)
    prepareV2 := fun rawDb sql s =>
      let dbTok := rawDbTokenModel rawDb
      if !(s.liveRawDbs.contains dbTok) then
        (.error (.misuse 21 "raw database handle not open"), s)
      else if sql.toList.isEmpty then
        (.ok (none, 0), s)
      else
        let stTok := s.nextRawStmtTok
        let consumed := consumedBytesUpToSemiModel sql.toUTF8.data.toList
        let extraQueue :=
          if sql.toList == "PRAGMA journal_mode = WAL;".toList && s.stepQueue.isEmpty then
            [.row, .done]
          else
            s.stepQueue
        (.ok (some (.mock stTok), consumed),
          { s with
            nextRawStmtTok := stTok + 1
            liveRawStmts := s.liveRawStmts ++ [(dbTok, stTok)]
            stepQueue := extraQueue })
    step := fun rawStmt s =>
      let stTok := rawStmtTokenModel rawStmt
      if !(hasLiveRawStmtModel stTok s.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s)
      else
        match s.stepQueue with
        | [] => (.ok .done, s)
        | tag :: rest => (.ok tag, { s with stepQueue := rest })
    reset := fun rawStmt s =>
      let stTok := rawStmtTokenModel rawStmt
      if !(hasLiveRawStmtModel stTok s.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s)
      else
        (.ok (), s)
    clearBindings := fun rawStmt s =>
      let stTok := rawStmtTokenModel rawStmt
      if !(hasLiveRawStmtModel stTok s.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s)
      else
        (.ok (), s)
    finalize := fun rawStmt s =>
      let stTok := rawStmtTokenModel rawStmt
      if !(hasLiveRawStmtModel stTok s.liveRawStmts) then
        (.rejected (.misuse 21 "raw statement handle already finalized"), s)
      else
        (.finalized none, { s with liveRawStmts := s.liveRawStmts.filter fun p => p.2 != stTok })
    bindParamCount := fun rawStmt s =>
      let stTok := rawStmtTokenModel rawStmt
      if !(hasLiveRawStmtModel stTok s.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s)
      else
        (.ok s.expectedBindParams, s)
    bindNull := fun rawStmt _ s =>
      let stTok := rawStmtTokenModel rawStmt
      if !(hasLiveRawStmtModel stTok s.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s)
      else
        (.ok (), s)
    bindInt64 := fun rawStmt _ _ s =>
      let stTok := rawStmtTokenModel rawStmt
      if !(hasLiveRawStmtModel stTok s.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s)
      else
        (.ok (), s)
    bindDouble := fun rawStmt _ _ s =>
      let stTok := rawStmtTokenModel rawStmt
      if !(hasLiveRawStmtModel stTok s.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s)
      else
        (.ok (), s)
    bindText := fun rawStmt _ _ s =>
      let stTok := rawStmtTokenModel rawStmt
      if !(hasLiveRawStmtModel stTok s.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s)
      else
        (.ok (), s)
    bindBlob := fun rawStmt _ _ s =>
      let stTok := rawStmtTokenModel rawStmt
      if !(hasLiveRawStmtModel stTok s.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s)
      else
        (.ok (), s)
    columnCount := fun rawStmt s =>
      let stTok := rawStmtTokenModel rawStmt
      if !(hasLiveRawStmtModel stTok s.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s)
      else
        (.ok (UInt32.ofNat s.columns.size), s)
    columnType := fun rawStmt col s =>
      let stTok := rawStmtTokenModel rawStmt
      if !(hasLiveRawStmtModel stTok s.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s)
      else
        let ty : UInt32 := match s.columns[col.toNat]? with
          | some .sqlNull => 5
          | some (.sqlInt _) => 1
          | some (.sqlDouble _) => 2
          | some (.sqlTextBytes _) => 3
          | some (.sqlBlobBytes _) => 4
          | none => 5
        (.ok ty, s)
    columnInt64 := fun rawStmt col s =>
      let stTok := rawStmtTokenModel rawStmt
      if !(hasLiveRawStmtModel stTok s.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s)
      else
        match s.columns[col.toNat]? with
        | some (.sqlInt v) => (.ok v, s)
        | _ => (.ok 0, s)
    columnDouble := fun rawStmt col s =>
      let stTok := rawStmtTokenModel rawStmt
      if !(hasLiveRawStmtModel stTok s.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s)
      else
        match s.columns[col.toNat]? with
        | some (.sqlDouble d) => (.ok d, s)
        | _ => (.ok 0.0, s)
    columnTextBytes := fun rawStmt col s =>
      let stTok := rawStmtTokenModel rawStmt
      if !(hasLiveRawStmtModel stTok s.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s)
      else
        match s.columns[col.toNat]? with
        | some (.sqlTextBytes bs) => (.ok bs, s)
        | _ => (.ok ByteArray.empty, s)
    columnBlob := fun rawStmt col s =>
      let stTok := rawStmtTokenModel rawStmt
      if !(hasLiveRawStmtModel stTok s.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s)
      else
        match s.columns[col.toNat]? with
        | some (.sqlBlobBytes bs) => (.ok bs, s)
        | _ => (.ok ByteArray.empty, s)
    lockStmt := fun {_} sh s =>
      if (lookupRawStmtModel sh s.table.stmts).isSome then
        (true, { s with heldStmtLocks := sh :: s.heldStmtLocks })
      else
        (false, s)
    unlockStmt := fun {_} sh s =>
      ((), { s with heldStmtLocks := eraseStmtLockModel sh s.heldStmtLocks }) }

end LeanSwe.Sqlite.Raw.Model
