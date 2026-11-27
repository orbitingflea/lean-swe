import Core.NondetTest
import LeanSwe.Sqlite.Types

namespace LeanSwe.Sqlite

open Core (NondetTest)
open Core.NondetTest

/-- Return the deterministic `UInt64` token for a mock database handle. -/
def rawDbToken (tok : UInt64) : UInt64 := tok

/-- Return the deterministic `UInt64` token for a mock statement handle. -/
def rawStmtToken (tok : UInt64) : UInt64 := tok

/-- Recorded thin-C hook invocation in `MockCState.calls`. -/
inductive MockCCall where
  /-- `openV2 path flags` -/
  | openV2 (path : String) (flags : UInt32)
  /-- `close rawDb` -/
  | close (dbTok : UInt64)
  /-- `extendedResultCodes rawDb onoff` -/
  | extendedResultCodes (dbTok : UInt64) (onoff : Bool)
  /-- `busyTimeout rawDb ms` -/
  | busyTimeout (dbTok : UInt64) (ms : UInt32)
  /-- `prepareV2 rawDb sql` -/
  | prepareV2 (dbTok : UInt64) (sql : String)
  /-- `step rawStmt` -/
  | step (stmtTok : UInt64)
  /-- `reset rawStmt` -/
  | reset (stmtTok : UInt64)
  /-- `clearBindings rawStmt` -/
  | clearBindings (stmtTok : UInt64)
  /-- `finalize rawStmt` -/
  | finalize (stmtTok : UInt64)
  /-- `bindParamCount rawStmt` -/
  | bindParamCount (stmtTok : UInt64)
  /-- `bindNull rawStmt idx` -/
  | bindNull (stmtTok : UInt64) (idx : UInt32)
  /-- `bindInt64 rawStmt idx val` -/
  | bindInt64 (stmtTok : UInt64) (idx : UInt32) (val : Int64)
  /-- `bindDouble rawStmt idx val` -/
  | bindDouble (stmtTok : UInt64) (idx : UInt32) (val : Float)
  /-- `bindText rawStmt idx val` -/
  | bindText (stmtTok : UInt64) (idx : UInt32) (val : String)
  /-- `bindBlob rawStmt idx val` -/
  | bindBlob (stmtTok : UInt64) (idx : UInt32) (val : ByteArray)
  /-- `columnCount rawStmt` -/
  | columnCount (stmtTok : UInt64)
  /-- `columnType rawStmt col` -/
  | columnType (stmtTok : UInt64) (col : UInt32)
  /-- `columnInt64 rawStmt col` -/
  | columnInt64 (stmtTok : UInt64) (col : UInt32)
  /-- `columnDouble rawStmt col` -/
  | columnDouble (stmtTok : UInt64) (col : UInt32)
  /-- `columnTextBytes rawStmt col` -/
  | columnTextBytes (stmtTok : UInt64) (col : UInt32)
  /-- `columnBlob rawStmt col` -/
  | columnBlob (stmtTok : UInt64) (col : UInt32)
  deriving BEq

/-- Raw C column cell returned by `mockCOps` during `step` row decoding. -/
inductive MockCColumn where
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
  deriving BEq

/-- Deterministic C-hook fault injection selector for `MockCState`. -/
inductive MockCFailStep where
  /-- All thin C hooks succeed normally. -/
  | none
  /-- `openV2` fails with `err`. -/
  | openV2 (err : SqliteRawError)
  /-- `close` fails with `err`. -/
  | close (err : SqliteRawError)
  /-- `extendedResultCodes` fails with `err`. -/
  | extendedResultCodes (err : SqliteRawError)
  /-- `busyTimeout` fails with `err`. -/
  | busyTimeout (err : SqliteRawError)
  /-- `prepareV2` fails on its `nth` (`0`-indexed) invocation with `err`. -/
  | prepareV2At (nth : Nat) (err : SqliteRawError)
  /-- `step` fails on its `nth` (`0`-indexed) invocation with `err`. -/
  | stepAt (nth : Nat) (err : SqliteRawError)
  /-- `reset` fails with `err`. -/
  | reset (err : SqliteRawError)
  /-- `clearBindings` fails with `err`. -/
  | clearBindings (err : SqliteRawError)
  /-- `bindParamCount` fails with `err`. -/
  | bindParamCount (err : SqliteRawError)
  /-- `bind*` fails on `1`-based parameter `paramIdx` with `err`. -/
  | bindAt (paramIdx : UInt32) (err : SqliteRawError)
  /-- `columnCount` fails with `err`. -/
  | columnCount (err : SqliteRawError)
  /-- `columnType` fails on `0`-based column `colIdx` with `err`. -/
  | columnType (colIdx : UInt32) (err : SqliteRawError)
  /-- `columnInt64` fails on `0`-based column `colIdx` with `err`. -/
  | columnInt64 (colIdx : UInt32) (err : SqliteRawError)
  /-- `columnDouble` fails on `0`-based column `colIdx` with `err`. -/
  | columnDouble (colIdx : UInt32) (err : SqliteRawError)
  /-- `columnTextBytes` fails on `0`-based column `colIdx` with `err`. -/
  | columnTextBytes (colIdx : UInt32) (err : SqliteRawError)
  /-- `columnBlob` fails on `0`-based column `colIdx` with `err`. -/
  | columnBlob (colIdx : UInt32) (err : SqliteRawError)
  /-- `finalize` returns `out` instead of `.finalized none`. -/
  | finalizeResult (out : RawFinalizeResult)
  deriving Repr, BEq, DecidableEq

/-- Pure deterministic state for testing `Internal.mkRawOps` over `CSqliteOpsM (StateM MockCState) UInt64 UInt64`. -/
structure MockCState where
  /-- Lean-managed handle table updated via `CSqliteOpsM.modifyTable`. -/
  table : RawHandleTable UInt64 UInt64 := {}
  /-- Next deterministic raw DB token (`100`-based). -/
  nextRawDbTok : UInt64 := 100
  /-- Next deterministic raw statement token (`200`-based). -/
  nextRawStmtTok : UInt64 := 200
  /-- Currently live C `sqlite3*` tokens allocated by `openV2` and not yet closed. -/
  liveRawDbs : List UInt64 := []
  /-- Currently live C `(dbTok, stmtTok)` pairs allocated by `prepareV2` and not yet finalized. -/
  liveRawStmts : List (UInt64 × UInt64) := []
  /-- Chronological log of thin C hook calls. -/
  calls : List MockCCall := []
  /-- Number of `prepareV2` calls executed so far. -/
  prepareCount : Nat := 0
  /-- Number of `step` calls executed so far. -/
  stepCount : Nat := 0
  /-- Optional override `(allocStmt, consumedByteLen)` for `prepareV2`. -/
  prepareOverride? : Option (Bool × Nat) := none
  /-- Queued `RawStepTag` outcomes consumed sequentially by `step` (`.done` when empty). -/
  stepQueue : List RawStepTag := []
  /-- Expected `1`-based parameter count reported by `bindParamCount`. -/
  expectedBindParams : UInt32 := 0
  /-- Raw C columns exposed to `column*` hooks when `step` yields `.row`. -/
  mockColumns : Array MockCColumn := #[]
  /-- Active fault-injection selector. -/
  failStep : MockCFailStep := .none

/-- Compute the byte count up to and including the first `';'` (`0x3B`) in `bs`, or `bs.length` if absent. -/
def mockConsumedBytesUpToSemi : List UInt8 → Nat
  | [] => 0
  | b :: bs =>
    if b == 0x3B then
      1
    else
      1 + mockConsumedBytesUpToSemi bs

/-- Return `true` iff `stmts` contains a live statement with raw statement token `stTok`. -/
def hasLiveRawStmt (stTok : UInt64) : List (UInt64 × UInt64) → Bool
  | [] => false
  | (_, s) :: rest => s == stTok || hasLiveRawStmt stTok rest

/-- Return `true` iff `stmts` contains a live statement belonging to raw DB token `dbTok`. -/
def hasLiveRawStmtForDb (dbTok : UInt64) : List (UInt64 × UInt64) → Bool
  | [] => false
  | (d, _) :: rest => d == dbTok || hasLiveRawStmtForDb dbTok rest

/-- Allocate or override the `(stmt?, consumedByteLen)` result for a succeeding `mockCOps.prepareV2` call. -/
def mockPrepareSuccess (dbTok : UInt64) (sql : String) (s1 : MockCState) :
    Except SqliteRawError (Option UInt64 × Nat) × MockCState :=
  match s1.prepareOverride? with
  | some (false, consumed) => (.ok (none, consumed), s1)
  | some (true, consumed) =>
    let stTok := s1.nextRawStmtTok
    (.ok (some stTok, consumed),
      { s1 with nextRawStmtTok := stTok + 1, liveRawStmts := s1.liveRawStmts ++ [(dbTok, stTok)] })
  | none =>
    if sql.toList.isEmpty then
      (.ok (none, 0), s1)
    else
      let stTok := s1.nextRawStmtTok
      let consumed := mockConsumedBytesUpToSemi sql.toUTF8.data.toList
      let extraQueue :=
        if sql.toList == "PRAGMA journal_mode = WAL;".toList && s1.stepQueue.isEmpty then
          [.row, .done]
        else
          s1.stepQueue
      (.ok (some stTok, consumed),
        { s1 with
          nextRawStmtTok := stTok + 1
          liveRawStmts := s1.liveRawStmts ++ [(dbTok, stTok)]
          stepQueue := extraQueue })

/-- Pure `StateM MockCState` thin-C backend modeling `sqlite3_*` single-call primitives. -/
def mockCOps : CSqliteOpsM (StateM MockCState) UInt64 UInt64 :=
  { modifyTable := fun f s =>
      let (a, t') := f s.table
      (a, { s with table := t' })
    openV2 := fun path flags s =>
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.openV2 path flags] }
      match s1.failStep with
      | .openV2 err => (.error err, s1)
      | _ =>
        let tok := s1.nextRawDbTok
        (.ok tok,
          { s1 with
            nextRawDbTok := tok + 1
            liveRawDbs := s1.liveRawDbs ++ [tok] })
    close := fun rawDb s =>
      let tok := rawDbToken rawDb
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.close tok] }
      if !(s1.liveRawDbs.contains tok) then
        (.error (.misuse 21 "raw database handle not open"), s1)
      else
        match s1.failStep with
        | .close err => (.error err, s1)
        | _ =>
          if hasLiveRawStmtForDb tok s1.liveRawStmts then
            (.error (.busy 5 "unable to close due to unfinalized statements"), s1)
          else
            (.ok (), { s1 with liveRawDbs := s1.liveRawDbs.filter (· != tok) })
    extendedResultCodes := fun rawDb onoff s =>
      let tok := rawDbToken rawDb
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.extendedResultCodes tok onoff] }
      if !(s1.liveRawDbs.contains tok) then
        (.error (.misuse 21 "raw database handle not open"), s1)
      else
        match s1.failStep with
        | .extendedResultCodes err => (.error err, s1)
        | _ => (.ok (), s1)
    busyTimeout := fun rawDb ms s =>
      let tok := rawDbToken rawDb
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.busyTimeout tok ms] }
      if !(s1.liveRawDbs.contains tok) then
        (.error (.misuse 21 "raw database handle not open"), s1)
      else
        match s1.failStep with
        | .busyTimeout err => (.error err, s1)
        | _ => (.ok (), s1)
    prepareV2 := fun rawDb sql s =>
      let dbTok := rawDbToken rawDb
      let idx := s.prepareCount
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.prepareV2 dbTok sql], prepareCount := idx + 1 }
      if !(s1.liveRawDbs.contains dbTok) then
        (.error (.misuse 21 "raw database handle not open"), s1)
      else
        match s1.failStep with
        | .prepareV2At nth err =>
          if nth == idx then
            (.error err, s1)
          else
            mockPrepareSuccess dbTok sql s1
        | _ =>
          mockPrepareSuccess dbTok sql s1
    step := fun rawStmt s =>
      let stTok := rawStmtToken rawStmt
      let idx := s.stepCount
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.step stTok], stepCount := idx + 1 }
      if !(hasLiveRawStmt stTok s1.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s1)
      else
        match s1.failStep with
        | .stepAt nth err =>
          if nth == idx then
            (.error err, s1)
          else
            match s1.stepQueue with
            | [] => (.ok .done, s1)
            | tag :: rest => (.ok tag, { s1 with stepQueue := rest })
        | _ =>
          match s1.stepQueue with
          | [] => (.ok .done, s1)
          | tag :: rest => (.ok tag, { s1 with stepQueue := rest })
    reset := fun rawStmt s =>
      let stTok := rawStmtToken rawStmt
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.reset stTok] }
      if !(hasLiveRawStmt stTok s1.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s1)
      else
        match s1.failStep with
        | .reset err => (.error err, s1)
        | _ => (.ok (), s1)
    clearBindings := fun rawStmt s =>
      let stTok := rawStmtToken rawStmt
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.clearBindings stTok] }
      if !(hasLiveRawStmt stTok s1.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s1)
      else
        match s1.failStep with
        | .clearBindings err => (.error err, s1)
        | _ => (.ok (), s1)
    finalize := fun rawStmt s =>
      let stTok := rawStmtToken rawStmt
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.finalize stTok] }
      if !(hasLiveRawStmt stTok s1.liveRawStmts) then
        (.rejected (.misuse 21 "raw statement handle already finalized"), s1)
      else
        match s1.failStep with
        | .finalizeResult (.rejected err) => (.rejected err, s1)
        | .finalizeResult (.finalized sticky?) =>
          (.finalized sticky?, { s1 with liveRawStmts := s1.liveRawStmts.filter fun p => p.2 != stTok })
        | _ =>
          (.finalized none, { s1 with liveRawStmts := s1.liveRawStmts.filter fun p => p.2 != stTok })
    bindParamCount := fun rawStmt s =>
      let stTok := rawStmtToken rawStmt
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.bindParamCount stTok] }
      if !(hasLiveRawStmt stTok s1.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s1)
      else
        match s1.failStep with
        | .bindParamCount err => (.error err, s1)
        | _ => (.ok s1.expectedBindParams, s1)
    bindNull := fun rawStmt idx s =>
      let stTok := rawStmtToken rawStmt
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.bindNull stTok idx] }
      if !(hasLiveRawStmt stTok s1.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s1)
      else
        match s1.failStep with
        | .bindAt fIdx err => if fIdx == idx then (.error err, s1) else (.ok (), s1)
        | _ => (.ok (), s1)
    bindInt64 := fun rawStmt idx val s =>
      let stTok := rawStmtToken rawStmt
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.bindInt64 stTok idx val] }
      if !(hasLiveRawStmt stTok s1.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s1)
      else
        match s1.failStep with
        | .bindAt fIdx err => if fIdx == idx then (.error err, s1) else (.ok (), s1)
        | _ => (.ok (), s1)
    bindDouble := fun rawStmt idx val s =>
      let stTok := rawStmtToken rawStmt
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.bindDouble stTok idx val] }
      if !(hasLiveRawStmt stTok s1.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s1)
      else
        match s1.failStep with
        | .bindAt fIdx err => if fIdx == idx then (.error err, s1) else (.ok (), s1)
        | _ => (.ok (), s1)
    bindText := fun rawStmt idx val s =>
      let stTok := rawStmtToken rawStmt
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.bindText stTok idx val] }
      if !(hasLiveRawStmt stTok s1.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s1)
      else
        match s1.failStep with
        | .bindAt fIdx err => if fIdx == idx then (.error err, s1) else (.ok (), s1)
        | _ => (.ok (), s1)
    bindBlob := fun rawStmt idx val s =>
      let stTok := rawStmtToken rawStmt
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.bindBlob stTok idx val] }
      if !(hasLiveRawStmt stTok s1.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s1)
      else
        match s1.failStep with
        | .bindAt fIdx err => if fIdx == idx then (.error err, s1) else (.ok (), s1)
        | _ => (.ok (), s1)
    columnCount := fun rawStmt s =>
      let stTok := rawStmtToken rawStmt
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.columnCount stTok] }
      if !(hasLiveRawStmt stTok s1.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s1)
      else
        match s1.failStep with
        | .columnCount err => (.error err, s1)
        | _ => (.ok (UInt32.ofNat s1.mockColumns.size), s1)
    columnType := fun rawStmt col s =>
      let stTok := rawStmtToken rawStmt
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.columnType stTok col] }
      if !(hasLiveRawStmt stTok s1.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s1)
      else
        match s1.failStep with
        | .columnType fCol err =>
          if fCol == col then
            (.error err, s1)
          else
            let ty : UInt32 := match s1.mockColumns[col.toNat]? with
              | some .sqlNull => 5
              | some (.sqlInt _) => 1
              | some (.sqlDouble _) => 2
              | some (.sqlTextBytes _) => 3
              | some (.sqlBlobBytes _) => 4
              | none => 5
            (.ok ty, s1)
        | _ =>
          let ty : UInt32 := match s1.mockColumns[col.toNat]? with
            | some .sqlNull => 5
            | some (.sqlInt _) => 1
            | some (.sqlDouble _) => 2
            | some (.sqlTextBytes _) => 3
            | some (.sqlBlobBytes _) => 4
            | none => 5
          (.ok ty, s1)
    columnInt64 := fun rawStmt col s =>
      let stTok := rawStmtToken rawStmt
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.columnInt64 stTok col] }
      if !(hasLiveRawStmt stTok s1.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s1)
      else
        match s1.failStep with
        | .columnInt64 fCol err =>
          if fCol == col then
            (.error err, s1)
          else
            match s1.mockColumns[col.toNat]? with
            | some (.sqlInt v) => (.ok v, s1)
            | _ => (.ok 0, s1)
        | _ =>
          match s1.mockColumns[col.toNat]? with
          | some (.sqlInt v) => (.ok v, s1)
          | _ => (.ok 0, s1)
    columnDouble := fun rawStmt col s =>
      let stTok := rawStmtToken rawStmt
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.columnDouble stTok col] }
      if !(hasLiveRawStmt stTok s1.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s1)
      else
        match s1.failStep with
        | .columnDouble fCol err =>
          if fCol == col then
            (.error err, s1)
          else
            match s1.mockColumns[col.toNat]? with
            | some (.sqlDouble d) => (.ok d, s1)
            | _ => (.ok 0.0, s1)
        | _ =>
          match s1.mockColumns[col.toNat]? with
          | some (.sqlDouble d) => (.ok d, s1)
          | _ => (.ok 0.0, s1)
    columnTextBytes := fun rawStmt col s =>
      let stTok := rawStmtToken rawStmt
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.columnTextBytes stTok col] }
      if !(hasLiveRawStmt stTok s1.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s1)
      else
        match s1.failStep with
        | .columnTextBytes fCol err =>
          if fCol == col then
            (.error err, s1)
          else
            match s1.mockColumns[col.toNat]? with
            | some (.sqlTextBytes bs) => (.ok bs, s1)
            | _ => (.ok ByteArray.empty, s1)
        | _ =>
          match s1.mockColumns[col.toNat]? with
          | some (.sqlTextBytes bs) => (.ok bs, s1)
          | _ => (.ok ByteArray.empty, s1)
    columnBlob := fun rawStmt col s =>
      let stTok := rawStmtToken rawStmt
      let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.columnBlob stTok col] }
      if !(hasLiveRawStmt stTok s1.liveRawStmts) then
        (.error (.misuse 21 "raw statement handle not live"), s1)
      else
        match s1.failStep with
        | .columnBlob fCol err =>
          if fCol == col then
            (.error err, s1)
          else
            match s1.mockColumns[col.toNat]? with
            | some (.sqlBlobBytes bs) => (.ok bs, s1)
            | _ => (.ok ByteArray.empty, s1)
        | _ =>
          match s1.mockColumns[col.toNat]? with
          | some (.sqlBlobBytes bs) => (.ok bs, s1)
          | _ => (.ok ByteArray.empty, s1) }

/-- Construct an initial `MockCState` with one open database handle (`id := 1`, raw token `100`). -/
def mockStateWithOpenDb (failStep : MockCFailStep := .none) : MockCState :=
  { table := { nextDbId := 2, nextStmtId := 1, dbs := [(1, 100)], stmts := [] }
    nextRawDbTok := 101
    nextRawStmtTok := 200
    liveRawDbs := [100]
    liveRawStmts := []
    failStep := failStep }

/-- Construct an initial `MockCState` with one open database (`id := 1`) and one prepared statement (`id := 1`). -/
def mockStateWithOpenStmt (expectedParams : UInt32 := 0) (stepQueue : List RawStepTag := [])
    (cols : Array MockCColumn := #[]) (failStep : MockCFailStep := .none) : MockCState :=
  let sh : StmtHandle := { id := 1, dbId := 1 }
  { table := { nextDbId := 2, nextStmtId := 2, dbs := [(1, 100)], stmts := [(sh, 200)] }
    nextRawDbTok := 101
    nextRawStmtTok := 201
    liveRawDbs := [100]
    liveRawStmts := [(100, 200)]
    stepQueue := stepQueue
    expectedBindParams := expectedParams
    mockColumns := cols
    failStep := failStep }

/-- Every error returned by `ops.mapRawError` carries a non-empty diagnostic message. -/
def test_sqliteraw_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (ops : RawSqliteOps) : runner Unit := do
  let raw ← nondet SqliteRawError
  let err := ops.mapRawError raw
  NondetTest.assert (err.message ≠ "")

/-- `ops.mapRawError` maps every `SqliteRawError` constructor (including primary-masked `sqliteCodeError`)
    to its exact `SqliteErrorKind`, `sqliteCode`, and `path`. -/
def test_sqliteraw_mapRawError_mapsKnownKinds
    {runner} [NondetTest runner] (ops : RawSqliteOps) : runner Unit := do
  let raw ← nondet SqliteRawError
  let err := ops.mapRawError raw
  match raw with
  | .cantOpen path? code _ =>
    NondetTest.assert (err.kind = .notFound ∧ err.sqliteCode = some code ∧ err.path = path? ∧ err.message ≠ "")
  | .busy code _ =>
    NondetTest.assert (err.kind = .busy ∧ err.sqliteCode = some code ∧ err.path = none ∧ err.message ≠ "")
  | .constraint code _ =>
    NondetTest.assert (err.kind = .constraint ∧ err.sqliteCode = some code ∧ err.path = none ∧ err.message ≠ "")
  | .misuse code _ =>
    NondetTest.assert (err.kind = .misuse ∧ err.sqliteCode = some code ∧ err.path = none ∧ err.message ≠ "")
  | .invalidArgument _ =>
    NondetTest.assert (err.kind = .invalidInput ∧ err.sqliteCode = none ∧ err.path = none ∧ err.message ≠ "")
  | .ioFailure code _ =>
    NondetTest.assert (err.kind = .ioError ∧ err.sqliteCode = some code ∧ err.path = none ∧ err.message ≠ "")
  | .sqliteCodeError code _ =>
    let expectedKind : SqliteErrorKind :=
      match (code &&& 0xFF).toNat with
      | 5 | 6 => .busy
      | 14 => .notFound
      | 19 => .constraint
      | 21 => .misuse
      | 25 => .invalidInput
      | _ => .ioError
    NondetTest.assert (err.kind = expectedKind ∧ err.sqliteCode = some code ∧ err.path = none ∧ err.message ≠ "")
  | .userError _ =>
    NondetTest.assert (err.kind = .ioError ∧ err.sqliteCode = none ∧ err.path = none ∧ err.message ≠ "")

/-- `(mkRaw mockCOps).mapRawError` agrees identically with `ops.mapRawError` across every `SqliteRawError`. -/
def test_sqliteraw_mapRawError_consistentAcrossBackends
    {runner} [NondetTest runner]
    (ops : RawSqliteOps)
    (mkRaw : CSqliteOpsM (StateM MockCState) UInt64 UInt64 → RawSqliteOpsM (StateM MockCState)) : runner Unit := do
  let raw ← nondet SqliteRawError
  NondetTest.assert ((mkRaw mockCOps).mapRawError raw = ops.mapRawError raw)

/-- `openDb` rejects empty paths, embedded-NUL paths, `readOnly && createIfMissing`, and
    `busyTimeoutMs > maxBusyTimeoutMs` with `.invalidInput` before making any C call. -/
def test_sqliteraw_openDb_rejectsInvalidPathAndConfigWithoutCallingC
    {runner} [NondetTest runner]
    (mkRaw : CSqliteOpsM (StateM MockCState) UInt64 UInt64 → RawSqliteOpsM (StateM MockCState)) : runner Unit := do
  let path ← nondet String
  let cfg ← nondet OpenConfig
  assume (path = "" ∨ Char.ofNat 0 ∈ path.toList ∨
    (cfg.readOnly = true ∧ cfg.createIfMissing = true) ∨ cfg.busyTimeoutMs > maxBusyTimeoutMs)
  let ops := mkRaw mockCOps
  let out := (ops.openDb path cfg).run {}
  NondetTest.assert ((∃ e, out.1 = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧
    out.2.calls = [] ∧ out.2.liveRawDbs = [] ∧ (ops.activeDbCount.run out.2).1 = 0)

/-- On valid non-memory, non-URI paths, `openDb` computes the exact `SQLITE_OPEN_FULLMUTEX | SQLITE_OPEN_URI | ...`
    bitmask, enables extended result codes, sets `busyTimeout`, runs conditional `foreign_keys` and `WAL` pragmas
    (draining `.row` before `.done` and finalizing every pragma statement), and records one active DB handle. -/
def test_sqliteraw_openDb_computesExactOpenFlagsAndSetupOrder
    {runner} [NondetTest runner]
    (mkRaw : CSqliteOpsM (StateM MockCState) UInt64 UInt64 → RawSqliteOpsM (StateM MockCState)) : runner Unit := do
  let path ← nondet String
  let cfg ← nondet OpenConfig
  assume (path ≠ "" ∧ Char.ofNat 0 ∉ path.toList)
  assume (path.toUTF8 != ":memory:".toUTF8 ∧ path.toUTF8.data.toList.take 5 != "file:".toUTF8.data.toList)
  assume (!(cfg.readOnly && cfg.createIfMissing) ∧ cfg.busyTimeoutMs ≤ maxBusyTimeoutMs)
  let ops := mkRaw mockCOps
  let out := (ops.openDb path cfg).run {}
  let expectedFlags : UInt32 :=
    sqliteOpenFullMutex ||| sqliteOpenUri |||
      (if cfg.readOnly then sqliteOpenReadOnly
       else if cfg.createIfMissing then sqliteOpenReadWrite ||| sqliteOpenCreate
       else sqliteOpenReadWrite)
  let fkCalls : List MockCCall :=
    if cfg.foreignKeys then
      [.prepareV2 100 "PRAGMA foreign_keys = ON;", .step 200, .finalize 200]
    else
      []
  let walTok : UInt64 := if cfg.foreignKeys then 201 else 200
  let walCalls : List MockCCall :=
    if !cfg.readOnly && cfg.walMode then
      [.prepareV2 100 "PRAGMA journal_mode = WAL;", .step walTok, .step walTok, .finalize walTok]
    else
      []
  let expectedCalls : List MockCCall :=
    [.openV2 path expectedFlags,
     .extendedResultCodes 100 true,
     .busyTimeout 100 (UInt32.ofNat cfg.busyTimeoutMs)] ++ fkCalls ++ walCalls
  NondetTest.assert (out.1 = .ok { id := 1 } ∧
    out.2.calls = expectedCalls ∧
    out.2.liveRawDbs = [100] ∧
    out.2.liveRawStmts = [] ∧
    (ops.activeDbCount.run out.2).1 = 1 ∧
    (ops.activeStmtCount.run out.2).1 = 0)

/-- `openDb` skips `PRAGMA journal_mode = WAL;` on `:memory:`, `file::memory:`, symbolic `"file:" ++ name ++ "?mode=memory"`,
    lowercase and uppercase percent-escaped `mode=%6demory` / `mode=%6Demory` / `%3amemory%3a`, `#` fragments,
    overridden `mode=rw&mode=memory`, and read-only `mode=ro` URIs. -/
def test_sqliteraw_openDb_skipsWalOnMemoryAndReadOnlyTargets
    {runner} [NondetTest runner]
    (mkRaw : CSqliteOpsM (StateM MockCState) UInt64 UInt64 → RawSqliteOpsM (StateM MockCState)) : runner Unit := do
  let name ← nondet String
  assume (Char.ofNat 0 ∉ name.toList ∧ '?' ∉ name.toList ∧ '#' ∉ name.toList)
  assume (name.toUTF8.data.toList.take 2 != [0x2F, 0x2F])
  let ops := mkRaw mockCOps
  let cfg : OpenConfig := { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }
  let walCall := MockCCall.prepareV2 100 "PRAGMA journal_mode = WAL;"

  let outSym := (ops.openDb ("file:" ++ name ++ "?mode=memory") cfg).run {}
  NondetTest.assert (outSym.1 = .ok { id := 1 } ∧ !(outSym.2.calls.contains walCall))

  let outMem := (ops.openDb ":memory:" cfg).run {}
  let outFileMem := (ops.openDb "file::memory:?cache=shared" cfg).run {}
  let outOverrideMem := (ops.openDb "file:mem.db?mode=rw&mode=memory" cfg).run {}
  let outPctModeLo := (ops.openDb "file:mem.db?mode=%6demory" cfg).run {}
  let outPctModeHi := (ops.openDb "file:mem.db?mode=%6Demory" cfg).run {}
  let outPctFile := (ops.openDb "file:%3amemory%3a?cache=shared" cfg).run {}
  let outFragMem := (ops.openDb "file:mem.db?mode=memory#section" cfg).run {}
  let outUriRo := (ops.openDb "file:disk.db?mode=ro" cfg).run {}
  NondetTest.assert (outMem.1 = .ok { id := 1 } ∧ !(outMem.2.calls.contains walCall))
  NondetTest.assert (outFileMem.1 = .ok { id := 1 } ∧ !(outFileMem.2.calls.contains walCall))
  NondetTest.assert (outOverrideMem.1 = .ok { id := 1 } ∧ !(outOverrideMem.2.calls.contains walCall))
  NondetTest.assert (outPctModeLo.1 = .ok { id := 1 } ∧ !(outPctModeLo.2.calls.contains walCall))
  NondetTest.assert (outPctModeHi.1 = .ok { id := 1 } ∧ !(outPctModeHi.2.calls.contains walCall))
  NondetTest.assert (outPctFile.1 = .ok { id := 1 } ∧ !(outPctFile.2.calls.contains walCall))
  NondetTest.assert (outFragMem.1 = .ok { id := 1 } ∧ !(outFragMem.2.calls.contains walCall))
  NondetTest.assert (outUriRo.1 = .ok { id := 1 } ∧ !(outUriRo.2.calls.contains walCall))

/-- `openDb` skips `PRAGMA journal_mode = WAL;` on `%00`-truncated memory URIs (`file::memory:%00extra?cache=shared`,
    `file:mem.db?mode=memory%00extra`), `file::memory:?mode=rwc`, and `//localhost/` or `///` authority memory URIs,
    while running `WAL` on `"file://localhost/:memory:?cache=shared"` (`zFile = "/:memory:"`),
    `"file:disk.db?%00mode=memory"` (empty key ignored), `"file:disk.db?mode=memory&mode=rwc"`, `"file:mode=memory"`,
    and non-URI `"disk_mode=memory.db"`. -/
def test_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets
    {runner} [NondetTest runner]
    (mkRaw : CSqliteOpsM (StateM MockCState) UInt64 UInt64 → RawSqliteOpsM (StateM MockCState)) : runner Unit := do
  let ops := mkRaw mockCOps
  let cfg : OpenConfig := { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }
  let walCall := MockCCall.prepareV2 100 "PRAGMA journal_mode = WAL;"

  let outNulFile := (ops.openDb "file::memory:%00extra?cache=shared" cfg).run {}
  let outNulVal := (ops.openDb "file:mem.db?mode=memory%00extra" cfg).run {}
  let outColonMemRwc := (ops.openDb "file::memory:?mode=rwc" cfg).run {}
  let outAuthLocal := (ops.openDb "file://localhost/mem.db?mode=memory" cfg).run {}
  let outAuthEmpty := (ops.openDb "file:///mem.db?mode=memory" cfg).run {}
  NondetTest.assert (outNulFile.1 = .ok { id := 1 } ∧ !(outNulFile.2.calls.contains walCall))
  NondetTest.assert (outNulVal.1 = .ok { id := 1 } ∧ !(outNulVal.2.calls.contains walCall))
  NondetTest.assert (outColonMemRwc.1 = .ok { id := 1 } ∧ !(outColonMemRwc.2.calls.contains walCall))
  NondetTest.assert (outAuthLocal.1 = .ok { id := 1 } ∧ !(outAuthLocal.2.calls.contains walCall))
  NondetTest.assert (outAuthEmpty.1 = .ok { id := 1 } ∧ !(outAuthEmpty.2.calls.contains walCall))

  let outAuthSlashColon := (ops.openDb "file://localhost/:memory:?cache=shared" cfg).run {}
  let outNulKey := (ops.openDb "file:disk.db?%00mode=memory" cfg).run {}
  let outOverrideRwc := (ops.openDb "file:disk.db?mode=memory&mode=rwc" cfg).run {}
  let outLiteralFile := (ops.openDb "file:mode=memory" cfg).run {}
  let outPlainPath := (ops.openDb "disk_mode=memory.db" cfg).run {}
  NondetTest.assert (outAuthSlashColon.1 = .ok { id := 1 } ∧ outAuthSlashColon.2.calls.contains walCall)
  NondetTest.assert (outNulKey.1 = .ok { id := 1 } ∧ outNulKey.2.calls.contains walCall)
  NondetTest.assert (outOverrideRwc.1 = .ok { id := 1 } ∧ outOverrideRwc.2.calls.contains walCall)
  NondetTest.assert (outLiteralFile.1 = .ok { id := 1 } ∧ outLiteralFile.2.calls.contains walCall)
  NondetTest.assert (outPlainPath.1 = .ok { id := 1 } ∧ outPlainPath.2.calls.contains walCall)

/-- Whenever `openV2` or any post-open setup step (`extendedResultCodes`, `busyTimeout`, `foreign_keys` prepare/step,
    or `WAL` prepare/step) fails, `openDb` finalizes any in-flight pragma statement, closes `rawDb`, attaches `some path`
    to `.cantOpen none`, and leaves zero live DB or statement handles. -/
def test_sqliteraw_openDb_closesHandleOnAnySetupFailure
    {runner} [NondetTest runner]
    (mkRaw : CSqliteOpsM (StateM MockCState) UInt64 UInt64 → RawSqliteOpsM (StateM MockCState)) : runner Unit := do
  let code ← nondet UInt32
  let detail ← nondet String
  let ops := mkRaw mockCOps
  let cfg : OpenConfig := { foreignKeys := true, walMode := true }
  let cantOpenNone : SqliteRawError := .cantOpen none code detail
  let busyErr : SqliteRawError := .busy code detail

  let outOpen := (ops.openDb "app.db" cfg).run { failStep := .openV2 cantOpenNone }
  NondetTest.assert ((∃ e, outOpen.1 = .error e ∧ e.kind = .notFound ∧ e.path = some "app.db") ∧
    outOpen.2.liveRawDbs = [] ∧ (ops.activeDbCount.run outOpen.2).1 = 0)

  let outExt := (ops.openDb "app.db" cfg).run { failStep := .extendedResultCodes busyErr }
  let outTimeout := (ops.openDb "app.db" cfg).run { failStep := .busyTimeout busyErr }
  let outFkPrep := (ops.openDb "app.db" cfg).run { failStep := .prepareV2At 0 busyErr }
  let outFkStep := (ops.openDb "app.db" cfg).run { failStep := .stepAt 0 busyErr }
  let outWalPrep := (ops.openDb "app.db" cfg).run { failStep := .prepareV2At 1 busyErr }
  let outWalStep := (ops.openDb "app.db" cfg).run { failStep := .stepAt 1 busyErr }

  NondetTest.assert ((∃ e, outExt.1 = .error e ∧ e.kind = .busy) ∧
    outExt.2.liveRawDbs = [] ∧ outExt.2.liveRawStmts = [] ∧ (ops.activeDbCount.run outExt.2).1 = 0)
  NondetTest.assert ((∃ e, outTimeout.1 = .error e ∧ e.kind = .busy) ∧
    outTimeout.2.liveRawDbs = [] ∧ outTimeout.2.liveRawStmts = [] ∧ (ops.activeDbCount.run outTimeout.2).1 = 0)
  NondetTest.assert ((∃ e, outFkPrep.1 = .error e ∧ e.kind = .busy) ∧
    outFkPrep.2.liveRawDbs = [] ∧ outFkPrep.2.liveRawStmts = [] ∧ (ops.activeDbCount.run outFkPrep.2).1 = 0)
  NondetTest.assert ((∃ e, outFkStep.1 = .error e ∧ e.kind = .busy) ∧
    outFkStep.2.liveRawDbs = [] ∧ outFkStep.2.liveRawStmts = [] ∧ (ops.activeDbCount.run outFkStep.2).1 = 0)
  NondetTest.assert ((∃ e, outWalPrep.1 = .error e ∧ e.kind = .busy) ∧
    outWalPrep.2.liveRawDbs = [] ∧ outWalPrep.2.liveRawStmts = [] ∧ (ops.activeDbCount.run outWalPrep.2).1 = 0)
  NondetTest.assert ((∃ e, outWalStep.1 = .error e ∧ e.kind = .busy) ∧
    outWalStep.2.liveRawDbs = [] ∧ outWalStep.2.liveRawStmts = [] ∧ (ops.activeDbCount.run outWalStep.2).1 = 0)

/-- `openDb` and `closeDb` maintain monotonic distinct `DbHandle` IDs and exact `activeDbCount`, reject closing a DB
    with `.busy` in Lean before `cops.close` when that DB owns an unfinalized statement while still allowing an
    independent second DB to close cleanly, propagate `.busy` from `cops.close` on C pin contention, and reject
    double-close / unknown handles with `.misuse`. -/
def test_sqliteraw_openClose_preservesActiveDbCountAndRejectsClosedOrBusy
    {runner} [NondetTest runner]
    (mkRaw : CSqliteOpsM (StateM MockCState) UInt64 UInt64 → RawSqliteOpsM (StateM MockCState)) : runner Unit := do
  let unknownId ← nondet UInt64
  assume (unknownId ≠ 1 ∧ unknownId ≠ 2)
  let ops := mkRaw mockCOps
  let cfg : OpenConfig := { walMode := false, foreignKeys := false }
  let (r1, s1) := (ops.openDb ":memory:" cfg).run {}
  let (r2, s2) := (ops.openDb ":memory:" cfg).run s1
  NondetTest.assert (r1 = .ok { id := 1 } ∧ r2 = .ok { id := 2 } ∧ (ops.activeDbCount.run s2).1 = 2)

  let (rUnknown, s2u) := (ops.closeDb { id := unknownId }).run s2
  NondetTest.assert ((∃ e, rUnknown = .error e ∧ e.kind = .misuse) ∧ (ops.activeDbCount.run s2u).1 = 2)

  let (rPrep1, sPrep1) := (ops.prepare { id := 1 } "SELECT 1").run s2
  NondetTest.assert (rPrep1 = .ok { id := 1, dbId := 1 } ∧
    sPrep1.liveRawStmts = [(100, 200)] ∧ (ops.activeStmtCount.run sPrep1).1 = 1)

  let (rBusyStmt1, sBusyStmt1) := (ops.closeDb { id := 1 }).run { sPrep1 with calls := [] }
  NondetTest.assert ((∃ e, rBusyStmt1 = .error e ∧ e.kind = .busy) ∧
    sBusyStmt1.calls = [] ∧ (ops.activeDbCount.run sBusyStmt1).1 = 2)

  let (rc2While1Active, sAfterClose2) := (ops.closeDb { id := 2 }).run sPrep1
  NondetTest.assert (rc2While1Active = .ok () ∧
    sAfterClose2.liveRawDbs = [100] ∧ (ops.activeDbCount.run sAfterClose2).1 = 1)

  let (rFin1, sAfterFin1) := (ops.finalize { id := 1, dbId := 1 }).run sAfterClose2
  NondetTest.assert (rFin1 = .ok () ∧ sAfterFin1.liveRawStmts = [] ∧ (ops.activeStmtCount.run sAfterFin1).1 = 0)

  let (rBusyPin, sBusyPin) := (ops.closeDb { id := 1 }).run
    { sAfterFin1 with failStep := .close (.busy 5 "c handle pinned") }
  NondetTest.assert ((∃ e, rBusyPin = .error e ∧ e.kind = .busy) ∧ (ops.activeDbCount.run sBusyPin).1 = 1)

  let (rc1, s4) := (ops.closeDb { id := 1 }).run sAfterFin1
  let (rcDup, s5) := (ops.closeDb { id := 1 }).run s4
  NondetTest.assert (rc1 = .ok () ∧
    (∃ e, rcDup = .error e ∧ e.kind = .misuse) ∧
    s4.liveRawDbs = [] ∧ (ops.activeDbCount.run s5).1 = 0)

/-- `prepare` rejects embedded-NUL SQL strings with `.invalidInput` without calling `prepareV2`, rejects closed/unknown
    `DbHandle`s with `.misuse` without calling `prepareV2`, and rejects empty/whitespace-only SQL `(none, _)` with `.misuse`. -/
def test_sqliteraw_prepare_rejectsNulClosedDbAndEmptySql
    {runner} [NondetTest runner]
    (mkRaw : CSqliteOpsM (StateM MockCState) UInt64 UInt64 → RawSqliteOpsM (StateM MockCState)) : runner Unit := do
  let pre ← nondet String
  let suf ← nondet String
  let closedId ← nondet UInt64
  assume (closedId ≠ 1)
  let ops := mkRaw mockCOps
  let sOpen := mockStateWithOpenDb
  let nulSql := pre ++ String.ofList [Char.ofNat 0] ++ suf
  let outNul := (ops.prepare { id := 1 } nulSql).run sOpen
  NondetTest.assert ((∃ e, outNul.1 = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧
    outNul.2.calls = [] ∧ (ops.activeStmtCount.run outNul.2).1 = 0)

  let outClosed := (ops.prepare { id := closedId } "SELECT 1").run sOpen
  NondetTest.assert ((∃ e, outClosed.1 = .error e ∧ e.kind = .misuse ∧ e.message ≠ "") ∧
    outClosed.2.calls = [] ∧ (ops.activeStmtCount.run outClosed.2).1 = 0)

  let outEmpty := (ops.prepare { id := 1 } "").run sOpen
  let outCommentOnly := (ops.prepare { id := 1 } "   -- comment only").run
    { sOpen with prepareOverride? := some (false, 18) }
  NondetTest.assert ((∃ e, outEmpty.1 = .error e ∧ e.kind = .misuse) ∧
    (ops.activeStmtCount.run outEmpty.2).1 = 0)
  NondetTest.assert ((∃ e, outCommentOnly.1 = .error e ∧ e.kind = .misuse) ∧
    (ops.activeStmtCount.run outCommentOnly.2).1 = 0)

/-- `prepare` accepts SQLite ASCII whitespace (`' '`, `'\t'`, `'\n'`, `'\f'`, `'\r'`), `--` line comments
    (both newline-terminated and EOF-terminated), and closed `/* ... */` block comments (including multi-star `/***/`)
    in the unconsumed tail after `;`. -/
def test_sqliteraw_prepare_acceptsCommentsAndWhitespaceInTail
    {runner} [NondetTest runner]
    (mkRaw : CSqliteOpsM (StateM MockCState) UInt64 UInt64 → RawSqliteOpsM (StateM MockCState)) : runner Unit := do
  let lineBody ← nondet String
  let blockBody ← nondet String
  assume (Char.ofNat 0 ∉ lineBody.toList ∧ '\n' ∉ lineBody.toList ∧ lineBody.toUTF8.size ≤ 4096)
  assume (Char.ofNat 0 ∉ blockBody.toList ∧ '*' ∉ blockBody.toList ∧ blockBody.toUTF8.size ≤ 4096)
  let ops := mkRaw mockCOps
  let sOpen := mockStateWithOpenDb

  let outLineEof := (ops.prepare { id := 1 } ("SELECT 1; --" ++ lineBody)).run sOpen
  let outLineNl := (ops.prepare { id := 1 } ("SELECT 1; --" ++ lineBody ++ "\n \t\r\x0c")).run sOpen
  let outBlock := (ops.prepare { id := 1 } ("SELECT 1; /*" ++ blockBody ++ "*/ \n")).run sOpen
  let outComplex := (ops.prepare { id := 1 } "SELECT 1; /***/ /* a * b **/ -- tail\n  ").run sOpen

  NondetTest.assert (outLineEof.1 = .ok { id := 1, dbId := 1 } ∧
    outLineEof.2.liveRawStmts = [(100, 200)] ∧ (ops.activeStmtCount.run outLineEof.2).1 = 1)
  NondetTest.assert (outLineNl.1 = .ok { id := 1, dbId := 1 } ∧
    outLineNl.2.liveRawStmts = [(100, 200)] ∧ (ops.activeStmtCount.run outLineNl.2).1 = 1)
  NondetTest.assert (outBlock.1 = .ok { id := 1, dbId := 1 } ∧
    outBlock.2.liveRawStmts = [(100, 200)] ∧ (ops.activeStmtCount.run outBlock.2).1 = 1)
  NondetTest.assert (outComplex.1 = .ok { id := 1, dbId := 1 } ∧
    outComplex.2.liveRawStmts = [(100, 200)] ∧ (ops.activeStmtCount.run outComplex.2).1 = 1)

/-- `prepare` rejects multi-statement SQL, extra semicolons, lone `-` or `/`, non-SQLite whitespace (`0x0B`),
    `consumedByteLen > totalBytes`, and all unclosed `/*` block comments (including `"SELECT 1; /*/"` and universal
    `'/'`-free `"SELECT 1; /*" ++ body`) with `.misuse`, calling `finalize` so zero raw statements leak. -/
def test_sqliteraw_prepare_rejectsMultiStmtAndUnclosedBlockCommentAndFinalizes
    {runner} [NondetTest runner]
    (mkRaw : CSqliteOpsM (StateM MockCState) UInt64 UInt64 → RawSqliteOpsM (StateM MockCState)) : runner Unit := do
  let unclosedBody ← nondet String
  assume (Char.ofNat 0 ∉ unclosedBody.toList ∧ '/' ∉ unclosedBody.toList ∧ unclosedBody.toUTF8.size ≤ 4096)
  let ops := mkRaw mockCOps
  let sOpen := mockStateWithOpenDb

  let outUnclosed := (ops.prepare { id := 1 } ("SELECT 1; /*" ++ unclosedBody)).run sOpen
  let outSlashStarSlash := (ops.prepare { id := 1 } "SELECT 1; /*/").run sOpen
  let outTwoStmts := (ops.prepare { id := 1 } "SELECT 1; SELECT 2").run sOpen
  let outExtraSemi := (ops.prepare { id := 1 } "SELECT 1;;").run sOpen
  let outLoneDash := (ops.prepare { id := 1 } "SELECT 1; -").run sOpen
  let outLoneSlash := (ops.prepare { id := 1 } "SELECT 1; /").run sOpen
  let outVertTab := (ops.prepare { id := 1 } ("SELECT 1;" ++ String.ofList [Char.ofNat 0x0B])).run sOpen
  let outOverConsumed := (ops.prepare { id := 1 } "SELECT 1").run
    { sOpen with prepareOverride? := some (true, 99) }

  NondetTest.assert ((∃ e, outUnclosed.1 = .error e ∧ e.kind = .misuse) ∧
    outUnclosed.2.liveRawStmts = [] ∧ (ops.activeStmtCount.run outUnclosed.2).1 = 0)
  NondetTest.assert ((∃ e, outSlashStarSlash.1 = .error e ∧ e.kind = .misuse) ∧
    outSlashStarSlash.2.liveRawStmts = [] ∧ (ops.activeStmtCount.run outSlashStarSlash.2).1 = 0)
  NondetTest.assert ((∃ e, outTwoStmts.1 = .error e ∧ e.kind = .misuse) ∧
    outTwoStmts.2.liveRawStmts = [] ∧ (ops.activeStmtCount.run outTwoStmts.2).1 = 0)
  NondetTest.assert ((∃ e, outExtraSemi.1 = .error e ∧ e.kind = .misuse) ∧
    outExtraSemi.2.liveRawStmts = [] ∧ (ops.activeStmtCount.run outExtraSemi.2).1 = 0)
  NondetTest.assert ((∃ e, outLoneDash.1 = .error e ∧ e.kind = .misuse) ∧
    outLoneDash.2.liveRawStmts = [] ∧ (ops.activeStmtCount.run outLoneDash.2).1 = 0)
  NondetTest.assert ((∃ e, outLoneSlash.1 = .error e ∧ e.kind = .misuse) ∧
    outLoneSlash.2.liveRawStmts = [] ∧ (ops.activeStmtCount.run outLoneSlash.2).1 = 0)
  NondetTest.assert ((∃ e, outVertTab.1 = .error e ∧ e.kind = .misuse) ∧
    outVertTab.2.liveRawStmts = [] ∧ (ops.activeStmtCount.run outVertTab.2).1 = 0)
  NondetTest.assert ((∃ e, outOverConsumed.1 = .error e ∧ e.kind = .misuse) ∧
    outOverConsumed.2.liveRawStmts = [] ∧ (ops.activeStmtCount.run outOverConsumed.2).1 = 0)

/-- `bind` rejects unknown or mismatched-`dbId` `StmtHandle`s with `.misuse`, runs `reset` then `clearBindings` then
    `bindParamCount`, rejects count mismatches with `.invalidInput`, binds all 5 `SqliteValue` variants at `1`-based
    indices in order, and propagates C errors. -/
def test_sqliteraw_bind_resetsValidatesCountAndBindsAllFiveTypes
    {runner} [NondetTest runner]
    (mkRaw : CSqliteOpsM (StateM MockCState) UInt64 UInt64 → RawSqliteOpsM (StateM MockCState)) : runner Unit := do
  let iVal ← nondet Int64
  let fVal ← nondet Float
  let sVal ← nondet String
  let bVal ← nondet ByteArray
  let ops := mkRaw mockCOps
  let sh : StmtHandle := { id := 1, dbId := 1 }

  let outWrongDb := (ops.bind { id := 1, dbId := 2 } #[]).run (mockStateWithOpenStmt 0)
  NondetTest.assert ((∃ e, outWrongDb.1 = .error e ∧ e.kind = .misuse) ∧ outWrongDb.2.calls = [])

  let outMismatch := (ops.bind sh #[.null]).run (mockStateWithOpenStmt 2)
  NondetTest.assert ((∃ e, outMismatch.1 = .error e ∧ e.kind = .invalidInput) ∧
    outMismatch.2.calls = [.reset 200, .clearBindings 200, .bindParamCount 200])

  let params : Array SqliteValue := #[.null, .int iVal, .real fVal, .text sVal, .bytes bVal]
  let outOk := (ops.bind sh params).run (mockStateWithOpenStmt 5)
  NondetTest.assert (outOk.1 = .ok () ∧
    outOk.2.calls =
      [.reset 200, .clearBindings 200, .bindParamCount 200,
       .bindNull 200 1, .bindInt64 200 2 iVal, .bindDouble 200 3 fVal,
       .bindText 200 4 sVal, .bindBlob 200 5 bVal])

  let outResetErr := (ops.bind sh params).run
    (mockStateWithOpenStmt 5 [] #[] (.reset (.constraint 19 "sticky constraint")))
  let outBindErr := (ops.bind sh params).run
    (mockStateWithOpenStmt 5 [] #[] (.bindAt 4 (.ioFailure 10 "bind text ioerr")))
  NondetTest.assert (∃ e, outResetErr.1 = .error e ∧ e.kind = .constraint)
  NondetTest.assert (∃ e, outBindErr.1 = .error e ∧ e.kind = .ioError)

/-- `step` rejects unknown `StmtHandle`s with `.misuse`, returns `.done` without reading columns, decodes all 5 column
    types on `.row` via separate `columnTextBytes` (`SQLITE_TEXT`) and `columnBlob` (`SQLITE_BLOB`) hooks (preserving
    invalid-UTF-8 bytes in `SQLITE_BLOB` while rejecting invalid-UTF-8 bytes in `SQLITE_TEXT` with `.ioError` and
    `sqliteCode = none`), and propagates `SQLITE_MISUSE` from all `column*` hooks instead of fabricating defaults. -/
def test_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors
    {runner} [NondetTest runner]
    (mkRaw : CSqliteOpsM (StateM MockCState) UInt64 UInt64 → RawSqliteOpsM (StateM MockCState)) : runner Unit := do
  let iVal ← nondet Int64
  let fVal ← nondet Float
  let sVal ← nondet String
  let badUtf8 ← nondet ByteArray
  assume (String.fromUTF8? badUtf8 = none)
  let ops := mkRaw mockCOps
  let sh : StmtHandle := { id := 1, dbId := 1 }

  let outUnknown := (ops.step { id := 99, dbId := 1 }).run (mockStateWithOpenStmt)
  NondetTest.assert ((∃ e, outUnknown.1 = .error e ∧ e.kind = .misuse) ∧ outUnknown.2.calls = [])

  let outDone := (ops.step sh).run (mockStateWithOpenStmt 0 [.done])
  NondetTest.assert (outDone.1 = .ok .done ∧ outDone.2.calls = [.step 200])

  let validCols : Array MockCColumn :=
    #[.sqlNull, .sqlInt iVal, .sqlDouble fVal, .sqlTextBytes sVal.toUTF8, .sqlBlobBytes badUtf8]
  let outRow := (ops.step sh).run (mockStateWithOpenStmt 0 [.row] validCols)
  NondetTest.assert (outRow.1 = .ok (.row #[.null, .int iVal, .real fVal, .text sVal, .bytes badUtf8]) ∧
    outRow.2.calls.contains (.columnTextBytes 200 3) ∧
    outRow.2.calls.contains (.columnBlob 200 4))

  let badTextCols : Array MockCColumn := #[.sqlTextBytes badUtf8]
  let outBadText := (ops.step sh).run (mockStateWithOpenStmt 0 [.row] badTextCols)
  NondetTest.assert (∃ e, outBadText.1 = .error e ∧ e.kind = .ioError ∧ e.sqliteCode = none ∧ e.message ≠ "")

  let outColCntErr := (ops.step sh).run
    (mockStateWithOpenStmt 0 [.row] validCols (.columnCount (.misuse 21 "closed")))
  let outColTyErr := (ops.step sh).run
    (mockStateWithOpenStmt 0 [.row] validCols (.columnType 1 (.misuse 21 "closed")))
  let outColIntErr := (ops.step sh).run
    (mockStateWithOpenStmt 0 [.row] validCols (.columnInt64 1 (.misuse 21 "closed")))
  let outColDblErr := (ops.step sh).run
    (mockStateWithOpenStmt 0 [.row] validCols (.columnDouble 2 (.misuse 21 "closed")))
  let outColTextErr := (ops.step sh).run
    (mockStateWithOpenStmt 0 [.row] validCols (.columnTextBytes 3 (.misuse 21 "closed")))
  let outColBlobErr := (ops.step sh).run
    (mockStateWithOpenStmt 0 [.row] validCols (.columnBlob 4 (.misuse 21 "closed")))
  NondetTest.assert (∃ e, outColCntErr.1 = .error e ∧ e.kind = .misuse)
  NondetTest.assert (∃ e, outColTyErr.1 = .error e ∧ e.kind = .misuse)
  NondetTest.assert (∃ e, outColIntErr.1 = .error e ∧ e.kind = .misuse)
  NondetTest.assert (∃ e, outColDblErr.1 = .error e ∧ e.kind = .misuse)
  NondetTest.assert (∃ e, outColTextErr.1 = .error e ∧ e.kind = .misuse)
  NondetTest.assert (∃ e, outColBlobErr.1 = .error e ∧ e.kind = .misuse)

/-- `finalize` releases the statement from `activeStmtCount` on both `.finalized none` and `.finalized (some stickyErr)`
    (allowing subsequent `closeDb` to succeed), retains the statement when `.rejected err` occurs, and rejects
    double-finalize with `.misuse`. -/
def test_sqliteraw_finalize_releasesStmtEvenOnStickyErrorAndRejectsDoubleFinalize
    {runner} [NondetTest runner]
    (mkRaw : CSqliteOpsM (StateM MockCState) UInt64 UInt64 → RawSqliteOpsM (StateM MockCState)) : runner Unit := do
  let code ← nondet UInt32
  let detail ← nondet String
  let ops := mkRaw mockCOps
  let sh : StmtHandle := { id := 1, dbId := 1 }

  let (rOk, s1) := (ops.finalize sh).run (mockStateWithOpenStmt)
  let (rDup, s2) := (ops.finalize sh).run s1
  NondetTest.assert (rOk = .ok () ∧ s1.liveRawStmts = [] ∧ (ops.activeStmtCount.run s1).1 = 0 ∧
    (∃ e, rDup = .error e ∧ e.kind = .misuse) ∧ (ops.activeStmtCount.run s2).1 = 0)

  let sStickyInit := mockStateWithOpenStmt 0 [] #[]
    (.finalizeResult (.finalized (some (.constraint code detail))))
  let (rSticky, sSticky1) := (ops.finalize sh).run sStickyInit
  let (rCloseAfterSticky, sSticky2) := (ops.closeDb { id := 1 }).run { sSticky1 with failStep := .none }
  NondetTest.assert ((∃ e, rSticky = .error e ∧ e.kind = .constraint) ∧
    sSticky1.liveRawStmts = [] ∧ (ops.activeStmtCount.run sSticky1).1 = 0 ∧
    rCloseAfterSticky = .ok () ∧ (ops.activeDbCount.run sSticky2).1 = 0)

  let sRejInit := mockStateWithOpenStmt 0 [] #[]
    (.finalizeResult (.rejected (.busy code detail)))
  let (rRej, sRej1) := (ops.finalize sh).run sRejInit
  NondetTest.assert ((∃ e, rRej = .error e ∧ e.kind = .busy) ∧
    sRej1.liveRawStmts = [(100, 200)] ∧ (ops.activeStmtCount.run sRej1).1 = 1)

end LeanSwe.Sqlite
