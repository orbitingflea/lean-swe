import Core.Obeys
import LeanSwe.Sqlite.Types
import LeanSweProofs.Sqlite.Model.PureSpec
import LeanSweProofs.Sqlite.Model.World
import LeanSweProofs.Sqlite.Model.Refines
import LeanSwe.Sqlite.Impl
import LeanSwe.Sqlite.Interface

namespace LeanSwe.Sqlite.Proofs

open LeanSwe.Sqlite

private theorem dite_true_eq {α : Sort _} {P : Prop} [Decidable P] (h : P)
    (t : P → α) (e : ¬ P → α) : (if hp : P then t hp else e hp) = t h := by
  split
  · rfl
  · next hn => exact absurd h hn

private theorem dite_false_eq {α : Sort _} {P : Prop} [Decidable P] (h : ¬ P)
    (t : P → α) (e : ¬ P → α) : (if hp : P then t hp else e hp) = e h := by
  split
  · next hp => exact absurd hp h
  · rfl

private theorem ite_true_eq {α : Sort _} {P : Prop} [Decidable P] (h : P)
    (t e : α) : (if P then t else e) = t := by
  split
  · rfl
  · next hn => exact absurd h hn

private theorem ite_false_eq {α : Sort _} {P : Prop} [Decidable P] (h : ¬ P)
    (t e : α) : (if P then t else e) = e := by
  split
  · next hp => exact absurd hp h
  · rfl

/-- `Internal.mapRawError` equals `Model.mapRawError`. -/
theorem internal_mapRawError_eq : Internal.mapRawError = Model.mapRawError := by
  funext err
  cases err <;> rfl

/-- Public `mapRawError` satisfies `Core.ObeysPureEq` against `Model.mapRawError`. -/
theorem mapRawError_obeys : Core.ObeysPureEq mapRawError Model.mapRawError := by
  intro err
  cases err <;> rfl

private theorem attachOpenPath_eq : Internal.attachOpenPath = Model.attachOpenPathModel := by
  funext path err
  cases err with
  | cantOpen p? c d => cases p? <;> rfl
  | _ => rfl

private theorem hasZeroByteBaAux_eq (bs : ByteArray) (idx rem : Nat) :
    Internal.hasZeroByteBaAux bs idx rem = Model.hasZeroByteBaAuxModel bs idx rem := by
  induction rem generalizing idx with
  | zero => rfl
  | succ r ih =>
    dsimp only [Internal.hasZeroByteBaAux, Model.hasZeroByteBaAuxModel]
    by_cases h : idx < bs.size
    · rw [dite_true_eq h, dite_true_eq h, ih (idx + 1)]
    · rw [dite_false_eq h, dite_false_eq h]

private theorem hasZeroByteBa_eq : Internal.hasZeroByteBa = Model.hasZeroByteBaModel := by
  funext bs idx
  exact hasZeroByteBaAux_eq bs idx (bs.size - idx)

private theorem computeOpenFlags_eq :
    Internal.computeOpenFlags = Model.computeOpenFlagsModel := rfl

private theorem hexByteVal_eq : Internal.hexByteVal? = Model.hexByteValModel? := rfl

private theorem feedUriMatchByte_eq :
    Internal.feedUriMatchByte = Model.feedUriMatchByteModel := rfl

private def mapUriState : Internal.UriDecodeState → Model.UriDecodeStateModel
  | .normal => .normal
  | .sawPct => .sawPct
  | .sawPctHex hi hv => .sawPctHex hi hv

private theorem decodeUriMatchBaAux_eq (bs : ByteArray) (stop : Nat)
    (st : Internal.UriDecodeState) (rem? : Option (List UInt8)) (idx fuel : Nat) :
    Internal.decodeUriMatchBaAux bs stop st rem? idx fuel =
      Model.decodeUriMatchBaAuxModel bs stop (mapUriState st) rem? idx fuel := by
  induction fuel generalizing st rem? idx with
  | zero =>
    cases st <;> rfl
  | succ f ih =>
    cases st with
    | normal =>
      dsimp only [mapUriState, Internal.decodeUriMatchBaAux, Model.decodeUriMatchBaAuxModel]
      by_cases h : idx < stop ∧ idx < bs.size
      · rw [dite_true_eq h, dite_true_eq h, feedUriMatchByte_eq,
          ih .sawPct rem? (idx + 1),
          ih .normal (Model.feedUriMatchByteModel rem? bs[idx]) (idx + 1)]
        rfl
      · rw [dite_false_eq h, dite_false_eq h]
    | sawPct =>
      dsimp only [mapUriState, Internal.decodeUriMatchBaAux, Model.decodeUriMatchBaAuxModel]
      by_cases h : idx < stop ∧ idx < bs.size
      · rw [dite_true_eq h, dite_true_eq h, hexByteVal_eq, feedUriMatchByte_eq]
        cases Model.hexByteValModel? bs[idx] with
        | some v1 =>
          exact ih (.sawPctHex bs[idx] v1) rem? (idx + 1)
        | none =>
          dsimp only
          rw [ih .sawPct (Model.feedUriMatchByteModel rem? 0x25) (idx + 1),
            ih .normal (Model.feedUriMatchByteModel (Model.feedUriMatchByteModel rem? 0x25) bs[idx]) (idx + 1)]
          rfl
      · rw [dite_false_eq h, dite_false_eq h, feedUriMatchByte_eq]
    | sawPctHex hi v1 =>
      dsimp only [mapUriState, Internal.decodeUriMatchBaAux, Model.decodeUriMatchBaAuxModel]
      by_cases h : idx < stop ∧ idx < bs.size
      · rw [dite_true_eq h, dite_true_eq h, hexByteVal_eq, feedUriMatchByte_eq]
        cases Model.hexByteValModel? bs[idx] with
        | some v2 =>
          dsimp only
          rw [ih .normal (Model.feedUriMatchByteModel rem? ((v1 <<< 4) ||| v2)) (idx + 1)]
          rfl
        | none =>
          dsimp only
          rw [ih .sawPct (Model.feedUriMatchByteModel (Model.feedUriMatchByteModel rem? 0x25) hi) (idx + 1),
            ih .normal
              (Model.feedUriMatchByteModel
                (Model.feedUriMatchByteModel (Model.feedUriMatchByteModel rem? 0x25) hi) bs[idx])
              (idx + 1)]
          rfl
      · rw [dite_false_eq h, dite_false_eq h, feedUriMatchByte_eq]

private theorem decodeUriMatchBa_eq (bs : ByteArray) (start stop : Nat) (pat : List UInt8) :
    Internal.decodeUriMatchBa bs start stop pat = Model.decodeUriMatchBaModel bs start stop pat :=
  decodeUriMatchBaAux_eq bs stop .normal (some pat) start (stop - start)

private theorem findByteBeforeAux_eq (bs : ByteArray) (delim : UInt8) (stop idx fuel : Nat) :
    Internal.findByteBeforeAux bs delim stop idx fuel =
      Model.findByteBeforeAuxModel bs delim stop idx fuel := by
  induction fuel generalizing idx with
  | zero => rfl
  | succ f ih =>
    dsimp only [Internal.findByteBeforeAux, Model.findByteBeforeAuxModel]
    by_cases h : idx < stop ∧ idx < bs.size
    · rw [dite_true_eq h, dite_true_eq h, ih (idx + 1)]
    · rw [dite_false_eq h, dite_false_eq h]

private theorem findByteBefore_eq (bs : ByteArray) (delim : UInt8) (idx stop : Nat) :
    Internal.findByteBefore bs delim idx stop = Model.findByteBeforeModel bs delim idx stop :=
  findByteBeforeAux_eq bs delim stop idx (stop - idx)

private theorem stripAuthorityIdx_eq (bs : ByteArray) (start stop : Nat) :
    Internal.stripAuthorityIdx bs start stop = Model.stripAuthorityIdxModel bs start stop := by
  simp only [Internal.stripAuthorityIdx, Model.stripAuthorityIdxModel, findByteBefore_eq]

private theorem extractLastUriModeFlagsBaAux_eq (bs : ByteArray) (stop : Nat)
    (cur : Bool × Bool) (idx fuel : Nat) :
    Internal.extractLastUriModeFlagsBaAux bs stop cur idx fuel =
      Model.extractLastUriModeFlagsBaAuxModel bs stop cur idx fuel := by
  induction fuel generalizing cur idx with
  | zero => rfl
  | succ f ih =>
    dsimp only [Internal.extractLastUriModeFlagsBaAux, Model.extractLastUriModeFlagsBaAuxModel]
    simp only [findByteBefore_eq, decodeUriMatchBa_eq,
      Internal.modeKeyBytes, Model.modeKeyBytesModel,
      Internal.memoryModeBytes, Model.memoryModeBytesModel,
      Internal.roModeBytes, Model.roModeBytesModel]
    by_cases h : Model.findByteBeforeModel bs 0x26 idx stop < stop
    · rw [ite_true_eq h, ite_true_eq h]
      exact ih _ _
    · rw [ite_false_eq h, ite_false_eq h]
      rfl

private theorem classifyPathBytesBa_eq (bs : ByteArray) :
    Internal.classifyPathBytesBa bs = Model.classifyPathBytesBaModel bs := by
  unfold Internal.classifyPathBytesBa Model.classifyPathBytesBaModel
  simp only [Internal.isExactColonMemoryBa, Model.isExactColonMemoryBaModel,
    Internal.hasFileSchemeBa, Model.hasFileSchemeBaModel,
    findByteBefore_eq, stripAuthorityIdx_eq, decodeUriMatchBa_eq,
    extractLastUriModeFlagsBaAux_eq,
    Internal.colonMemoryColonBytes, Model.colonMemoryColonBytesModel]
  rfl

private theorem shouldEnableWal_eq : Internal.shouldEnableWal = Model.shouldEnableWalModel := by
  funext path cfg
  simp only [Internal.shouldEnableWal, Model.shouldEnableWalModel, classifyPathBytesBa_eq]

private def mapSqlState : Internal.SqlTailScanState → Model.SqlTailScanStateModel
  | .normal => .normal
  | .inSpace => .inSpace
  | .sawDash => .sawDash
  | .inLineComment => .inLineComment
  | .sawSlash => .sawSlash
  | .inBlockComment => .inBlockComment
  | .inBlockSawStar => .inBlockSawStar
  | .sawBom1 => .sawBom1
  | .sawBom2 => .sawBom2

private theorem scanSqlTailBaAux_eq (st : Internal.SqlTailScanState)
    (bs : ByteArray) (idx rem : Nat) :
    Internal.scanSqlTailBaAux st bs idx rem =
      Model.scanSqlTailBaAuxModel (mapSqlState st) bs idx rem := by
  induction rem generalizing st idx with
  | zero =>
    cases st <;> rfl
  | succ r ih =>
    cases st <;>
      dsimp only [mapSqlState, Internal.scanSqlTailBaAux, Model.scanSqlTailBaAuxModel] <;>
      (by_cases h : idx < bs.size;
       · rw [dite_true_eq h, dite_true_eq h];
         simp only [Internal.isSqlAsciiSpace, Model.isSqlAsciiSpaceModel,
           ih .normal (idx + 1), ih .inSpace (idx + 1), ih .sawDash (idx + 1),
           ih .inLineComment (idx + 1), ih .sawSlash (idx + 1), ih .inBlockComment (idx + 1),
           ih .inBlockSawStar (idx + 1), ih .sawBom1 (idx + 1), ih .sawBom2 (idx + 1)];
         rfl
       · rw [dite_false_eq h, dite_false_eq h])

private theorem scanSqlTailBa_normal_eq (bs : ByteArray) (idx : Nat) :
    Internal.scanSqlTailBa .normal bs idx = Model.scanSqlTailBaModel .normal bs idx :=
  scanSqlTailBaAux_eq .normal bs idx (bs.size - idx)

private theorem lookupRawDb_eq (dbId : UInt64) (dbs : List (UInt64 × UInt64)) :
    Internal.lookupRawDb dbId dbs = Model.lookupRawDbModel dbId dbs := by
  induction dbs with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨id, h⟩
    simp only [Internal.lookupRawDb, Model.lookupRawDbModel, ih]

private theorem eraseRawDbAux_eq (dbId : UInt64)
    (acc dbs : List (UInt64 × UInt64)) :
    Internal.eraseRawDbAux dbId acc dbs = Model.eraseRawDbAuxModel dbId acc dbs := by
  induction dbs generalizing acc with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨id, h⟩
    simp only [Internal.eraseRawDbAux, Model.eraseRawDbAuxModel, ih ((id, h) :: acc)]

private theorem eraseRawDb_eq (dbId : UInt64) (dbs : List (UInt64 × UInt64)) :
    Internal.eraseRawDb dbId dbs = Model.eraseRawDbModel dbId dbs :=
  eraseRawDbAux_eq dbId [] dbs

private theorem lookupRawStmt_eq (stmt : StmtHandle) (stmts : List (StmtHandle × UInt64)) :
    Internal.lookupRawStmt stmt stmts = Model.lookupRawStmtModel stmt stmts := by
  induction stmts with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨sh, h⟩
    simp only [Internal.lookupRawStmt, Model.lookupRawStmtModel, ih]

private theorem eraseRawStmtAux_eq (stmt : StmtHandle)
    (acc stmts : List (StmtHandle × UInt64)) :
    Internal.eraseRawStmtAux stmt acc stmts = Model.eraseRawStmtAuxModel stmt acc stmts := by
  induction stmts generalizing acc with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨sh, h⟩
    simp only [Internal.eraseRawStmtAux, Model.eraseRawStmtAuxModel, ih ((sh, h) :: acc)]

private theorem eraseRawStmt_eq (stmt : StmtHandle) (stmts : List (StmtHandle × UInt64)) :
    Internal.eraseRawStmt stmt stmts = Model.eraseRawStmtModel stmt stmts :=
  eraseRawStmtAux_eq stmt [] stmts

private theorem hasActiveStmtForDb_eq (dbId : UInt64) (stmts : List (StmtHandle × UInt64)) :
    Internal.hasActiveStmtForDb dbId stmts = Model.hasActiveStmtForDbModel dbId stmts := by
  induction stmts with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨sh, h⟩
    simp only [Internal.hasActiveStmtForDb, Model.hasActiveStmtForDbModel, ih]

private theorem modify_eraseDb_eq {m : Type → Type} (cops : CSqliteOpsM m UInt64 UInt64) (dbId : UInt64) :
    cops.modifyTable (fun t : RawHandleTable UInt64 UInt64 => ((), { t with dbs := Internal.eraseRawDb dbId t.dbs })) =
      cops.modifyTable (Model.tableEraseDb dbId) := by
  congr 1
  funext t
  simp only [Model.tableEraseDb, eraseRawDb_eq]

private theorem modify_lookupDb_eq {m : Type → Type} (cops : CSqliteOpsM m UInt64 UInt64) (dbId : UInt64) :
    cops.modifyTable (fun t : RawHandleTable UInt64 UInt64 => (Internal.lookupRawDb dbId t.dbs, t)) =
      cops.modifyTable (Model.tableLookupDb dbId) := by
  congr 1
  funext t
  simp only [Model.tableLookupDb, lookupRawDb_eq]

private theorem modify_lookupStmt_eq {m : Type → Type} (cops : CSqliteOpsM m UInt64 UInt64) (stmt : StmtHandle) :
    cops.modifyTable (fun t : RawHandleTable UInt64 UInt64 => (Internal.lookupRawStmt stmt t.stmts, t)) =
      cops.modifyTable (Model.tableLookupStmt stmt) := by
  congr 1
  funext t
  simp only [Model.tableLookupStmt, lookupRawStmt_eq]

private theorem modify_eraseStmt_eq {m : Type → Type} (cops : CSqliteOpsM m UInt64 UInt64) (stmt : StmtHandle) :
    cops.modifyTable (fun t : RawHandleTable UInt64 UInt64 => ((), { t with stmts := Internal.eraseRawStmt stmt t.stmts })) =
      cops.modifyTable (Model.tableEraseStmt stmt) := by
  congr 1
  funext t
  simp only [Model.tableEraseStmt, eraseRawStmt_eq]

private theorem stepPragmaLoop_eq {m : Type → Type} [Monad m] (cops : CSqliteOpsM m UInt64 UInt64)
    (rawStmt : UInt64) (fuel : Nat) :
    Internal.stepPragmaLoop cops rawStmt fuel = Model.stepPragmaLoopModel cops rawStmt fuel := by
  induction fuel with
  | zero => rfl
  | succ f ih =>
    simp only [Internal.stepPragmaLoop, Model.stepPragmaLoopModel, ih]
    rfl

private theorem runSetupPragma_eq {m : Type → Type} [Monad m] [MonadFinally m]
    (cops : CSqliteOpsM m UInt64 UInt64) (rawDb : UInt64) (sql : String) :
    Internal.runSetupPragma cops rawDb sql = Model.runSetupPragmaModel cops rawDb sql := by
  simp only [Internal.runSetupPragma, Model.runSetupPragmaModel, stepPragmaLoop_eq]
  congr 1
  funext r
  rcases r with _ | ⟨_ | _, _⟩ <;> rfl

private theorem setupConnection_eq {m : Type → Type} [Monad m] [MonadFinally m]
    (cops : CSqliteOpsM m UInt64 UInt64) (path : String) (cfg : OpenConfig) (rawDb : UInt64) :
    Internal.setupConnection cops path cfg rawDb =
      Model.setupConnectionModel cops path cfg rawDb := by
  simp only [Internal.setupConnection, Model.setupConnectionModel,
    runSetupPragma_eq, shouldEnableWal_eq]
  rfl

private theorem bindOneParam_eq {m : Type → Type} (cops : CSqliteOpsM m UInt64 UInt64)
    (rawStmt : UInt64) (idx : UInt32) (v : SqliteValue) :
    Internal.bindOneParam cops rawStmt idx v = Model.bindOneParamModel cops rawStmt idx v := by
  cases v <;> rfl

private theorem bindLoop_eq {m : Type → Type} [Monad m] (cops : CSqliteOpsM m UInt64 UInt64)
    (rawStmt : UInt64) (params : Array SqliteValue) (rem : Nat) :
    Internal.bindLoop cops rawStmt params rem = Model.bindLoopModel cops rawStmt params rem := by
  induction rem with
  | zero => rfl
  | succ r ih =>
    simp only [Internal.bindLoop, Model.bindLoopModel, bindOneParam_eq,
      internal_mapRawError_eq, ih]
    rfl

private theorem decodeColumns_eq {m : Type → Type} [Monad m] (cops : CSqliteOpsM m UInt64 UInt64)
    (rawStmt : UInt64) (total rem : Nat) (acc : Array SqliteValue) :
    Internal.decodeColumns cops rawStmt total rem acc =
      Model.decodeColumnsModel cops rawStmt total rem acc := by
  induction rem generalizing acc with
  | zero => rfl
  | succ r ih =>
    unfold Internal.decodeColumns Model.decodeColumnsModel
    simp only [internal_mapRawError_eq, ih]
    rfl

private theorem withStmtLock_eq {m : Type → Type} [Monad m] [MonadFinally m]
    (cops : CSqliteOpsM m UInt64 UInt64) {α : Type} (stmt : StmtHandle) (act : m α) :
    Internal.withStmtLock cops stmt act = Model.withStmtLockModel cops stmt act :=
  rfl

private theorem mkRawOps_openDb_eq {m : Type → Type} [Monad m] [MonadFinally m]
    (cops : CSqliteOpsM m UInt64 UInt64) :
    (Internal.mkRawOps cops).openDb = (Model.mkRawOpsModel cops).openDb := by
  funext path cfg
  dsimp only [Internal.mkRawOps, Model.mkRawOpsModel]
  rw [internal_mapRawError_eq, attachOpenPath_eq, hasZeroByteBa_eq, computeOpenFlags_eq]
  simp only [setupConnection_eq]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · congr 1
          funext r
          cases r with
          | error _ => rfl
          | ok rawDb =>
            dsimp only
            congr 1

private theorem mkRawOps_closeDb_eq {m : Type → Type} [Monad m] [MonadFinally m]
    (cops : CSqliteOpsM m UInt64 UInt64) :
    (Internal.mkRawOps cops).closeDb = (Model.mkRawOpsModel cops).closeDb := by
  funext db
  dsimp only [Internal.mkRawOps, Model.mkRawOpsModel]
  rw [internal_mapRawError_eq]
  congr 1
  · congr 1
    funext t
    simp only [Model.tableCheckCloseDb, lookupRawDb_eq, hasActiveStmtForDb_eq]
    cases Model.lookupRawDbModel db.id t.dbs <;> rfl
  · funext lookupRes
    cases lookupRes with
    | error _ => rfl
    | ok rawDb =>
      dsimp only
      congr 1
      funext closeRes
      cases closeRes with
      | error _ => rfl
      | ok _ =>
        dsimp only
        rw [modify_eraseDb_eq cops db.id]

private theorem mkRawOps_prepare_eq {m : Type → Type} [Monad m] [MonadFinally m]
    (cops : CSqliteOpsM m UInt64 UInt64) :
    (Internal.mkRawOps cops).prepare = (Model.mkRawOpsModel cops).prepare := by
  funext db sql
  dsimp only [Internal.mkRawOps, Model.mkRawOpsModel]
  rw [internal_mapRawError_eq, hasZeroByteBa_eq, modify_lookupDb_eq cops db.id]
  congr 1
  congr 1
  congr 1
  funext rawDb?
  cases rawDb? with
  | none => rfl
  | some rawDb =>
    dsimp only
    congr 1
    funext prepRes
    cases prepRes with
    | error _ => rfl
    | ok pair =>
      rcases pair with ⟨stmt?, consumed⟩
      cases stmt? with
      | none => rfl
      | some rawStmt =>
        dsimp only
        rw [scanSqlTailBa_normal_eq sql.toUTF8 consumed]
        rfl

private theorem mkRawOps_bind_eq {m : Type → Type} [Monad m] [MonadFinally m]
    (cops : CSqliteOpsM m UInt64 UInt64) :
    (Internal.mkRawOps cops).bind = (Model.mkRawOpsModel cops).bind := by
  funext stmt params
  dsimp only [Internal.mkRawOps, Model.mkRawOpsModel]
  rw [withStmtLock_eq]
  apply congrArg (Model.withStmtLockModel cops stmt)
  rw [modify_lookupStmt_eq cops stmt, internal_mapRawError_eq]
  congr 1
  funext rawStmt?
  cases rawStmt? with
  | none => rfl
  | some rawStmt =>
    dsimp only
    congr 1
    funext r1
    cases r1 with
    | error _ => rfl
    | ok _ =>
      dsimp only
      congr 1
      funext r2
      cases r2 with
      | error _ => rfl
      | ok _ =>
        dsimp only
        congr 1
        funext r3
        cases r3 with
        | error _ => rfl
        | ok _ =>
          dsimp only
          rw [bindLoop_eq cops rawStmt params params.size]

private theorem mkRawOps_step_eq {m : Type → Type} [Monad m] [MonadFinally m]
    (cops : CSqliteOpsM m UInt64 UInt64) :
    (Internal.mkRawOps cops).step = (Model.mkRawOpsModel cops).step := by
  funext stmt
  dsimp only [Internal.mkRawOps, Model.mkRawOpsModel]
  rw [withStmtLock_eq]
  apply congrArg (Model.withStmtLockModel cops stmt)
  rw [modify_lookupStmt_eq cops stmt, internal_mapRawError_eq]
  congr 1
  funext rawStmt?
  cases rawStmt? with
  | none => rfl
  | some rawStmt =>
    dsimp only
    congr 1
    funext stRes
    cases stRes with
    | error _ => rfl
    | ok tag =>
      cases tag with
      | done => rfl
      | row =>
        dsimp only
        congr 1
        funext cntRes
        cases cntRes with
        | error _ => rfl
        | ok cnt =>
          dsimp only
          rw [decodeColumns_eq cops rawStmt cnt.toNat cnt.toNat #[]]
          rfl

private theorem mkRawOps_finalize_eq {m : Type → Type} [Monad m] [MonadFinally m]
    (cops : CSqliteOpsM m UInt64 UInt64) :
    (Internal.mkRawOps cops).finalize = (Model.mkRawOpsModel cops).finalize := by
  funext stmt
  dsimp only [Internal.mkRawOps, Model.mkRawOpsModel]
  rw [withStmtLock_eq]
  apply congrArg (Model.withStmtLockModel cops stmt)
  rw [modify_lookupStmt_eq cops stmt, internal_mapRawError_eq]
  congr 1
  funext rawStmt?
  cases rawStmt? with
  | none => rfl
  | some rawStmt =>
    dsimp only
    congr 1
    funext finOut
    cases finOut with
    | finalized _ =>
      dsimp only
      rw [modify_eraseStmt_eq cops stmt]
      rfl
    | rejected _ => rfl

/-- `Internal.mkRawOps cops` equals `Model.mkRawOpsModel cops` for every monad `m` and `cops`. -/
theorem mkRawOps_eq_model {m : Type → Type} [Monad m] [MonadFinally m]
    (cops : CSqliteOpsM m UInt64 UInt64) :
    Internal.mkRawOps cops = Model.mkRawOpsModel cops := by
  have hMap : (Internal.mkRawOps cops).mapRawError = (Model.mkRawOpsModel cops).mapRawError :=
    internal_mapRawError_eq
  have hOpen := mkRawOps_openDb_eq cops
  have hClose := mkRawOps_closeDb_eq cops
  have hPrep := mkRawOps_prepare_eq cops
  have hBind := mkRawOps_bind_eq cops
  have hStep := mkRawOps_step_eq cops
  have hFin := mkRawOps_finalize_eq cops
  have hDbCnt : (Internal.mkRawOps cops).activeDbCount = (Model.mkRawOpsModel cops).activeDbCount := rfl
  have hStCnt : (Internal.mkRawOps cops).activeStmtCount = (Model.mkRawOpsModel cops).activeStmtCount := rfl
  cases hI : Internal.mkRawOps cops
  cases hM : Model.mkRawOpsModel cops
  rw [hI, hM] at hMap hOpen hClose hPrep hBind hStep hFin hDbCnt hStCnt
  dsimp only at hMap hOpen hClose hPrep hBind hStep hFin hDbCnt hStCnt
  subst hMap hOpen hClose hPrep hBind hStep hFin hDbCnt hStCnt
  rfl

end LeanSwe.Sqlite.Proofs
