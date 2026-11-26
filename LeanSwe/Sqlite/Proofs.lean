import Core.Assumptions
import Core.Obeys
import LeanSwe.Sqlite.Model
import LeanSwe.Sqlite.Interface

namespace LeanSwe.Sqlite.Proofs

open LeanSwe.Sqlite

private theorem validateConfig_never (k : SqliteErrorKind) (hk : k ≠ .invalidInput) (cfg : OpenConfig) :
    Core.NeverErrorKindPure Raw.SqliteError.kind k (LeanSwe.Sqlite.validateConfig cfg) := by
  unfold LeanSwe.Sqlite.validateConfig defaultApi Internal.mkApiM Internal.validateConfigWith
    Raw.defaultOps Raw.Internal.mkRawOps Raw.Internal.mapRawError
  dsimp only
  split
  · exact hk.symm
  · split
    · exact hk.symm
    · trivial

/-- `LeanSwe.Sqlite.validateConfig` never returns `.notFound`. -/
theorem sqlite_validateConfig_never_notFound (cfg : OpenConfig) :
    Core.NeverErrorKindPure Raw.SqliteError.kind .notFound (LeanSwe.Sqlite.validateConfig cfg) :=
  validateConfig_never .notFound (by decide) cfg

/-- `LeanSwe.Sqlite.validateConfig` never returns `.busy`. -/
theorem sqlite_validateConfig_never_busy (cfg : OpenConfig) :
    Core.NeverErrorKindPure Raw.SqliteError.kind .busy (LeanSwe.Sqlite.validateConfig cfg) :=
  validateConfig_never .busy (by decide) cfg

/-- `LeanSwe.Sqlite.validateConfig` never returns `.constraint`. -/
theorem sqlite_validateConfig_never_constraint (cfg : OpenConfig) :
    Core.NeverErrorKindPure Raw.SqliteError.kind .constraint (LeanSwe.Sqlite.validateConfig cfg) :=
  validateConfig_never .constraint (by decide) cfg

/-- `LeanSwe.Sqlite.validateConfig` never returns `.misuse`. -/
theorem sqlite_validateConfig_never_misuse (cfg : OpenConfig) :
    Core.NeverErrorKindPure Raw.SqliteError.kind .misuse (LeanSwe.Sqlite.validateConfig cfg) :=
  validateConfig_never .misuse (by decide) cfg

/-- `LeanSwe.Sqlite.validateConfig` never returns `.ioError`. -/
theorem sqlite_validateConfig_never_ioError (cfg : OpenConfig) :
    Core.NeverErrorKindPure Raw.SqliteError.kind .ioError (LeanSwe.Sqlite.validateConfig cfg) :=
  validateConfig_never .ioError (by decide) cfg

/-- `defaultApi` agrees definitionally with `Internal.mkApiM Raw.defaultOps`. -/
theorem sqlite_defaultApi_eq_mkApiM_defaultOps :
    defaultApi = Internal.mkApiM Raw.defaultOps := rfl

/-- Every operation field of `defaultApi` agrees definitionally with `Internal.mkApiM Raw.defaultOps`. -/
theorem sqlite_defaultApi_fields_wired :
    defaultApi.mapRawError = (Internal.mkApiM Raw.defaultOps).mapRawError ∧
    defaultApi.validateConfig = (Internal.mkApiM Raw.defaultOps).validateConfig ∧
    (∀ {α : Type} (path : String) (cfg : OpenConfig) (action : DbHandle → IO (Except SqliteError α)),
      defaultApi.withDb path cfg action = Internal.withDbOp Raw.defaultOps path cfg action) ∧
    (∀ {α : Type} (db : DbHandle) (action : DbHandle → IO (Except SqliteError α)),
      defaultApi.withTransaction db action = Internal.withTransactionOp Raw.defaultOps db action) ∧
    (∀ db sql params, defaultApi.exec db sql params = Internal.execOp Raw.defaultOps db sql params) ∧
    (∀ db sql params, defaultApi.query db sql params = Internal.queryOp Raw.defaultOps db sql params) ∧
    (∀ db sql params, defaultApi.queryOne db sql params = Internal.queryOneOp Raw.defaultOps db sql params) ∧
    defaultApi.activeDbCount = Raw.defaultOps.activeDbCount ∧
    defaultApi.activeStmtCount = Raw.defaultOps.activeStmtCount :=
  ⟨rfl, rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl,
   fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl⟩

private theorem validateConfigWith_eq_model (f : SqliteRawError → SqliteError) :
    Internal.validateConfigWith f = Model.validateConfigWith f := by
  funext cfg
  unfold Internal.validateConfigWith Model.validateConfigWith Model.validateConfigRaw
  cases cfg.readOnly <;> cases cfg.createIfMissing <;>
    by_cases hGT : (cfg.busyTimeoutMs > maxBusyTimeoutMs) <;>
    simp [hGT, Except.mapError]

private theorem modelExecLoop_eq (ops : RawSqliteOpsM (StateM Model.SqliteWorldState))
    (stmt : StmtHandle) (fuel : Nat) :
    Model.modelExecLoop ops stmt fuel = Internal.execLoop ops stmt fuel := by
  induction fuel generalizing stmt with
  | zero => rfl
  | succ f ih =>
    simp only [Model.modelExecLoop, Internal.execLoop]
    congr 1
    funext res
    cases res with
    | error _ => rfl
    | ok sr =>
      cases sr with
      | done => rfl
      | row _ => exact ih stmt

private theorem modelQueryLoop_eq (ops : RawSqliteOpsM (StateM Model.SqliteWorldState))
    (stmt : StmtHandle) (acc : Array SqliteRow) (fuel : Nat) :
    Model.modelQueryLoop ops stmt acc fuel = Internal.queryLoop ops stmt acc fuel := by
  induction fuel generalizing stmt acc with
  | zero => rfl
  | succ f ih =>
    simp only [Model.modelQueryLoop, Internal.queryLoop]
    congr 1
    funext res
    cases res with
    | error _ => rfl
    | ok sr =>
      cases sr with
      | done => rfl
      | row cols => exact ih stmt (acc.push cols)

private theorem modelExecMaybeBind_eq (ops : RawSqliteOpsM (StateM Model.SqliteWorldState))
    (db : DbHandle) (sql : String) (params? : Option (Array SqliteValue)) :
    Model.modelExecMaybeBind ops db sql params? = Internal.execMaybeBindOp ops db sql params? := by
  dsimp only [Model.modelExecMaybeBind, Internal.execMaybeBindOp]
  rw [show Internal.maxStepFuel = 100000000 from rfl]
  simp only [modelExecLoop_eq]
  rfl

private theorem mk_SqliteApiM_eq {m : Type → Type}
    {f1 f1' : SqliteRawError → SqliteError}
    {f2 f2' : OpenConfig → Except SqliteError Unit}
    {f3 f3' : {α : Type} → String → OpenConfig → (DbHandle → m (Except SqliteError α)) → m (Except SqliteError α)}
    {f4 f4' : {α : Type} → DbHandle → (DbHandle → m (Except SqliteError α)) → m (Except SqliteError α)}
    {f5 f5' : DbHandle → String → Array SqliteValue → m (Except SqliteError Unit)}
    {f6 f6' : DbHandle → String → Array SqliteValue → m (Except SqliteError (Array SqliteRow))}
    {f7 f7' : DbHandle → String → Array SqliteValue → m (Except SqliteError (Option SqliteRow))}
    {f8 f8' : m Nat}
    {f9 f9' : m Nat}
    (h1 : f1 = f1') (h2 : f2 = f2') (h3 : @f3 = @f3') (h4 : @f4 = @f4')
    (h5 : f5 = f5') (h6 : f6 = f6') (h7 : f7 = f7') (h8 : f8 = f8') (h9 : f9 = f9') :
    (⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ : SqliteApiM m) =
      ⟨f1', f2', f3', f4', f5', f6', f7', f8', f9'⟩ := by
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9
  rfl

/-- `Internal.mkApiM Model.modelRawOps` equals `Model.modelApi` across every `SqliteApiM` operation. -/
theorem sqlite_mkApiM_modelRawOps_eq_modelApi :
    Internal.mkApiM Model.modelRawOps = Model.modelApi := by
  have hCfg : Internal.validateConfigWith Model.modelRawOps.mapRawError = Model.modelApi.validateConfig :=
    validateConfigWith_eq_model Model.modelRawOps.mapRawError
  have hDb : @Internal.withDbOp (StateM Model.SqliteWorldState) _ _ Model.modelRawOps =
      @Model.modelApi.withDb := by
    funext α path cfg action
    simp only [Internal.withDbOp, Model.modelApi, validateConfigWith_eq_model]
    rfl
  have hTx : @Internal.withTransactionOp (StateM Model.SqliteWorldState) _ _ Model.modelRawOps =
      @Model.modelApi.withTransaction := by
    funext α db action
    simp only [Internal.withTransactionOp, Model.modelApi, modelExecMaybeBind_eq]
    rfl
  have hEx : Internal.execOp Model.modelRawOps = Model.modelApi.exec := by
    funext db sql params
    simp only [Internal.execOp, Model.modelApi, modelExecMaybeBind_eq]
  have hQu : Internal.queryOp Model.modelRawOps = Model.modelApi.query := by
    funext db sql params
    simp only [Internal.queryOp, Model.modelApi, show Internal.maxStepFuel = 100000000 from rfl,
      modelQueryLoop_eq]
    rfl
  exact mk_SqliteApiM_eq rfl hCfg hDb hTx hEx hQu rfl rfl rfl

/-- Public `LeanSwe.Sqlite.mapRawError` agrees definitionally with `Raw.defaultOps.mapRawError`. -/
theorem sqlite_mapRawError_eq (err : SqliteRawError) :
    LeanSwe.Sqlite.mapRawError err = Raw.defaultOps.mapRawError err := rfl

/-- Public `LeanSwe.Sqlite.withDb` agrees definitionally with `Internal.withDbOp Raw.defaultOps`. -/
theorem sqlite_withDb_eq {α : Type} (path : String) (cfg : OpenConfig)
    (action : DbHandle → IO (Except SqliteError α)) :
    LeanSwe.Sqlite.withDb path cfg action = Internal.withDbOp Raw.defaultOps path cfg action := rfl

/-- Public `LeanSwe.Sqlite.withDb` with default configuration agrees with `Internal.withDbOp Raw.defaultOps path {}`. -/
theorem sqlite_withDb_default_eq {α : Type} (path : String)
    (action : DbHandle → IO (Except SqliteError α)) :
    LeanSwe.Sqlite.withDb path (action := action) = Internal.withDbOp Raw.defaultOps path {} action := rfl

/-- Public `LeanSwe.Sqlite.withTransaction` agrees definitionally with `Internal.withTransactionOp Raw.defaultOps`. -/
theorem sqlite_withTransaction_eq {α : Type} (db : DbHandle)
    (action : DbHandle → IO (Except SqliteError α)) :
    LeanSwe.Sqlite.withTransaction db action = Internal.withTransactionOp Raw.defaultOps db action := rfl

/-- Public `LeanSwe.Sqlite.exec` agrees definitionally with `Internal.execOp Raw.defaultOps`. -/
theorem sqlite_exec_eq (db : DbHandle) (sql : String) (params : Array SqliteValue) :
    LeanSwe.Sqlite.exec db sql params = Internal.execOp Raw.defaultOps db sql params := rfl

/-- Public `LeanSwe.Sqlite.exec` with default empty parameters agrees with `Internal.execOp Raw.defaultOps db sql #[]`. -/
theorem sqlite_exec_default_eq (db : DbHandle) (sql : String) :
    LeanSwe.Sqlite.exec db sql = Internal.execOp Raw.defaultOps db sql #[] := rfl

/-- Public `LeanSwe.Sqlite.query` agrees definitionally with `Internal.queryOp Raw.defaultOps`. -/
theorem sqlite_query_eq (db : DbHandle) (sql : String) (params : Array SqliteValue) :
    LeanSwe.Sqlite.query db sql params = Internal.queryOp Raw.defaultOps db sql params := rfl

/-- Public `LeanSwe.Sqlite.query` with default empty parameters agrees with `Internal.queryOp Raw.defaultOps db sql #[]`. -/
theorem sqlite_query_default_eq (db : DbHandle) (sql : String) :
    LeanSwe.Sqlite.query db sql = Internal.queryOp Raw.defaultOps db sql #[] := rfl

/-- Public `LeanSwe.Sqlite.queryOne` agrees definitionally with `Internal.queryOneOp Raw.defaultOps`. -/
theorem sqlite_queryOne_eq (db : DbHandle) (sql : String) (params : Array SqliteValue) :
    LeanSwe.Sqlite.queryOne db sql params = Internal.queryOneOp Raw.defaultOps db sql params := rfl

/-- Public `LeanSwe.Sqlite.queryOne` with default empty parameters agrees with `Internal.queryOneOp Raw.defaultOps db sql #[]`. -/
theorem sqlite_queryOne_default_eq (db : DbHandle) (sql : String) :
    LeanSwe.Sqlite.queryOne db sql = Internal.queryOneOp Raw.defaultOps db sql #[] := rfl

/-- Public `LeanSwe.Sqlite.activeDbCount` agrees definitionally with `Raw.defaultOps.activeDbCount`. -/
theorem sqlite_activeDbCount_eq :
    LeanSwe.Sqlite.activeDbCount = Raw.defaultOps.activeDbCount := rfl

/-- Public `LeanSwe.Sqlite.activeStmtCount` agrees definitionally with `Raw.defaultOps.activeStmtCount`. -/
theorem sqlite_activeStmtCount_eq :
    LeanSwe.Sqlite.activeStmtCount = Raw.defaultOps.activeStmtCount := rfl

private theorem mapRawError_eq_model (err : SqliteRawError) :
    LeanSwe.Sqlite.mapRawError err = Model.mapRawError err := by
  cases err <;> rfl

private theorem validateConfig_eq_model (cfg : OpenConfig) :
    LeanSwe.Sqlite.validateConfig cfg = Model.validateConfig cfg := by
  change Internal.validateConfigWith LeanSwe.Sqlite.mapRawError cfg = Model.validateConfig cfg
  unfold Internal.validateConfigWith Model.validateConfig Model.validateConfigWith Model.validateConfigRaw
  by_cases hRo : (cfg.readOnly && cfg.createIfMissing) = true
  · simp [hRo, Except.mapError, mapRawError_eq_model]
  · have hRoF : (cfg.readOnly && cfg.createIfMissing) = false := by
      cases h : (cfg.readOnly && cfg.createIfMissing) <;> simp_all
    by_cases hBt : cfg.busyTimeoutMs > maxBusyTimeoutMs
    · simp [hRoF, hBt, Except.mapError, mapRawError_eq_model]
    · simp [hRoF, hBt, Except.mapError]

private theorem rawMapEq {W : Type} (proj : W → Model.SqliteWorldState)
    (raw : RawSqliteOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (w : W) (err : SqliteRawError) :
    raw.mapRawError err = Model.modelRawOps.mapRawError err := by
  have h := hRaw w (.mapRawError err) rfl
  simp only [Model.execRawStep, Raw.Model.execRawStep, Model.allowedRawStep, StateT.run,
    Pure.pure, StateT.pure] at h
  exact Raw.Model.RawStepOut.mapRawError.inj h.1

private theorem rawOpenEq {W : Type} (proj : W → Model.SqliteWorldState)
    (raw : RawSqliteOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (w : W) (path : String) (cfg : OpenConfig) :
    (raw.openDb path cfg w).1 = (Model.modelRawOps.openDb path cfg (proj w)).1 ∧
    proj (raw.openDb path cfg w).2 = (Model.modelRawOps.openDb path cfg (proj w)).2 := by
  have h := hRaw w (.openDb path cfg) rfl
  simp only [Model.execRawStep, Raw.Model.execRawStep, Model.allowedRawStep, StateT.run,
    Functor.map, StateT.map] at h
  exact ⟨Raw.Model.RawStepOut.openDb.inj h.1, h.2⟩

private theorem rawCloseEq {W : Type} (proj : W → Model.SqliteWorldState)
    (raw : RawSqliteOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (w : W) (db : DbHandle) :
    (raw.closeDb db w).1 = (Model.modelRawOps.closeDb db (proj w)).1 ∧
    proj (raw.closeDb db w).2 = (Model.modelRawOps.closeDb db (proj w)).2 := by
  have h := hRaw w (.closeDb db) rfl
  simp only [Model.execRawStep, Raw.Model.execRawStep, Model.allowedRawStep, StateT.run,
    Functor.map, StateT.map] at h
  exact ⟨Raw.Model.RawStepOut.closeDb.inj h.1, h.2⟩

private theorem rawPrepareEq {W : Type} (proj : W → Model.SqliteWorldState)
    (raw : RawSqliteOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (w : W) (db : DbHandle) (sql : String) :
    (raw.prepare db sql w).1 = (Model.modelRawOps.prepare db sql (proj w)).1 ∧
    proj (raw.prepare db sql w).2 = (Model.modelRawOps.prepare db sql (proj w)).2 := by
  have h := hRaw w (.prepare db sql) rfl
  simp only [Model.execRawStep, Raw.Model.execRawStep, Model.allowedRawStep, StateT.run,
    Functor.map, StateT.map] at h
  exact ⟨Raw.Model.RawStepOut.prepare.inj h.1, h.2⟩

private theorem rawBindEq {W : Type} (proj : W → Model.SqliteWorldState)
    (raw : RawSqliteOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (w : W) (stmt : StmtHandle) (params : Array SqliteValue) :
    (raw.bind stmt params w).1 = (Model.modelRawOps.bind stmt params (proj w)).1 ∧
    proj (raw.bind stmt params w).2 = (Model.modelRawOps.bind stmt params (proj w)).2 := by
  have h := hRaw w (.bind stmt params) rfl
  simp only [Model.execRawStep, Raw.Model.execRawStep, Model.allowedRawStep, StateT.run,
    Functor.map, StateT.map] at h
  exact ⟨Raw.Model.RawStepOut.bind.inj h.1, h.2⟩

private theorem rawStepEq {W : Type} (proj : W → Model.SqliteWorldState)
    (raw : RawSqliteOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (w : W) (stmt : StmtHandle) :
    (raw.step stmt w).1 = (Model.modelRawOps.step stmt (proj w)).1 ∧
    proj (raw.step stmt w).2 = (Model.modelRawOps.step stmt (proj w)).2 := by
  have h := hRaw w (.step stmt) rfl
  simp only [Model.execRawStep, Raw.Model.execRawStep, Model.allowedRawStep, StateT.run,
    Functor.map, StateT.map] at h
  exact ⟨Raw.Model.RawStepOut.step.inj h.1, h.2⟩

private theorem rawFinalizeEq {W : Type} (proj : W → Model.SqliteWorldState)
    (raw : RawSqliteOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (w : W) (stmt : StmtHandle) :
    (raw.finalize stmt w).1 = (Model.modelRawOps.finalize stmt (proj w)).1 ∧
    proj (raw.finalize stmt w).2 = (Model.modelRawOps.finalize stmt (proj w)).2 := by
  have h := hRaw w (.finalize stmt) rfl
  simp only [Model.execRawStep, Raw.Model.execRawStep, Model.allowedRawStep, StateT.run,
    Functor.map, StateT.map] at h
  exact ⟨Raw.Model.RawStepOut.finalize.inj h.1, h.2⟩

private theorem state_bind_refines {W S α β : Type} (proj : W → S)
    {x : StateM W α} {y : StateM S α} {k1 : α → StateM W β} {k2 : α → StateM S β}
    (w : W)
    (hx : (x w).1 = (y (proj w)).1 ∧ proj (x w).2 = (y (proj w)).2)
    (hk : ∀ (a : α) (w1 : W),
      (k1 a w1).1 = (k2 a (proj w1)).1 ∧ proj (k1 a w1).2 = (k2 a (proj w1)).2) :
    ((x >>= k1) w).1 = ((y >>= k2) (proj w)).1 ∧
    proj ((x >>= k1) w).2 = ((y >>= k2) (proj w)).2 := by
  change (k1 (x w).1 (x w).2).1 = (k2 (y (proj w)).1 (y (proj w)).2).1 ∧
    proj (k1 (x w).1 (x w).2).2 = (k2 (y (proj w)).1 (y (proj w)).2).2
  have h := hk (x w).1 (x w).2
  exact ⟨h.1.trans (by rw [hx.1, hx.2]), h.2.trans (by rw [hx.1, hx.2])⟩

private theorem state_map_refines {W S α β : Type} (proj : W → S) (f : α → β)
    {x : StateM W α} {y : StateM S α} (w : W)
    (hx : (x w).1 = (y (proj w)).1 ∧ proj (x w).2 = (y (proj w)).2) :
    ((f <$> x) w).1 = ((f <$> y) (proj w)).1 ∧
    proj ((f <$> x) w).2 = ((f <$> y) (proj w)).2 :=
  ⟨congrArg f hx.1, hx.2⟩

private theorem state_tryFinally_refines {W S α β : Type} (proj : W → S)
    {x : StateM W α} {y : StateM S α}
    {f1 : Option α → StateM W β} {f2 : Option α → StateM S β}
    (w : W)
    (hx : (x w).1 = (y (proj w)).1 ∧ proj (x w).2 = (y (proj w)).2)
    (hf : ∀ (a : α) (w1 : W),
      (f1 (some a) w1).1 = (f2 (some a) (proj w1)).1 ∧
      proj (f1 (some a) w1).2 = (f2 (some a) (proj w1)).2) :
    (tryFinally' x f1 w).1 = (tryFinally' y f2 (proj w)).1 ∧
    proj (tryFinally' x f1 w).2 = (tryFinally' y f2 (proj w)).2 := by
  have hx1 := hx.1
  have hx2 := hx.2
  have hfin := hf (x w).1 (x w).2
  change ((x w).1, (f1 (some (x w).1) (x w).2).1) =
      ((y (proj w)).1, (f2 (some (y (proj w)).1) (y (proj w)).2).1) ∧
    proj (f1 (some (x w).1) (x w).2).2 = (f2 (some (y (proj w)).1) (y (proj w)).2).2
  exact ⟨Prod.ext hx1 (hfin.1.trans (by rw [hx1, hx2])), hfin.2.trans (by rw [hx1, hx2])⟩

private theorem execLoop_refines {W : Type} (proj : W → Model.SqliteWorldState)
    (raw : RawSqliteOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (stmt : StmtHandle) :
    ∀ (fuel : Nat) (w : W),
      (Internal.execLoop raw stmt fuel w).1 =
        (Internal.execLoop Model.modelRawOps stmt fuel (proj w)).1 ∧
      proj (Internal.execLoop raw stmt fuel w).2 =
        (Internal.execLoop Model.modelRawOps stmt fuel (proj w)).2
  | 0, w =>
    ⟨congrArg Except.error (rawMapEq proj raw hRaw w _), rfl⟩
  | fuel + 1, w => by
    unfold Internal.execLoop
    refine state_bind_refines proj w (rawStepEq proj raw hRaw w stmt) fun res w1 => ?_
    cases res with
    | error _ => exact ⟨rfl, rfl⟩
    | ok sr =>
      cases sr with
      | done => exact ⟨rfl, rfl⟩
      | row _ => exact execLoop_refines proj raw hRaw stmt fuel w1

private theorem queryLoop_refines {W : Type} (proj : W → Model.SqliteWorldState)
    (raw : RawSqliteOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (stmt : StmtHandle) :
    ∀ (fuel : Nat) (acc : Array SqliteRow) (w : W),
      (Internal.queryLoop raw stmt acc fuel w).1 =
        (Internal.queryLoop Model.modelRawOps stmt acc fuel (proj w)).1 ∧
      proj (Internal.queryLoop raw stmt acc fuel w).2 =
        (Internal.queryLoop Model.modelRawOps stmt acc fuel (proj w)).2
  | 0, _, w =>
    ⟨congrArg Except.error (rawMapEq proj raw hRaw w _), rfl⟩
  | fuel + 1, acc, w => by
    unfold Internal.queryLoop
    refine state_bind_refines proj w (rawStepEq proj raw hRaw w stmt) fun res w1 => ?_
    cases res with
    | error _ => exact ⟨rfl, rfl⟩
    | ok sr =>
      cases sr with
      | done => exact ⟨rfl, rfl⟩
      | row cols => exact queryLoop_refines proj raw hRaw stmt fuel (acc.push cols) w1

private theorem execMaybeBindOp_refines {W : Type} (proj : W → Model.SqliteWorldState)
    (raw : RawSqliteOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (db : DbHandle) (sql : String) (params? : Option (Array SqliteValue)) (w : W) :
    (Internal.execMaybeBindOp raw db sql params? w).1 =
      (Internal.execMaybeBindOp Model.modelRawOps db sql params? (proj w)).1 ∧
    proj (Internal.execMaybeBindOp raw db sql params? w).2 =
      (Internal.execMaybeBindOp Model.modelRawOps db sql params? (proj w)).2 := by
  unfold Internal.execMaybeBindOp
  refine state_bind_refines proj w (rawPrepareEq proj raw hRaw w db sql) fun rp w1 => ?_
  cases rp with
  | error _ => exact ⟨rfl, rfl⟩
  | ok stmt =>
    refine state_bind_refines proj w1 (state_tryFinally_refines proj w1 ?_ fun _ w2 =>
      rawFinalizeEq proj raw hRaw w2 stmt) fun pair _ => by
      cases pair with | mk r1 r2 => cases r1 <;> cases r2 <;> exact ⟨rfl, rfl⟩
    cases params? with
    | none => exact execLoop_refines proj raw hRaw stmt Internal.maxStepFuel w1
    | some params =>
      refine state_bind_refines proj w1 (rawBindEq proj raw hRaw w1 stmt params) fun rb w2 => ?_
      cases rb with
      | error _ => exact ⟨rfl, rfl⟩
      | ok _ => exact execLoop_refines proj raw hRaw stmt Internal.maxStepFuel w2

private theorem queryOp_refines {W : Type} (proj : W → Model.SqliteWorldState)
    (raw : RawSqliteOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (db : DbHandle) (sql : String) (params : Array SqliteValue) (w : W) :
    (Internal.queryOp raw db sql params w).1 =
      (Internal.queryOp Model.modelRawOps db sql params (proj w)).1 ∧
    proj (Internal.queryOp raw db sql params w).2 =
      (Internal.queryOp Model.modelRawOps db sql params (proj w)).2 := by
  unfold Internal.queryOp
  refine state_bind_refines proj w (rawPrepareEq proj raw hRaw w db sql) fun rp w1 => ?_
  cases rp with
  | error _ => exact ⟨rfl, rfl⟩
  | ok stmt =>
    refine state_bind_refines proj w1 (state_tryFinally_refines proj w1 ?_ fun _ w2 =>
      rawFinalizeEq proj raw hRaw w2 stmt) fun pair _ => by
      cases pair with | mk r1 r2 => cases r1 <;> cases r2 <;> exact ⟨rfl, rfl⟩
    refine state_bind_refines proj w1 (rawBindEq proj raw hRaw w1 stmt params) fun rb w2 => ?_
    cases rb with
    | error _ => exact ⟨rfl, rfl⟩
    | ok _ => exact queryLoop_refines proj raw hRaw stmt Internal.maxStepFuel #[] w2

private theorem queryOneOp_refines {W : Type} (proj : W → Model.SqliteWorldState)
    (raw : RawSqliteOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (db : DbHandle) (sql : String) (params : Array SqliteValue) (w : W) :
    (Internal.queryOneOp raw db sql params w).1 =
      (Internal.queryOneOp Model.modelRawOps db sql params (proj w)).1 ∧
    proj (Internal.queryOneOp raw db sql params w).2 =
      (Internal.queryOneOp Model.modelRawOps db sql params (proj w)).2 := by
  unfold Internal.queryOneOp
  refine state_bind_refines proj w (rawPrepareEq proj raw hRaw w db sql) fun rp w1 => ?_
  cases rp with
  | error _ => exact ⟨rfl, rfl⟩
  | ok stmt =>
    refine state_bind_refines proj w1 (state_tryFinally_refines proj w1 ?_ fun _ w2 =>
      rawFinalizeEq proj raw hRaw w2 stmt) fun pair _ => by
      cases pair with | mk r1 r2 => cases r1 <;> cases r2 <;> exact ⟨rfl, rfl⟩
    refine state_bind_refines proj w1 (rawBindEq proj raw hRaw w1 stmt params) fun rb w2 => ?_
    cases rb with
    | error _ => exact ⟨rfl, rfl⟩
    | ok _ =>
      refine state_bind_refines proj w2 (rawStepEq proj raw hRaw w2 stmt) fun rs _ => ?_
      cases rs with
      | error _ => exact ⟨rfl, rfl⟩
      | ok sr => cases sr <;> exact ⟨rfl, rfl⟩

private theorem runStepAction_refines {W : Type} (proj : W → Model.SqliteWorldState)
    (raw : RawSqliteOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (db : DbHandle) :
    ∀ (act : Model.StepAction) (w : W),
      (Model.runStepAction (Internal.mkApiM raw) db act w).1 =
        (Model.runStepAction (Internal.mkApiM Model.modelRawOps) db act (proj w)).1 ∧
      proj (Model.runStepAction (Internal.mkApiM raw) db act w).2 =
        (Model.runStepAction (Internal.mkApiM Model.modelRawOps) db act (proj w)).2
  | .ret _, _ => ⟨rfl, rfl⟩
  | .exec sql params, w => execMaybeBindOp_refines proj raw hRaw db sql (some params) w
  | .seq a b, w => by
    unfold Model.runStepAction
    refine state_bind_refines proj w (runStepAction_refines proj raw hRaw db a w) fun ra w1 => ?_
    cases ra with
    | error _ => exact ⟨rfl, rfl⟩
    | ok _ => exact runStepAction_refines proj raw hRaw db b w1

private theorem obeysStepFromFinally_mkApiM :
    Core.ObeysStepFromFinally id Model.rawStepWf Model.execRawStep Model.allowedRawStep
      Model.rawStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj raw hRaw w req _
  change ((Model.execPkgStep (Internal.mkApiM raw) req) w).1 =
      ((Model.execPkgStep Model.modelApi req) (proj w)).1 ∧
    proj ((Model.execPkgStep (Internal.mkApiM raw) req) w).2 =
      ((Model.execPkgStep Model.modelApi req) (proj w)).2
  rw [← sqlite_mkApiM_modelRawOps_eq_modelApi]
  cases req with
  | withDb path cfg act =>
    unfold Model.execPkgStep
    refine state_map_refines proj Model.PkgStepOut.unit w ?_
    change (Internal.withDbOp raw path cfg (fun db => Model.runStepAction (Internal.mkApiM raw) db act) w).1 =
      (Internal.withDbOp Model.modelRawOps path cfg
        (fun db => Model.runStepAction (Internal.mkApiM Model.modelRawOps) db act) (proj w)).1 ∧
      proj (Internal.withDbOp raw path cfg (fun db => Model.runStepAction (Internal.mkApiM raw) db act) w).2 =
      (Internal.withDbOp Model.modelRawOps path cfg
        (fun db => Model.runStepAction (Internal.mkApiM Model.modelRawOps) db act) (proj w)).2
    unfold Internal.withDbOp
    have hVal : Internal.validateConfigWith raw.mapRawError cfg =
        Internal.validateConfigWith Model.modelRawOps.mapRawError cfg := by
      unfold Internal.validateConfigWith
      split
      · simp [rawMapEq proj raw hRaw w]
      · split
        · simp [rawMapEq proj raw hRaw w]
        · rfl
    rw [hVal]
    cases Internal.validateConfigWith Model.modelRawOps.mapRawError cfg with
    | error _ => exact ⟨rfl, rfl⟩
    | ok _ =>
      refine state_bind_refines proj w (rawOpenEq proj raw hRaw w path cfg) fun ro w1 => ?_
      cases ro with
      | error _ => exact ⟨rfl, rfl⟩
      | ok db =>
        refine state_bind_refines proj w1
          (state_tryFinally_refines proj w1 (runStepAction_refines proj raw hRaw db act w1)
            fun _ w2 => rawCloseEq proj raw hRaw w2 db) fun pair _ => by
          cases pair with | mk r1 r2 => cases r1 <;> cases r2 <;> exact ⟨rfl, rfl⟩
  | withTransaction db act =>
    unfold Model.execPkgStep
    refine state_map_refines proj Model.PkgStepOut.unit w ?_
    change (Internal.withTransactionOp raw db (fun txDb => Model.runStepAction (Internal.mkApiM raw) txDb act) w).1 =
      (Internal.withTransactionOp Model.modelRawOps db
        (fun txDb => Model.runStepAction (Internal.mkApiM Model.modelRawOps) txDb act) (proj w)).1 ∧
      proj (Internal.withTransactionOp raw db (fun txDb => Model.runStepAction (Internal.mkApiM raw) txDb act) w).2 =
      (Internal.withTransactionOp Model.modelRawOps db
        (fun txDb => Model.runStepAction (Internal.mkApiM Model.modelRawOps) txDb act) (proj w)).2
    unfold Internal.withTransactionOp
    refine state_bind_refines proj w
      (execMaybeBindOp_refines proj raw hRaw db "BEGIN IMMEDIATE" none w) fun rb w1 => ?_
    cases rb with
    | error _ => exact ⟨rfl, rfl⟩
    | ok _ =>
      refine state_bind_refines proj w1
        (state_tryFinally_refines proj w1 (runStepAction_refines proj raw hRaw db act w1)
          fun a w2 => by
            cases a with
            | error _ => exact execMaybeBindOp_refines proj raw hRaw db "ROLLBACK" none w2
            | ok _ => exact execMaybeBindOp_refines proj raw hRaw db "COMMIT" none w2)
        fun pair w2 => by
          cases pair with
          | mk r1 r2 =>
            cases r1 with
            | error _ => exact ⟨rfl, rfl⟩
            | ok _ =>
              cases r2 with
              | ok _ => exact ⟨rfl, rfl⟩
              | error _ =>
                refine state_bind_refines proj w2
                  (execMaybeBindOp_refines proj raw hRaw db "ROLLBACK" none w2) fun _ _ =>
                  ⟨rfl, rfl⟩
  | exec db sql params =>
    unfold Model.execPkgStep
    exact state_map_refines proj Model.PkgStepOut.unit w
      (execMaybeBindOp_refines proj raw hRaw db sql (some params) w)
  | query db sql params =>
    unfold Model.execPkgStep
    exact state_map_refines proj Model.PkgStepOut.rows w
      (queryOp_refines proj raw hRaw db sql params w)
  | queryOne db sql params =>
    unfold Model.execPkgStep
    exact state_map_refines proj Model.PkgStepOut.rowOpt w
      (queryOneOp_refines proj raw hRaw db sql params w)
  | activeDbCount =>
    have h := hRaw w .activeDbCount rfl
    simp only [Model.execRawStep, Raw.Model.execRawStep, Model.allowedRawStep, StateT.run,
      Functor.map, StateT.map] at h
    exact ⟨congrArg Model.PkgStepOut.count (Raw.Model.RawStepOut.activeDbCount.inj h.1), h.2⟩
  | activeStmtCount =>
    have h := hRaw w .activeStmtCount rfl
    simp only [Model.execRawStep, Raw.Model.execRawStep, Model.allowedRawStep, StateT.run,
      Functor.map, StateT.map] at h
    exact ⟨congrArg Model.PkgStepOut.count (Raw.Model.RawStepOut.activeStmtCount.inj h.1), h.2⟩

/-- Full public `Interface` obedience of `LeanSwe.Sqlite` against `LeanSwe.Sqlite.Model`. -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.Sqlite.mapRawError Model.mapRawError ∧
    Core.ObeysPureEq LeanSwe.Sqlite.validateConfig Model.validateConfig ∧
    Core.ObeysStepFromFinally id Model.rawStepWf Model.execRawStep Model.allowedRawStep
      Model.rawStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep :=
  ⟨mapRawError_eq_model, validateConfig_eq_model, obeysStepFromFinally_mkApiM⟩

end LeanSwe.Sqlite.Proofs
