import LeanSwe.Sqlite.Interface
import LeanSwe.Sqlite.SpecTests
import LeanSwe.Sqlite.Raw.Proofs

namespace LeanSwe.Sqlite.Proofs

open Core
open Core.NondetTest
open LeanSwe.Sqlite

private theorem nonEmptyMsg_ne_empty (fallback msg : String) (hf : fallback ≠ "") :
    Raw.Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Raw.Internal.nonEmptyMsg
  split
  · exact hf
  · next h =>
    intro hem
    subst hem
    simp [String.isEmpty] at h

/-- Proof of `test_sqlite_mapRawError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem proof_sqlite_mapRawError_returnsNonEmptyMessage :
    AllPass (test_sqlite_mapRawError_returnsNonEmptyMessage defaultApi) := by
  intro raw
  simpa [defaultApi, Internal.mkApiM] using
    Raw.Proofs.proof_sqliteraw_mapRawError_returnsNonEmptyMessage raw

/-- Non-vacuity `CanReach` witness for `test_sqlite_mapRawError_returnsNonEmptyMessage`. -/
theorem reach_sqlite_mapRawError_returnsNonEmptyMessage :
    CanReach (test_sqlite_mapRawError_returnsNonEmptyMessage defaultApi) :=
  ⟨.userError "", proof_sqlite_mapRawError_returnsNonEmptyMessage (.userError "")⟩

/-- Proof of `test_sqlite_mapRawError_mapsExpectedKinds` for `defaultApi`. -/
theorem proof_sqlite_mapRawError_mapsExpectedKinds :
    AllPass (test_sqlite_mapRawError_mapsExpectedKinds defaultApi) := by
  intro path? code detail
  dsimp only [test_sqlite_mapRawError_mapsExpectedKinds, Bind.bind, Pure.pure,
    defaultApi, Internal.mkApiM, Raw.defaultOps, Raw.Internal.mkRawOps,
    Raw.Internal.mapRawError, assert]
  refine ⟨⟨rfl, nonEmptyMsg_ne_empty _ _ (by decide)⟩,
    ⟨rfl, nonEmptyMsg_ne_empty _ _ (by decide)⟩,
    ⟨rfl, nonEmptyMsg_ne_empty _ _ (by decide)⟩,
    ⟨rfl, nonEmptyMsg_ne_empty _ _ (by decide)⟩,
    ⟨rfl, nonEmptyMsg_ne_empty _ _ (by decide)⟩,
    ⟨rfl, ?_⟩, trivial⟩
  apply nonEmptyMsg_ne_empty
  intro h
  have h1 := (String.append_eq_empty_iff.mp h).1
  exact absurd (String.append_eq_empty_iff.mp h1).1 (by decide)

/-- Non-vacuity `CanReach` witness for `test_sqlite_mapRawError_mapsExpectedKinds`. -/
theorem reach_sqlite_mapRawError_mapsExpectedKinds :
    CanReach (test_sqlite_mapRawError_mapsExpectedKinds defaultApi) := by
  refine ⟨none, 5, "locked", ?_⟩
  dsimp only [test_sqlite_mapRawError_mapsExpectedKinds, Bind.bind, Pure.pure,
    defaultApi, Internal.mkApiM, Raw.defaultOps, Raw.Internal.mkRawOps,
    Raw.Internal.mapRawError, Raw.Internal.nonEmptyMsg, assert]
  exact ⟨⟨rfl, by decide⟩, ⟨rfl, by decide⟩, ⟨rfl, by decide⟩,
    ⟨rfl, by decide⟩, ⟨rfl, by decide⟩, ⟨rfl, by decide⟩, trivial⟩

/-- Proof of `test_sqlite_validateConfig_rejectsReadOnlyWithCreate` for `defaultApi`. -/
theorem proof_sqlite_validateConfig_rejectsReadOnlyWithCreate :
    AllPass (test_sqlite_validateConfig_rejectsReadOnlyWithCreate defaultApi) := by
  intro cfg hAssume
  rcases hAssume with ⟨hRO, hCr⟩
  dsimp only [test_sqlite_validateConfig_rejectsReadOnlyWithCreate, Bind.bind,
    defaultApi, Internal.mkApiM, Internal.validateConfigWith, Raw.defaultOps,
    Raw.Internal.mkRawOps, Raw.Internal.mapRawError, assert]
  rw [hRO, hCr]
  have hMsg : Raw.Internal.nonEmptyMsg "invalid sqlite argument"
      "cannot combine readOnly = true with createIfMissing = true" ≠ "" :=
    nonEmptyMsg_ne_empty _ _ (by decide)
  exact ⟨⟨rfl, hMsg⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_sqlite_validateConfig_rejectsReadOnlyWithCreate`. -/
theorem reach_sqlite_validateConfig_rejectsReadOnlyWithCreate :
    CanReach (test_sqlite_validateConfig_rejectsReadOnlyWithCreate defaultApi) := by
  refine ⟨{ readOnly := true, createIfMissing := true }, ⟨rfl, rfl⟩, ?_⟩
  dsimp only [test_sqlite_validateConfig_rejectsReadOnlyWithCreate, Bind.bind,
    defaultApi, Internal.mkApiM, Internal.validateConfigWith, Raw.defaultOps,
    Raw.Internal.mkRawOps, Raw.Internal.mapRawError, Raw.Internal.nonEmptyMsg, assert]
  exact ⟨⟨rfl, by decide⟩, trivial⟩

/-- Proof of `test_sqlite_validateConfig_rejectsExcessiveBusyTimeout` for `defaultApi`. -/
theorem proof_sqlite_validateConfig_rejectsExcessiveBusyTimeout :
    AllPass (test_sqlite_validateConfig_rejectsExcessiveBusyTimeout defaultApi) := by
  intro cfg hGt
  dsimp only [test_sqlite_validateConfig_rejectsExcessiveBusyTimeout, Bind.bind,
    defaultApi, Internal.mkApiM, Internal.validateConfigWith, Raw.defaultOps,
    Raw.Internal.mkRawOps, Raw.Internal.mapRawError, assert]
  cases hRO : (cfg.readOnly && cfg.createIfMissing)
  · simp only [Bool.false_eq_true, ↓reduceIte, ite_eq_left hGt]
    refine ⟨⟨trivial, ?_⟩, trivial⟩
    apply nonEmptyMsg_ne_empty
    decide
  · simp only [↓reduceIte]
    refine ⟨⟨trivial, ?_⟩, trivial⟩
    apply nonEmptyMsg_ne_empty
    decide

/-- Non-vacuity `CanReach` witness for `test_sqlite_validateConfig_rejectsExcessiveBusyTimeout`. -/
theorem reach_sqlite_validateConfig_rejectsExcessiveBusyTimeout :
    CanReach (test_sqlite_validateConfig_rejectsExcessiveBusyTimeout defaultApi) := by
  refine ⟨{ busyTimeoutMs := maxBusyTimeoutMs + 1 }, by decide, ?_⟩
  dsimp only [test_sqlite_validateConfig_rejectsExcessiveBusyTimeout, Bind.bind,
    defaultApi, Internal.mkApiM, Internal.validateConfigWith, Raw.defaultOps,
    Raw.Internal.mkRawOps, Raw.Internal.mapRawError, Raw.Internal.nonEmptyMsg, assert]
  exact ⟨⟨rfl, by decide⟩, trivial⟩

/-- Proof of `test_sqlite_validateConfig_acceptsValidConfig` for `defaultApi`. -/
theorem proof_sqlite_validateConfig_acceptsValidConfig :
    AllPass (test_sqlite_validateConfig_acceptsValidConfig defaultApi) := by
  intro cfg hNoBoth hLe
  dsimp only [test_sqlite_validateConfig_acceptsValidConfig, Bind.bind,
    defaultApi, Internal.mkApiM, Internal.validateConfigWith, assert]
  have h1 : (cfg.readOnly && cfg.createIfMissing) = false := by
    cases h : (cfg.readOnly && cfg.createIfMissing) <;> simp_all
  have h2 : ¬ (cfg.busyTimeoutMs > maxBusyTimeoutMs) := Nat.not_lt.mpr hLe
  simp [h1, h2]

/-- Non-vacuity `CanReach` witness for `test_sqlite_validateConfig_acceptsValidConfig`. -/
theorem reach_sqlite_validateConfig_acceptsValidConfig :
    CanReach (test_sqlite_validateConfig_acceptsValidConfig defaultApi) := by
  refine ⟨{}, by decide, by decide, ?_⟩
  dsimp only [test_sqlite_validateConfig_acceptsValidConfig, Bind.bind,
    defaultApi, Internal.mkApiM, Internal.validateConfigWith, assert]
  exact ⟨rfl, trivial⟩

private theorem list_nil_of_toList_nil (s : String) (h : s.toList = []) : s = "" :=
  String.ext (by simpa using h)

private theorem mkApiM_validate_validCfg (cfg : OpenConfig) :
    Internal.validateConfigWith mockRawOps.mapRawError
      { readOnly := false, createIfMissing := cfg.createIfMissing,
        busyTimeoutMs := cfg.busyTimeoutMs % (maxBusyTimeoutMs + 1),
        walMode := cfg.walMode, foreignKeys := cfg.foreignKeys } = .ok () := by
  unfold Internal.validateConfigWith
  have hLt : cfg.busyTimeoutMs % (maxBusyTimeoutMs + 1) < maxBusyTimeoutMs + 1 :=
    Nat.mod_lt _ (Nat.succ_pos _)
  have hNotGt : ¬ (cfg.busyTimeoutMs % (maxBusyTimeoutMs + 1) > maxBusyTimeoutMs) := by omega
  simp [hNotGt]

private theorem execLoop_done {S : Type} (ops : RawSqliteOpsM (StateM S))
    (stmt : StmtHandle) (n : Nat) (s0 s1 : S)
    (hs : ops.step stmt s0 = (.ok .done, s1)) :
    Internal.execLoop ops stmt (n + 1) s0 = (.ok (), s1) := by
  simp [Internal.execLoop, bind, pure, StateT.bind, StateT.pure, hs]

private theorem execLoop_err {S : Type} (ops : RawSqliteOpsM (StateM S))
    (stmt : StmtHandle) (n : Nat) (s0 s1 : S) (e : SqliteError)
    (hs : ops.step stmt s0 = (.error e, s1)) :
    Internal.execLoop ops stmt (n + 1) s0 = (.error e, s1) := by
  simp [Internal.execLoop, bind, pure, StateT.bind, StateT.pure, hs]

private theorem state_tryFinally_eq {S α β : Type} (x : StateM S α) (f : Option α → StateM S β) (s : S) :
    tryFinally' x f s =
      let (a, s') := x s
      let (b, s'') := f (some a) s'
      ((a, b), s'') := rfl

private theorem state_tryFinally_step {S α β : Type} {x : StateM S α} {f : Option α → StateM S β}
    {s0 s1 s2 : S} {a : α} {b : β} (hx : x s0 = (a, s1)) (hf : f (some a) s1 = (b, s2)) :
    tryFinally' x f s0 = ((a, b), s2) := by
  change (let (a', s') := x s0; let (b', s'') := f (some a') s'; ((a', b'), s'')) = ((a, b), s2)
  rw [hx]
  dsimp only
  rw [hf]

private theorem execOp_ok {S : Type} (ops : RawSqliteOpsM (StateM S))
    (db : DbHandle) (sql : String) (params : Array SqliteValue) (s0 s1 s2 s3 s4 : S)
    (stmt : StmtHandle)
    (hp : ops.prepare db sql s0 = (.ok stmt, s1))
    (hb : ops.bind stmt params s1 = (.ok (), s2))
    (hs : ops.step stmt s2 = (.ok .done, s3))
    (hf : ops.finalize stmt s3 = (.ok (), s4)) :
    Internal.execOp ops db sql params s0 = (.ok (), s4) := by
  simp only [Internal.execOp, Internal.execMaybeBindOp, bind, pure, StateT.bind,
    state_tryFinally_eq, hp, hb]
  have hl : Internal.execLoop ops stmt Internal.maxStepFuel s2 = (.ok (), s3) := by
    change Internal.execLoop ops stmt (99999999 + 1) s2 = (.ok (), s3)
    exact execLoop_done ops stmt 99999999 s2 s3 hs
  simp [hl, hf, pure, StateT.pure]

private theorem execOp_step_err {S : Type} (ops : RawSqliteOpsM (StateM S))
    (db : DbHandle) (sql : String) (params : Array SqliteValue) (s0 s1 s2 s3 s4 : S)
    (stmt : StmtHandle) (e : SqliteError) (finRes : Except SqliteError Unit)
    (hp : ops.prepare db sql s0 = (.ok stmt, s1))
    (hb : ops.bind stmt params s1 = (.ok (), s2))
    (hs : ops.step stmt s2 = (.error e, s3))
    (hf : ops.finalize stmt s3 = (finRes, s4)) :
    Internal.execOp ops db sql params s0 = (.error e, s4) := by
  simp only [Internal.execOp, Internal.execMaybeBindOp, bind, pure, StateT.bind,
    state_tryFinally_eq, hp, hb]
  have hl : Internal.execLoop ops stmt Internal.maxStepFuel s2 = (.error e, s3) := by
    change Internal.execLoop ops stmt (99999999 + 1) s2 = (.error e, s3)
    exact execLoop_err ops stmt 99999999 s2 s3 e hs
  simp [hl, hf, pure, StateT.pure]

private theorem execControlOp_ok {S : Type} (ops : RawSqliteOpsM (StateM S))
    (db : DbHandle) (sql : String) (s0 s1 s2 s3 : S) (stmt : StmtHandle)
    (hp : ops.prepare db sql s0 = (.ok stmt, s1))
    (hs : ops.step stmt s1 = (.ok .done, s2))
    (hf : ops.finalize stmt s2 = (.ok (), s3)) :
    Internal.execMaybeBindOp ops db sql none s0 = (.ok (), s3) := by
  simp only [Internal.execMaybeBindOp, bind, pure, StateT.bind,
    state_tryFinally_eq, hp]
  have hl : Internal.execLoop ops stmt Internal.maxStepFuel s1 = (.ok (), s2) := by
    change Internal.execLoop ops stmt (99999999 + 1) s1 = (.ok (), s2)
    exact execLoop_done ops stmt 99999999 s1 s2 hs
  simp [hl, hf, pure, StateT.pure]

private theorem execControlOp_step_err {S : Type} (ops : RawSqliteOpsM (StateM S))
    (db : DbHandle) (sql : String) (s0 s1 s2 s3 : S)
    (stmt : StmtHandle) (e : SqliteError) (finRes : Except SqliteError Unit)
    (hp : ops.prepare db sql s0 = (.ok stmt, s1))
    (hs : ops.step stmt s1 = (.error e, s2))
    (hf : ops.finalize stmt s2 = (finRes, s3)) :
    Internal.execMaybeBindOp ops db sql none s0 = (.error e, s3) := by
  simp only [Internal.execMaybeBindOp, bind, pure, StateT.bind,
    state_tryFinally_eq, hp]
  have hl : Internal.execLoop ops stmt Internal.maxStepFuel s1 = (.error e, s2) := by
    change Internal.execLoop ops stmt (99999999 + 1) s1 = (.error e, s2)
    exact execLoop_err ops stmt 99999999 s1 s2 e hs
  simp [hl, hf, pure, StateT.pure]

private theorem state_bind_step {S α β : Type} {f : StateM S α} {k : α → StateM S β}
    {s0 s1 : S} {a : α} (hf : f s0 = (a, s1)) :
    StateT.bind f k s0 = k a s1 := by
  simp [StateT.bind, Bind.bind, hf]

private theorem queryLoop_row {S : Type} (ops : RawSqliteOpsM (StateM S))
    (stmt : StmtHandle) (acc : Array SqliteRow) (n : Nat) (s0 s1 : S) (r : SqliteRow)
    (hs : ops.step stmt s0 = (.ok (.row r), s1)) :
    Internal.queryLoop ops stmt acc (n + 1) s0 =
      Internal.queryLoop ops stmt (acc.push r) n s1 := by
  simp [Internal.queryLoop, bind, StateT.bind, hs]

private theorem queryLoop_done {S : Type} (ops : RawSqliteOpsM (StateM S))
    (stmt : StmtHandle) (acc : Array SqliteRow) (n : Nat) (s0 s1 : S)
    (hs : ops.step stmt s0 = (.ok .done, s1)) :
    Internal.queryLoop ops stmt acc (n + 1) s0 = (.ok acc, s1) := by
  simp [Internal.queryLoop, bind, pure, StateT.bind, StateT.pure, hs]

private theorem queryLoop_err {S : Type} (ops : RawSqliteOpsM (StateM S))
    (stmt : StmtHandle) (acc : Array SqliteRow) (n : Nat) (s0 s1 : S) (e : SqliteError)
    (hs : ops.step stmt s0 = (.error e, s1)) :
    Internal.queryLoop ops stmt acc (n + 1) s0 = (.error e, s1) := by
  simp [Internal.queryLoop, bind, pure, StateT.bind, StateT.pure, hs]

private theorem queryOp_two_rows_ok {S : Type} (ops : RawSqliteOpsM (StateM S))
    (db : DbHandle) (sql : String) (params : Array SqliteValue)
    (s0 s1 s2 s3 s4 s5 s6 : S) (stmt : StmtHandle) (r0 r1 : SqliteRow)
    (hp : ops.prepare db sql s0 = (.ok stmt, s1))
    (hb : ops.bind stmt params s1 = (.ok (), s2))
    (hs1 : ops.step stmt s2 = (.ok (.row r0), s3))
    (hs2 : ops.step stmt s3 = (.ok (.row r1), s4))
    (hs3 : ops.step stmt s4 = (.ok .done, s5))
    (hf : ops.finalize stmt s5 = (.ok (), s6)) :
    Internal.queryOp ops db sql params s0 = (.ok #[r0, r1], s6) := by
  simp only [Internal.queryOp, bind, pure, StateT.bind, state_tryFinally_eq, hp, hb]
  have hl : Internal.queryLoop ops stmt #[] Internal.maxStepFuel s2 = (.ok #[r0, r1], s5) := by
    change Internal.queryLoop ops stmt #[] (99999999 + 1) s2 = _
    rw [queryLoop_row ops stmt #[] 99999999 s2 s3 r0 hs1]
    rw [queryLoop_row ops stmt (#[].push r0) 99999998 s3 s4 r1 hs2]
    rw [queryLoop_done ops stmt ((#[].push r0).push r1) 99999997 s4 s5 hs3]
    rfl
  simp [hl, hf, pure, StateT.pure]

private theorem queryOp_empty_ok {S : Type} (ops : RawSqliteOpsM (StateM S))
    (db : DbHandle) (sql : String) (params : Array SqliteValue)
    (s0 s1 s2 s3 s4 : S) (stmt : StmtHandle)
    (hp : ops.prepare db sql s0 = (.ok stmt, s1))
    (hb : ops.bind stmt params s1 = (.ok (), s2))
    (hs : ops.step stmt s2 = (.ok .done, s3))
    (hf : ops.finalize stmt s3 = (.ok (), s4)) :
    Internal.queryOp ops db sql params s0 = (.ok #[], s4) := by
  simp only [Internal.queryOp, bind, pure, StateT.bind, state_tryFinally_eq, hp, hb]
  have hl : Internal.queryLoop ops stmt #[] Internal.maxStepFuel s2 = (.ok #[], s3) := by
    change Internal.queryLoop ops stmt #[] (99999999 + 1) s2 = _
    exact queryLoop_done ops stmt #[] 99999999 s2 s3 hs
  simp [hl, hf, pure, StateT.pure]

private theorem queryOp_two_rows_mid_err {S : Type} (ops : RawSqliteOpsM (StateM S))
    (db : DbHandle) (sql : String) (params : Array SqliteValue)
    (s0 s1 s2 s3 s4 s5 : S) (stmt : StmtHandle) (r0 : SqliteRow) (e : SqliteError)
    (finRes : Except SqliteError Unit)
    (hp : ops.prepare db sql s0 = (.ok stmt, s1))
    (hb : ops.bind stmt params s1 = (.ok (), s2))
    (hs1 : ops.step stmt s2 = (.ok (.row r0), s3))
    (hs2 : ops.step stmt s3 = (.error e, s4))
    (hf : ops.finalize stmt s4 = (finRes, s5)) :
    Internal.queryOp ops db sql params s0 = (.error e, s5) := by
  simp only [Internal.queryOp, bind, pure, StateT.bind, state_tryFinally_eq, hp, hb]
  have hl : Internal.queryLoop ops stmt #[] Internal.maxStepFuel s2 = (.error e, s4) := by
    change Internal.queryLoop ops stmt #[] (99999999 + 1) s2 = _
    rw [queryLoop_row ops stmt #[] 99999999 s2 s3 r0 hs1]
    exact queryLoop_err ops stmt (#[].push r0) 99999998 s3 s4 e hs2
  simp [hl, hf, pure, StateT.pure]

private theorem queryOneOp_done {S : Type} (ops : RawSqliteOpsM (StateM S))
    (db : DbHandle) (sql : String) (params : Array SqliteValue)
    (s0 s1 s2 s3 s4 : S) (stmt : StmtHandle)
    (hp : ops.prepare db sql s0 = (.ok stmt, s1))
    (hb : ops.bind stmt params s1 = (.ok (), s2))
    (hs : ops.step stmt s2 = (.ok .done, s3))
    (hf : ops.finalize stmt s3 = (.ok (), s4)) :
    Internal.queryOneOp ops db sql params s0 = (.ok none, s4) := by
  simp [Internal.queryOneOp, bind, pure, StateT.bind, StateT.pure, state_tryFinally_eq, hp, hb, hs, hf]

private theorem queryOneOp_row {S : Type} (ops : RawSqliteOpsM (StateM S))
    (db : DbHandle) (sql : String) (params : Array SqliteValue)
    (s0 s1 s2 s3 s4 : S) (stmt : StmtHandle) (r : SqliteRow)
    (hp : ops.prepare db sql s0 = (.ok stmt, s1))
    (hb : ops.bind stmt params s1 = (.ok (), s2))
    (hs : ops.step stmt s2 = (.ok (.row r), s3))
    (hf : ops.finalize stmt s3 = (.ok (), s4)) :
    Internal.queryOneOp ops db sql params s0 = (.ok (some r), s4) := by
  simp [Internal.queryOneOp, bind, pure, StateT.bind, StateT.pure, state_tryFinally_eq, hp, hb, hs, hf]

private theorem queryOneOp_step_err {S : Type} (ops : RawSqliteOpsM (StateM S))
    (db : DbHandle) (sql : String) (params : Array SqliteValue)
    (s0 s1 s2 s3 s4 : S) (stmt : StmtHandle) (e : SqliteError) (finRes : Except SqliteError Unit)
    (hp : ops.prepare db sql s0 = (.ok stmt, s1))
    (hb : ops.bind stmt params s1 = (.ok (), s2))
    (hs : ops.step stmt s2 = (.error e, s3))
    (hf : ops.finalize stmt s3 = (finRes, s4)) :
    Internal.queryOneOp ops db sql params s0 = (.error e, s4) := by
  simp [Internal.queryOneOp, bind, pure, StateT.bind, StateT.pure, state_tryFinally_eq, hp, hb, hs, hf]

/-- Proof of `test_sqlite_withDb_preservesActiveDbCount_andPropagatesBusy` for `Internal.mkApiM`. -/
theorem proof_sqlite_withDb_preservesActiveDbCount_andPropagatesBusy :
    AllPass (test_sqlite_withDb_preservesActiveDbCount_andPropagatesBusy Internal.mkApiM) := by
  intro path cfg failOnBody bodyErr hPathNe
  have hToList : (path.toList == []) = false := by
    cases h : (path.toList == [])
    · rfl
    · exact absurd (list_nil_of_toList_nil path (beq_iff_eq.mp h)) hPathNe
  let validCfg : OpenConfig :=
    { cfg with readOnly := false, busyTimeoutMs := cfg.busyTimeoutMs % (maxBusyTimeoutMs + 1) }
  have hVal : Internal.validateConfigWith mockRawOps.mapRawError validCfg = .ok () :=
    mkApiM_validate_validCfg cfg
  let sOpen : MockDb :=
    { nextDbId := 2, openDbs := [1], openCalls := [(path, validCfg)], failMode := .none }
  let sClose : MockDb :=
    { nextDbId := 2, openDbs := [], openCalls := [(path, validCfg)], failMode := .none }
  let sBusyInit : MockDb := { failMode := .failOpen .busy }
  let sBusyDone : MockDb := { openCalls := [(path, validCfg)], failMode := .failOpen .busy }
  have hOpen1 : mockRawOps.openDb path validCfg {} = (.ok { id := 1 }, sOpen) := by
    change (if path.toList == [] then _ else _) = _
    simp [hToList, sOpen]
  have hClose1 : mockRawOps.closeDb { id := 1 } sOpen = (.ok (), sClose) := rfl
  have hOpenBusy : mockRawOps.openDb path validCfg sBusyInit =
      (.error { kind := .busy, path := some path, message := "mock open failure" }, sBusyDone) := rfl
  dsimp only [test_sqlite_withDb_preservesActiveDbCount_andPropagatesBusy, Bind.bind,
    Internal.mkApiM, Internal.withDbOp, StateT.run]
  rw [hVal]
  simp only [bind, pure, StateT.bind]
  cases failOnBody <;>
    · rw [hOpen1]
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.bind, Bind.bind, Pure.pure, StateT.pure,
        state_tryFinally_eq]
      rw [hClose1, hOpenBusy]
      simp [mockRawOps, Internal.validateConfigWith, validCfg, sClose, sBusyDone, StateT.pure,
        Pure.pure, assert]
      try rfl

/-- Non-vacuity `CanReach` witness for `test_sqlite_withDb_preservesActiveDbCount_andPropagatesBusy`. -/
theorem reach_sqlite_withDb_preservesActiveDbCount_andPropagatesBusy :
    CanReach (test_sqlite_withDb_preservesActiveDbCount_andPropagatesBusy Internal.mkApiM) :=
  ⟨"app.db", {}, false, { kind := .ioError, message := "e" }, by decide,
    proof_sqlite_withDb_preservesActiveDbCount_andPropagatesBusy
      "app.db" {} false { kind := .ioError, message := "e" } (by decide)⟩

/-- Proof of `test_sqlite_exec_preservesActiveStmtCount_andPropagatesErrors` for `Internal.mkApiM`. -/
theorem proof_sqlite_exec_preservesActiveStmtCount_andPropagatesErrors :
    AllPass (test_sqlite_exec_preservesActiveStmtCount_andPropagatesErrors Internal.mkApiM) := by
  intro sql params mode hMode hSql
  simp only [Bool.not_eq_true'] at hSql
  simp only [Bool.or_eq_false_iff] at hSql
  rcases hSql with ⟨⟨hNBegF, hNComF⟩, hNRbF⟩
  simp only [Bool.eq_false_iff] at hNBegF hNComF hNRbF
  dsimp only [test_sqlite_exec_preservesActiveStmtCount_andPropagatesErrors, Bind.bind,
    Internal.mkApiM, StateT.run]
  let stmt : StmtHandle := { id := 1, dbId := 1 }
  rcases hMode with rfl | rfl | rfl | rfl | rfl
  · let s0 : MockDb := { openDbs := [1], nextDbId := 2, failMode := .none }
    let s1 : MockDb := { s0 with nextStmtId := 2, openStmts := [{ id := 1, dbId := 1, sql := sql }] }
    let s2 : MockDb :=
      { s1 with
          openStmts := [{ id := 1, dbId := 1, sql := sql, boundParams := some params }],
          boundCalls := [(sql, params)] }
    have hp : mockRawOps.prepare { id := 1 } sql s0 = (.ok stmt, s1) := rfl
    have hb : mockRawOps.bind stmt params s1 = (.ok (), s2) := rfl
    have hsOk : mockRawOps.step stmt s2 = (Except.ok Raw.StepResult.done, s2) ∨
        mockRawOps.step stmt s2 =
          (Except.ok Raw.StepResult.done, { s2 with committedWrites := [(sql, params)] }) := by
      dsimp only [mockRawOps]
      change (if _ then _ else _) = _ ∨ (if _ then _ else _) = _
      rw [ite_eq_right hNBegF, ite_eq_right hNComF, ite_eq_right hNRbF]
      dsimp only [s2, s1, s0]
      split
      · exact Or.inl (by simp [*])
      · exact Or.inr (by simp [*])
    rcases hsOk with hs | hs
    · have hEx := execOp_ok mockRawOps { id := 1 } sql params s0 s1 s2 s2
        { s2 with openStmts := [] } stmt hp hb hs rfl
      rw [hEx]
      simp [mockRawOps, assert]
    · have hEx := execOp_ok mockRawOps { id := 1 } sql params s0 s1 s2
        { s2 with committedWrites := [(sql, params)] }
        { s2 with committedWrites := [(sql, params)], openStmts := [] } stmt hp hb hs rfl
      rw [hEx]
      simp [mockRawOps, assert]
  · let s0 : MockDb := { openDbs := [1], nextDbId := 2, failMode := .failPrepare .invalidInput }
    have hp : mockRawOps.prepare { id := 1 } sql s0 =
        (.error { kind := .invalidInput, message := "mock prepare failure" }, s0) := rfl
    have hEx : Internal.execOp mockRawOps { id := 1 } sql params s0 =
        (.error { kind := .invalidInput, message := "mock prepare failure" }, s0) := by
      simp [Internal.execOp, Internal.execMaybeBindOp, bind, pure, StateT.bind, StateT.pure, hp]
    rw [hEx]
    simp [mockRawOps, s0, assert]
  · let s0 : MockDb := { openDbs := [1], nextDbId := 2, failMode := .failBind .invalidInput }
    let s1 : MockDb := { s0 with nextStmtId := 2, openStmts := [{ id := 1, dbId := 1, sql := sql }] }
    let s2 : MockDb := { s1 with openStmts := [] }
    have hp : mockRawOps.prepare { id := 1 } sql s0 = (.ok stmt, s1) := rfl
    have hb : mockRawOps.bind stmt params s1 =
        (.error { kind := .invalidInput, message := "mock bind failure" }, s1) := rfl
    have hf : mockRawOps.finalize stmt s1 = (.ok (), s2) := rfl
    have hEx : Internal.execOp mockRawOps { id := 1 } sql params s0 =
        (.error { kind := .invalidInput, message := "mock bind failure" }, s2) := by
      simp [Internal.execOp, Internal.execMaybeBindOp, bind, pure, StateT.bind, StateT.pure,
        state_tryFinally_eq, hp, hb, hf]
    rw [hEx]
    simp [mockRawOps, s2, assert]
  · let s0 : MockDb := { openDbs := [1], nextDbId := 2, failMode := .failStep .busy }
    let s1 : MockDb := { s0 with nextStmtId := 2, openStmts := [{ id := 1, dbId := 1, sql := sql }] }
    let s2 : MockDb :=
      { s1 with
          openStmts := [{ id := 1, dbId := 1, sql := sql, boundParams := some params }],
          boundCalls := [(sql, params)] }
    let s3 : MockDb := { s2 with openStmts := [] }
    have hs : mockRawOps.step stmt s2 = (.error { kind := .busy, message := "mock step failure" }, s2) := by
      dsimp only [mockRawOps]
      change (if _ then _ else _) = _
      rw [ite_eq_right hNBegF, ite_eq_right hNComF, ite_eq_right hNRbF]
    have hEx := execOp_step_err mockRawOps { id := 1 } sql params s0 s1 s2 s2 s3 stmt
      { kind := .busy, message := "mock step failure" } (.ok ()) rfl rfl hs rfl
    rw [hEx]
    simp [mockRawOps, s3, assert]
  · let s0 : MockDb := { openDbs := [1], nextDbId := 2, failMode := .failStep .constraint }
    let s1 : MockDb := { s0 with nextStmtId := 2, openStmts := [{ id := 1, dbId := 1, sql := sql }] }
    let s2 : MockDb :=
      { s1 with
          openStmts := [{ id := 1, dbId := 1, sql := sql, boundParams := some params }],
          boundCalls := [(sql, params)] }
    let s3 : MockDb := { s2 with openStmts := [] }
    have hs : mockRawOps.step stmt s2 =
        (.error { kind := .constraint, message := "mock step failure" }, s2) := by
      dsimp only [mockRawOps]
      change (if _ then _ else _) = _
      rw [ite_eq_right hNBegF, ite_eq_right hNComF, ite_eq_right hNRbF]
    have hEx := execOp_step_err mockRawOps { id := 1 } sql params s0 s1 s2 s2 s3 stmt
      { kind := .constraint, message := "mock step failure" } (.ok ()) rfl rfl hs rfl
    rw [hEx]
    simp [mockRawOps, s3, assert]

/-- Non-vacuity `CanReach` witness for `test_sqlite_exec_preservesActiveStmtCount_andPropagatesErrors`. -/
theorem reach_sqlite_exec_preservesActiveStmtCount_andPropagatesErrors :
    CanReach (test_sqlite_exec_preservesActiveStmtCount_andPropagatesErrors Internal.mkApiM) :=
  ⟨"INSERT INTO items(v) VALUES (?)", #[.int 1], .none, by decide, by decide,
    proof_sqlite_exec_preservesActiveStmtCount_andPropagatesErrors
      "INSERT INTO items(v) VALUES (?)" #[.int 1] .none (by decide) (by decide)⟩

/-- Proof of `test_sqlite_query_collectsRows_andPreservesActiveStmtCount` for `Internal.mkApiM`. -/
theorem proof_sqlite_query_collectsRows_andPreservesActiveStmtCount :
    AllPass (test_sqlite_query_collectsRows_andPreservesActiveStmtCount Internal.mkApiM) := by
  intro r0 r1 params
  let sOk : MockDb := { openDbs := [1], nextDbId := 2, queryRows := #[r0, r1], failMode := .none }
  let stmt : StmtHandle := { id := 1, dbId := 1 }
  have hp1 : mockRawOps.prepare { id := 1 } "SELECT id, name FROM items WHERE id = ?" sOk =
      (.ok stmt, { sOk with nextStmtId := 2, openStmts := [{ id := 1, dbId := 1, sql := "SELECT id, name FROM items WHERE id = ?" }] }) := rfl
  have hb1 : mockRawOps.bind stmt params
      { sOk with nextStmtId := 2, openStmts := [{ id := 1, dbId := 1, sql := "SELECT id, name FROM items WHERE id = ?" }] } =
      (.ok (), { sOk with
        nextStmtId := 2,
        openStmts := [{ id := 1, dbId := 1, sql := "SELECT id, name FROM items WHERE id = ?", boundParams := some params }],
        boundCalls := [("SELECT id, name FROM items WHERE id = ?", params)] }) := rfl
  let sOk2 : MockDb :=
    { sOk with
        nextStmtId := 2,
        openStmts := [{ id := 1, dbId := 1, sql := "SELECT id, name FROM items WHERE id = ?", boundParams := some params }],
        boundCalls := [("SELECT id, name FROM items WHERE id = ?", params)] }
  let sOk3 : MockDb :=
    { sOk2 with
        openStmts := [{ id := 1, dbId := 1, sql := "SELECT id, name FROM items WHERE id = ?", boundParams := some params, stepIndex := 1 }] }
  let sOk4 : MockDb :=
    { sOk2 with
        openStmts := [{ id := 1, dbId := 1, sql := "SELECT id, name FROM items WHERE id = ?", boundParams := some params, stepIndex := 2 }] }
  let sOk5 : MockDb := { sOk2 with openStmts := [] }
  have hs1a : mockRawOps.step stmt sOk2 = (.ok (.row r0), sOk3) := by
    dsimp only [mockRawOps]
    change (if _ then _ else _) = _
    dsimp only
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]
    simp [stmt, sOk, sOk2, sOk3]
  have hs1b : mockRawOps.step stmt sOk3 = (.ok (.row r1), sOk4) := by
    dsimp only [mockRawOps]
    change (if _ then _ else _) = _
    dsimp only
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]
    simp [stmt, sOk, sOk2, sOk4]
  have hs1c : mockRawOps.step stmt sOk4 = (.ok .done, sOk4) := by
    dsimp only [mockRawOps]
    change (if _ then _ else _) = _
    dsimp only
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]
    simp [sOk, sOk2, sOk4]
  have hf1 : mockRawOps.finalize stmt sOk4 = (.ok (), sOk5) := rfl
  have hQOk := queryOp_two_rows_ok mockRawOps { id := 1 } "SELECT id, name FROM items WHERE id = ?"
    params sOk _ sOk2 sOk3 sOk4 sOk4 sOk5 stmt r0 r1 hp1 hb1 hs1a hs1b hs1c hf1

  let sMid : MockDb := { openDbs := [1], nextDbId := 2, queryRows := #[r0, r1], failMode := .failStepAfterFirstRow .busy }
  let sMid1 : MockDb := { sMid with nextStmtId := 2, openStmts := [{ id := 1, dbId := 1, sql := "SELECT id, name FROM items WHERE id = ?" }] }
  let sMid2 : MockDb :=
    { sMid with
        nextStmtId := 2,
        openStmts := [{ id := 1, dbId := 1, sql := "SELECT id, name FROM items WHERE id = ?", boundParams := some params }],
        boundCalls := [("SELECT id, name FROM items WHERE id = ?", params)] }
  let sMid3 : MockDb :=
    { sMid2 with
        openStmts := [{ id := 1, dbId := 1, sql := "SELECT id, name FROM items WHERE id = ?", boundParams := some params, stepIndex := 1 }] }
  let sMid4 : MockDb := { sMid2 with openStmts := [] }
  have hp2 : mockRawOps.prepare { id := 1 } "SELECT id, name FROM items WHERE id = ?" sMid = (.ok stmt, sMid1) := rfl
  have hb2 : mockRawOps.bind stmt params sMid1 = (.ok (), sMid2) := rfl
  have hs2a : mockRawOps.step stmt sMid2 = (.ok (.row r0), sMid3) := by
    dsimp only [mockRawOps]
    change (if _ then _ else _) = _
    dsimp only
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]
    simp [stmt, sMid, sMid2, sMid3]
  have hs2b : mockRawOps.step stmt sMid3 = (.error { kind := .busy, message := "mock mid-stream step failure" }, sMid3) := by
    dsimp only [mockRawOps]
    change (if _ then _ else _) = _
    dsimp only
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]
    simp [sMid, sMid2, sMid3]
  have hf2 : mockRawOps.finalize stmt sMid3 = (.ok (), sMid4) := rfl
  have hQMid := queryOp_two_rows_mid_err mockRawOps { id := 1 } "SELECT id, name FROM items WHERE id = ?"
    params sMid sMid1 sMid2 sMid3 sMid3 sMid4 stmt r0 { kind := .busy, message := "mock mid-stream step failure" }
    (.ok ()) hp2 hb2 hs2a hs2b hf2

  dsimp only [test_sqlite_query_collectsRows_andPreservesActiveStmtCount, Bind.bind,
    Internal.mkApiM, StateT.run]
  rw [hQOk, hQMid]
  simp [mockRawOps, sOk5, sMid4, assert]

/-- Non-vacuity `CanReach` witness for `test_sqlite_query_collectsRows_andPreservesActiveStmtCount`. -/
theorem reach_sqlite_query_collectsRows_andPreservesActiveStmtCount :
    CanReach (test_sqlite_query_collectsRows_andPreservesActiveStmtCount Internal.mkApiM) :=
  ⟨#[.int 1], #[.text "a"], #[.int 1],
    proof_sqlite_query_collectsRows_andPreservesActiveStmtCount #[.int 1] #[.text "a"] #[.int 1]⟩

/-- Proof of `test_sqlite_queryOne_returnsOptionalRow_andPreservesActiveStmtCount` for `Internal.mkApiM`. -/
theorem proof_sqlite_queryOne_returnsOptionalRow_andPreservesActiveStmtCount :
    AllPass (test_sqlite_queryOne_returnsOptionalRow_andPreservesActiveStmtCount Internal.mkApiM) := by
  intro row params
  let stmt : StmtHandle := { id := 1, dbId := 1 }
  let sql := "SELECT id FROM items WHERE id = ?"

  let sE : MockDb := { openDbs := [1], nextDbId := 2, queryRows := #[], failMode := .none }
  let sE1 : MockDb := { sE with nextStmtId := 2, openStmts := [{ id := 1, dbId := 1, sql := sql }] }
  let sE2 : MockDb :=
    { sE with
        nextStmtId := 2,
        openStmts := [{ id := 1, dbId := 1, sql := sql, boundParams := some params }],
        boundCalls := [(sql, params)] }
  let sE3 : MockDb := { sE2 with openStmts := [] }
  have hsE : mockRawOps.step stmt sE2 = (.ok .done, sE2) := by
    dsimp only [mockRawOps]
    change (if _ then _ else _) = _
    dsimp only
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]
    simp [sE, sE2]
  have hE := queryOneOp_done mockRawOps { id := 1 } sql params sE sE1 sE2 sE2 sE3 stmt
    rfl rfl hsE rfl

  let sO : MockDb := { openDbs := [1], nextDbId := 2, queryRows := #[row], failMode := .none }
  let sO1 : MockDb := { sO with nextStmtId := 2, openStmts := [{ id := 1, dbId := 1, sql := sql }] }
  let sO2 : MockDb :=
    { sO with
        nextStmtId := 2,
        openStmts := [{ id := 1, dbId := 1, sql := sql, boundParams := some params }],
        boundCalls := [(sql, params)] }
  let sO3 : MockDb :=
    { sO2 with
        openStmts := [{ id := 1, dbId := 1, sql := sql, boundParams := some params, stepIndex := 1 }] }
  let sO4 : MockDb := { sO2 with openStmts := [] }
  have hsO : mockRawOps.step stmt sO2 = (.ok (.row row), sO3) := by
    dsimp only [mockRawOps]
    change (if _ then _ else _) = _
    dsimp only
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]
    simp [stmt, sO, sO2, sO3]
  have hO := queryOneOp_row mockRawOps { id := 1 } sql params sO sO1 sO2 sO3 sO4 stmt row
    rfl rfl hsO rfl

  let sB : MockDb := { openDbs := [1], nextDbId := 2, queryRows := #[row], failMode := .failStep .busy }
  let sB1 : MockDb := { sB with nextStmtId := 2, openStmts := [{ id := 1, dbId := 1, sql := sql }] }
  let sB2 : MockDb :=
    { sB with
        nextStmtId := 2,
        openStmts := [{ id := 1, dbId := 1, sql := sql, boundParams := some params }],
        boundCalls := [(sql, params)] }
  let sB3 : MockDb := { sB2 with openStmts := [] }
  have hsB : mockRawOps.step stmt sB2 = (.error { kind := .busy, message := "mock step failure" }, sB2) := by
    dsimp only [mockRawOps]
    change (if _ then _ else _) = _
    dsimp only
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
  have hB := queryOneOp_step_err mockRawOps { id := 1 } sql params sB sB1 sB2 sB2 sB3 stmt
    { kind := .busy, message := "mock step failure" } (.ok ()) rfl rfl hsB rfl

  dsimp only [test_sqlite_queryOne_returnsOptionalRow_andPreservesActiveStmtCount, Bind.bind,
    Internal.mkApiM, StateT.run]
  rw [hE, hO, hB]
  simp [mockRawOps, sE, sE2, sE3, sO, sO2, sO4, sB, sB2, sB3, assert]

/-- Non-vacuity `CanReach` witness for `test_sqlite_queryOne_returnsOptionalRow_andPreservesActiveStmtCount`. -/
theorem reach_sqlite_queryOne_returnsOptionalRow_andPreservesActiveStmtCount :
    CanReach (test_sqlite_queryOne_returnsOptionalRow_andPreservesActiveStmtCount Internal.mkApiM) :=
  ⟨#[.int 1], #[.int 1],
    proof_sqlite_queryOne_returnsOptionalRow_andPreservesActiveStmtCount #[.int 1] #[.int 1]⟩

/-- Proof of `test_sqlite_withTransaction_commitsOnOk` for `Internal.mkApiM`. -/
theorem proof_sqlite_withTransaction_commitsOnOk :
    AllPass (test_sqlite_withTransaction_commitsOnOk Internal.mkApiM) := by
  intro val
  let s0 : MockDb := { openDbs := [1], nextDbId := 2, failMode := .none }
  let s1 : MockDb := { s0 with nextStmtId := 2, inTransaction := true }
  let s2 : MockDb :=
    { s1 with
        nextStmtId := 3,
        stagedWrites := [("INSERT INTO items(v) VALUES (?)", #[val])],
        boundCalls := [("INSERT INTO items(v) VALUES (?)", #[val])] }
  let s3 : MockDb :=
    { s2 with
        nextStmtId := 4, inTransaction := false,
        committedWrites := [("INSERT INTO items(v) VALUES (?)", #[val])],
        stagedWrites := [] }
  let s1b : MockDb :=
    { s1 with
        nextStmtId := 3,
        openStmts := [{ id := 2, dbId := 1, sql := "INSERT INTO items(v) VALUES (?)", boundParams := some #[val] }],
        boundCalls := [("INSERT INTO items(v) VALUES (?)", #[val])] }
  let s1c : MockDb := { s1b with stagedWrites := [("INSERT INTO items(v) VALUES (?)", #[val])] }
  have hsIns : mockRawOps.step { id := 2, dbId := 1 } s1b = (.ok .done, s1c) := by
    dsimp only [mockRawOps]
    change (if _ then _ else _) = _
    dsimp only
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
    simp [s0, s1, s1b, s1c]
  have hBeg := execControlOp_ok mockRawOps { id := 1 } "BEGIN IMMEDIATE" s0 _ _ s1 { id := 1, dbId := 1 }
    rfl rfl rfl
  have hIns := execOp_ok mockRawOps { id := 1 } "INSERT INTO items(v) VALUES (?)" #[val] s1 _ s1b s1c s2 { id := 2, dbId := 1 }
    rfl rfl hsIns rfl
  have hCom := execControlOp_ok mockRawOps { id := 1 } "COMMIT" s2 _ _ s3 { id := 3, dbId := 1 }
    rfl rfl rfl
  dsimp only [test_sqlite_withTransaction_commitsOnOk, Bind.bind,
    Internal.mkApiM, Internal.withTransactionOp, StateT.run, bind, StateT.bind]
  rw [hBeg]
  dsimp only
  rw [state_bind_step (s1 := s3) (a := (Except.ok "committed", Except.ok ())) (by
    refine state_tryFinally_step (s1 := s2) (s2 := s3) (a := Except.ok "committed") (b := Except.ok ()) ?_ hCom
    refine Eq.trans (b := match Internal.execOp mockRawOps { id := 1 } "INSERT INTO items(v) VALUES (?)" #[val] s1 with
      | (.error e, s') => (.error e, s')
      | (.ok (), s') => (.ok "committed", s')) rfl ?_
    rw [hIns])]
  simp [mockRawOps, s0, s1, s2, s3, pure, StateT.pure, assert]

/-- Non-vacuity `CanReach` witness for `test_sqlite_withTransaction_commitsOnOk`. -/
theorem reach_sqlite_withTransaction_commitsOnOk :
    CanReach (test_sqlite_withTransaction_commitsOnOk Internal.mkApiM) :=
  ⟨.int 42, proof_sqlite_withTransaction_commitsOnOk (.int 42)⟩

/-- Proof of `test_sqlite_withTransaction_rollsBackOnError` for `Internal.mkApiM`. -/
theorem proof_sqlite_withTransaction_rollsBackOnError :
    AllPass (test_sqlite_withTransaction_rollsBackOnError Internal.mkApiM) := by
  intro val err
  let pre : String × Array SqliteValue := ("INSERT INTO items(v) VALUES (?)", #[.int 1])
  let s0 : MockDb := { openDbs := [1], nextDbId := 2, committedWrites := [pre], failMode := .none }
  let s1 : MockDb := { s0 with nextStmtId := 2, inTransaction := true }
  let s2 : MockDb :=
    { s1 with
        nextStmtId := 3,
        stagedWrites := [("INSERT INTO items(v) VALUES (?)", #[val])],
        boundCalls := [("INSERT INTO items(v) VALUES (?)", #[val])] }
  let s3 : MockDb :=
    { s2 with
        nextStmtId := 4, inTransaction := false, stagedWrites := [] }
  let s1b : MockDb :=
    { s1 with
        nextStmtId := 3,
        openStmts := [{ id := 2, dbId := 1, sql := "INSERT INTO items(v) VALUES (?)", boundParams := some #[val] }],
        boundCalls := [("INSERT INTO items(v) VALUES (?)", #[val])] }
  let s1c : MockDb := { s1b with stagedWrites := [("INSERT INTO items(v) VALUES (?)", #[val])] }
  have hsIns : mockRawOps.step { id := 2, dbId := 1 } s1b = (.ok .done, s1c) := by
    dsimp only [mockRawOps]
    change (if _ then _ else _) = _
    dsimp only
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
    simp [s0, s1, s1b, s1c]
  have hBeg := execControlOp_ok mockRawOps { id := 1 } "BEGIN IMMEDIATE" s0 _ _ s1 { id := 1, dbId := 1 }
    rfl rfl rfl
  have hIns := execOp_ok mockRawOps { id := 1 } "INSERT INTO items(v) VALUES (?)" #[val] s1 _ s1b s1c s2 { id := 2, dbId := 1 }
    rfl rfl hsIns rfl
  have hRb := execControlOp_ok mockRawOps { id := 1 } "ROLLBACK" s2 _ _ s3 { id := 3, dbId := 1 }
    rfl rfl rfl
  dsimp only [test_sqlite_withTransaction_rollsBackOnError, Bind.bind,
    Internal.mkApiM, Internal.withTransactionOp, StateT.run, bind, pure, StateT.bind, StateT.pure]
  rw [hBeg]
  dsimp only
  rw [state_bind_step (s1 := s3) (a := (Except.error err, Except.ok ())) (by
    refine state_tryFinally_step (s1 := s2) (s2 := s3) (a := Except.error err) (b := Except.ok ()) ?_ hRb
    refine Eq.trans (b := match Internal.execOp mockRawOps { id := 1 } "INSERT INTO items(v) VALUES (?)" #[val] s1 with
      | (.error e, s') => (.error e, s')
      | (.ok (), s') => (.error err, s')) rfl ?_
    rw [hIns])]
  simp [mockRawOps, pre, s0, s1, s2, s3, pure, StateT.pure, assert]

/-- Non-vacuity `CanReach` witness for `test_sqlite_withTransaction_rollsBackOnError`. -/
theorem reach_sqlite_withTransaction_rollsBackOnError :
    CanReach (test_sqlite_withTransaction_rollsBackOnError Internal.mkApiM) :=
  ⟨.int 42, { kind := .constraint, message := "fail" },
    proof_sqlite_withTransaction_rollsBackOnError (.int 42) { kind := .constraint, message := "fail" }⟩

/-- Proof of `test_sqlite_withTransaction_rollsBackOnCommitAndBeginBusy` for `Internal.mkApiM`. -/
theorem proof_sqlite_withTransaction_rollsBackOnCommitAndBeginBusy :
    AllPass (test_sqlite_withTransaction_rollsBackOnCommitAndBeginBusy Internal.mkApiM) := by
  intro val
  let sBegin : MockDb := { openDbs := [1], nextDbId := 2, failMode := .failBegin .busy }
  let sBegin1 : MockDb :=
    { sBegin with
        nextStmtId := 2,
        openStmts := [{ id := 1, dbId := 1, sql := "BEGIN IMMEDIATE" }] }
  let sBegin2 : MockDb := { sBegin1 with openStmts := [] }
  have hBegErr := execControlOp_step_err mockRawOps { id := 1 } "BEGIN IMMEDIATE"
    sBegin sBegin1 sBegin1 sBegin2 { id := 1, dbId := 1 }
    { kind := .busy, message := "mock begin failure" } (.ok ()) rfl rfl rfl

  let sCom : MockDb := { openDbs := [1], nextDbId := 2, failMode := .failCommit .busy }
  let sCom1 : MockDb := { sCom with nextStmtId := 2, inTransaction := true }
  let sCom2 : MockDb :=
    { sCom1 with
        nextStmtId := 3,
        stagedWrites := [("INSERT INTO items(v) VALUES (?)", #[val])],
        boundCalls := [("INSERT INTO items(v) VALUES (?)", #[val])] }
  let sCom3a : MockDb :=
    { sCom2 with
        nextStmtId := 4,
        openStmts := [{ id := 3, dbId := 1, sql := "COMMIT" }] }
  let sCom3 : MockDb :=
    { openDbs := [1], nextDbId := 2, nextStmtId := 4, inTransaction := true,
      stagedWrites := [("INSERT INTO items(v) VALUES (?)", #[val])],
      boundCalls := [("INSERT INTO items(v) VALUES (?)", #[val])],
      failMode := .failCommit .busy }
  let sCom4 : MockDb :=
    { openDbs := [1], nextDbId := 2, nextStmtId := 5, inTransaction := false,
      stagedWrites := [],
      boundCalls := [("INSERT INTO items(v) VALUES (?)", #[val])],
      failMode := .failCommit .busy }
  let sCom1b : MockDb :=
    { sCom1 with
        nextStmtId := 3,
        openStmts := [{ id := 2, dbId := 1, sql := "INSERT INTO items(v) VALUES (?)", boundParams := some #[val] }],
        boundCalls := [("INSERT INTO items(v) VALUES (?)", #[val])] }
  let sCom1c : MockDb := { sCom1b with stagedWrites := [("INSERT INTO items(v) VALUES (?)", #[val])] }
  have hsCIns : mockRawOps.step { id := 2, dbId := 1 } sCom1b = (.ok .done, sCom1c) := by
    dsimp only [mockRawOps]
    change (if _ then _ else _) = _
    dsimp only
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
    simp [sCom, sCom1, sCom1b, sCom1c]
  have hCBeg := execControlOp_ok mockRawOps { id := 1 } "BEGIN IMMEDIATE" sCom _ _ sCom1 { id := 1, dbId := 1 }
    rfl rfl rfl
  have hCIns := execOp_ok mockRawOps { id := 1 } "INSERT INTO items(v) VALUES (?)" #[val] sCom1 _ sCom1b sCom1c sCom2 { id := 2, dbId := 1 }
    rfl rfl hsCIns rfl
  have hCCom := execControlOp_step_err mockRawOps { id := 1 } "COMMIT" sCom2 sCom3a sCom3a sCom3 { id := 3, dbId := 1 }
    { kind := .busy, message := "mock commit failure" } (.ok ()) rfl rfl rfl
  have hCRb := execControlOp_ok mockRawOps { id := 1 } "ROLLBACK" sCom3 _ _ sCom4 { id := 4, dbId := 1 }
    rfl rfl rfl

  dsimp only [test_sqlite_withTransaction_rollsBackOnCommitAndBeginBusy, Bind.bind,
    Internal.mkApiM, Internal.withTransactionOp, StateT.run, bind, pure, StateT.bind, StateT.pure]
  rw [hBegErr, hCBeg]
  dsimp only
  rw [state_bind_step (s1 := sCom3) (a := (Except.ok (), Except.error ({ kind := .busy, message := "mock commit failure" } : SqliteError))) (by
    refine state_tryFinally_step (s1 := sCom2) (s2 := sCom3)
      (a := Except.ok ()) (b := Except.error ({ kind := .busy, message := "mock commit failure" } : SqliteError)) ?_ hCCom
    refine Eq.trans (b := Internal.execOp mockRawOps { id := 1 } "INSERT INTO items(v) VALUES (?)" #[val] sCom1) rfl hCIns)]
  dsimp only
  simp only [StateT.bind, Bind.bind, Pure.pure, StateT.pure, hCRb]
  simp [mockRawOps, sBegin, sBegin1, sBegin2, sCom4, assert]

/-- Non-vacuity `CanReach` witness for `test_sqlite_withTransaction_rollsBackOnCommitAndBeginBusy`. -/
theorem reach_sqlite_withTransaction_rollsBackOnCommitAndBeginBusy :
    CanReach (test_sqlite_withTransaction_rollsBackOnCommitAndBeginBusy Internal.mkApiM) :=
  ⟨.int 42, proof_sqlite_withTransaction_rollsBackOnCommitAndBeginBusy (.int 42)⟩

/-- Proof of `test_sqlite_binding_noSqlStringInterpolation` for `Internal.mkApiM`. -/
theorem proof_sqlite_binding_noSqlStringInterpolation :
    AllPass (test_sqlite_binding_noSqlStringInterpolation Internal.mkApiM) := by
  intro payload n
  let insertSql := "INSERT INTO users(name, age) VALUES (?, ?)"
  let selectSql := "SELECT name, age FROM users WHERE name = ? AND age = ?"
  let selectOneSql := "SELECT name, age FROM users WHERE name = ? AND age = ? LIMIT 1"
  let params : Array SqliteValue := #[.text payload, .int n]
  let s0 : MockDb := { openDbs := [1], nextDbId := 2, failMode := .none }
  let s1 : MockDb :=
    { s0 with
        nextStmtId := 2,
        openStmts := [],
        committedWrites := [(insertSql, params)],
        boundCalls := [(insertSql, params)] }
  let s2 : MockDb :=
    { s1 with
        nextStmtId := 3,
        boundCalls := [(insertSql, params), (selectSql, params)] }
  let s3 : MockDb :=
    { s2 with
        nextStmtId := 4,
        boundCalls := [(insertSql, params), (selectSql, params), (selectOneSql, params)] }
  have hp1 : mockRawOps.prepare { id := 1 } insertSql s0 =
      (.ok { id := 1, dbId := 1 }, { s0 with nextStmtId := 2, openStmts := [{ id := 1, dbId := 1, sql := insertSql }] }) := rfl
  have hb1 : mockRawOps.bind { id := 1, dbId := 1 } params
      { s0 with nextStmtId := 2, openStmts := [{ id := 1, dbId := 1, sql := insertSql }] } =
      (.ok (),
        { s0 with
            nextStmtId := 2,
            openStmts := [{ id := 1, dbId := 1, sql := insertSql, boundParams := some params }],
            boundCalls := [(insertSql, params)] }) := rfl
  have hs1 : mockRawOps.step { id := 1, dbId := 1 }
      { s0 with
          nextStmtId := 2,
          openStmts := [{ id := 1, dbId := 1, sql := insertSql, boundParams := some params }],
          boundCalls := [(insertSql, params)] } =
      (.ok .done,
        { s0 with
            nextStmtId := 2,
            openStmts := [{ id := 1, dbId := 1, sql := insertSql, boundParams := some params }],
            committedWrites := [(insertSql, params)],
            boundCalls := [(insertSql, params)] }) := by
    dsimp only [mockRawOps]
    change (if _ then _ else _) = _
    dsimp only
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
    simp [s0, insertSql]
  have hf1 : mockRawOps.finalize { id := 1, dbId := 1 }
      { s0 with
          nextStmtId := 2,
          openStmts := [{ id := 1, dbId := 1, sql := insertSql, boundParams := some params }],
          committedWrites := [(insertSql, params)],
          boundCalls := [(insertSql, params)] } = (.ok (), s1) := rfl
  have hEx := execOp_ok mockRawOps { id := 1 } insertSql params s0 _ _ _ s1 { id := 1, dbId := 1 }
    hp1 hb1 hs1 hf1
  let s1q : MockDb :=
    { s1 with
        nextStmtId := 3,
        openStmts := [{ id := 2, dbId := 1, sql := selectSql, boundParams := some params }],
        boundCalls := [(insertSql, params), (selectSql, params)] }
  have hsQ : mockRawOps.step { id := 2, dbId := 1 } s1q = (.ok .done, s1q) := by
    dsimp only [mockRawOps]
    change (if _ then _ else _) = _
    dsimp only
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]
    simp [s0, s1, s1q, insertSql, selectSql]
  have hQ := queryOp_empty_ok mockRawOps { id := 1 } selectSql params s1 _ s1q s1q s2 { id := 2, dbId := 1 }
    rfl rfl hsQ rfl
  let s2q : MockDb :=
    { s2 with
        nextStmtId := 4,
        openStmts := [{ id := 3, dbId := 1, sql := selectOneSql, boundParams := some params }],
        boundCalls := [(insertSql, params), (selectSql, params), (selectOneSql, params)] }
  have hsQ1 : mockRawOps.step { id := 3, dbId := 1 } s2q = (.ok .done, s2q) := by
    dsimp only [mockRawOps]
    change (if _ then _ else _) = _
    dsimp only
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]
    simp [s0, s1, s2, s2q]
  have hQ1 := queryOneOp_done mockRawOps { id := 1 } selectOneSql params s2 _ s2q s2q s3 { id := 3, dbId := 1 }
    rfl rfl hsQ1 rfl
  dsimp only [test_sqlite_binding_noSqlStringInterpolation, Bind.bind,
    Internal.mkApiM, StateT.run]
  rw [hEx, hQ, hQ1]
  simp [assert, s3, insertSql, selectSql, selectOneSql, params]

/-- Non-vacuity `CanReach` witness for `test_sqlite_binding_noSqlStringInterpolation`. -/
theorem reach_sqlite_binding_noSqlStringInterpolation :
    CanReach (test_sqlite_binding_noSqlStringInterpolation Internal.mkApiM) :=
  ⟨"'; DROP TABLE users; --", 7,
    proof_sqlite_binding_noSqlStringInterpolation "'; DROP TABLE users; --" 7⟩

/-- Proof of `test_sqlite_withDb_withTransaction_preservesAllHandles` for `Internal.mkApiM`. -/
theorem proof_sqlite_withDb_withTransaction_preservesAllHandles :
    AllPass (test_sqlite_withDb_withTransaction_preservesAllHandles Internal.mkApiM) := by
  intro val
  let s0 : MockDb := {}
  let s1 : MockDb := { nextDbId := 2, openDbs := [1], openCalls := [(":memory:", {})] }
  let s2 : MockDb := { s1 with nextStmtId := 2, inTransaction := true }
  let s3 : MockDb :=
    { s2 with
        nextStmtId := 3,
        stagedWrites := [("INSERT INTO logs(msg) VALUES (?)", #[val])],
        boundCalls := [("INSERT INTO logs(msg) VALUES (?)", #[val])] }
  let s4 : MockDb :=
    { s3 with
        nextStmtId := 4, inTransaction := false,
        committedWrites := [("INSERT INTO logs(msg) VALUES (?)", #[val])],
        stagedWrites := [] }
  let s5 : MockDb := { s4 with openDbs := [] }
  let s2b : MockDb :=
    { s2 with
        nextStmtId := 3,
        openStmts := [{ id := 2, dbId := 1, sql := "INSERT INTO logs(msg) VALUES (?)", boundParams := some #[val] }],
        boundCalls := [("INSERT INTO logs(msg) VALUES (?)", #[val])] }
  let s2c : MockDb := { s2b with stagedWrites := [("INSERT INTO logs(msg) VALUES (?)", #[val])] }
  have hsIns : mockRawOps.step { id := 2, dbId := 1 } s2b = (.ok .done, s2c) := by
    dsimp only [mockRawOps]
    change (if _ then _ else _) = _
    dsimp only
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
    simp [s1, s2, s2b, s2c]
  have hOpen : mockRawOps.openDb ":memory:" {} s0 = (.ok { id := 1 }, s1) := rfl
  have hBeg := execControlOp_ok mockRawOps { id := 1 } "BEGIN IMMEDIATE" s1 _ _ s2 { id := 1, dbId := 1 }
    rfl rfl rfl
  have hIns := execOp_ok mockRawOps { id := 1 } "INSERT INTO logs(msg) VALUES (?)" #[val] s2 _ s2b s2c s3 { id := 2, dbId := 1 }
    rfl rfl hsIns rfl
  have hCom := execControlOp_ok mockRawOps { id := 1 } "COMMIT" s3 _ _ s4 { id := 3, dbId := 1 }
    rfl rfl rfl
  have hClose : mockRawOps.closeDb { id := 1 } s4 = (.ok (), s5) := rfl
  dsimp only [test_sqlite_withDb_withTransaction_preservesAllHandles, Bind.bind,
    Internal.mkApiM, Internal.withDbOp, Internal.validateConfigWith,
    StateT.run, bind, pure, StateT.bind, StateT.pure]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  have hNotGt : ¬ (5000 > maxBusyTimeoutMs) := by decide
  rw [ite_eq_right hNotGt]
  dsimp only
  rw [state_bind_step (s1 := s1) (a := .ok { id := 1 }) hOpen]
  dsimp only
  rw [state_bind_step (s1 := s5) (a := (Except.ok (), Except.ok ())) (by
    refine state_tryFinally_step (s1 := s4) (s2 := s5) (a := Except.ok ()) (b := Except.ok ()) ?_ hClose
    refine Eq.trans (b := Internal.withTransactionOp mockRawOps { id := 1 }
      (fun h => Internal.execOp mockRawOps h "INSERT INTO logs(msg) VALUES (?)" #[val]) s1) rfl ?_
    dsimp only [Internal.withTransactionOp, Bind.bind, StateT.bind, bind]
    rw [hBeg]
    dsimp only
    rw [state_bind_step (s1 := s4) (a := (Except.ok (), Except.ok ())) (state_tryFinally_step hIns hCom)]
    rfl)]
  simp [mockRawOps, s1, s2, s3, s4, s5, pure, StateT.pure, assert]

/-- Non-vacuity `CanReach` witness for `test_sqlite_withDb_withTransaction_preservesAllHandles`. -/
theorem reach_sqlite_withDb_withTransaction_preservesAllHandles :
    CanReach (test_sqlite_withDb_withTransaction_preservesAllHandles Internal.mkApiM) :=
  ⟨.int 99, proof_sqlite_withDb_withTransaction_preservesAllHandles (.int 99)⟩

end LeanSwe.Sqlite.Proofs
