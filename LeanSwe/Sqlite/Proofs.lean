import Core.Obeys
import LeanSwe.Sqlite.Interface
import LeanSwe.Sqlite.SpecTests
import LeanSwe.Sqlite.Proofs.ModelTrace

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
  dsimp only [test_sqlite_mapRawError_returnsNonEmptyMessage, Bind.bind, Pure.pure,
    defaultApi, Internal.mkApiM, Raw.defaultOps, Raw.Internal.mkRawOps,
    Raw.Internal.mapRawError, assert]
  refine ⟨?_, trivial⟩
  cases raw with
  | cantOpen _ _ _ | busy _ _ | constraint _ _ | misuse _ _ | invalidArgument _ | userError _ =>
    exact nonEmptyMsg_ne_empty _ _ (by decide)
  | ioFailure _ _ | sqliteCodeError _ _ =>
    exact nonEmptyMsg_ne_empty _ _ (by intro h; simp only [String.append_eq_empty_iff] at h; exact absurd h.2 (by decide))

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

private theorem mapRawError_eq (raw : SqliteRawError) :
    Raw.Internal.mapRawError raw = Model.mapRawError raw := by
  cases raw with
  | sqliteCodeError code detail =>
    simp only [Raw.Internal.mapRawError, Raw.Internal.nonEmptyMsg,
      Raw.Internal.classifySqliteCode, Model.mapRawError, Model.nonEmptyMsg,
      Model.classifySqliteCode]
    congr 1
  | _ =>
    simp [Raw.Internal.mapRawError, Raw.Internal.nonEmptyMsg,
      Model.mapRawError, Model.nonEmptyMsg]

/-- Proof of `test_sqlite_defaultApi_agreesWithModelValidator` for `defaultApi`. -/
theorem proof_sqlite_defaultApi_agreesWithModelValidator :
    AllPass (test_sqlite_defaultApi_agreesWithModelValidator defaultApi) := by
  intro raw cfg
  have hMap : defaultApi.mapRawError raw = Model.mapRawError raw := mapRawError_eq raw
  have hVal : defaultApi.validateConfig cfg = Model.validateConfig cfg := by
    change Internal.validateConfigWith Raw.Internal.mapRawError cfg = Model.validateConfigWith Model.mapRawError cfg
    unfold Internal.validateConfigWith Model.validateConfigWith Model.validateConfigRaw
    cases cfg.readOnly <;> cases cfg.createIfMissing <;>
      by_cases hGT : (cfg.busyTimeoutMs > maxBusyTimeoutMs) <;>
      simp [hGT, Except.mapError, mapRawError_eq]
  exact ⟨hMap, hVal, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_sqlite_defaultApi_agreesWithModelValidator`. -/
theorem reach_sqlite_defaultApi_agreesWithModelValidator :
    CanReach (test_sqlite_defaultApi_agreesWithModelValidator defaultApi) :=
  ⟨.invalidArgument "bad", {},
    proof_sqlite_defaultApi_agreesWithModelValidator (.invalidArgument "bad") {}⟩

/-- Proof of `test_sqlite_cleanupFailuresPropagate` for `Internal.mkApiM`. -/
theorem proof_sqlite_cleanupFailuresPropagate :
    AllPass (test_sqlite_cleanupFailuresPropagate Internal.mkApiM) := by
  intro failOnBody bodyErr
  dsimp only [test_sqlite_cleanupFailuresPropagate, Bind.bind, Pure.pure,
    Internal.mkApiM, StateT.run]
  have hOpen : mockRawOps.openDb ":memory:" {} { failMode := .failClose .ioError } =
      (.ok { id := 1 }, { nextDbId := 2, openDbs := [1], openCalls := [(":memory:", {})], failMode := .failClose .ioError }) := rfl
  have hClose : mockRawOps.closeDb { id := 1 }
      { nextDbId := 2, openDbs := [1], openCalls := [(":memory:", {})], failMode := .failClose .ioError } =
      (.error { kind := .ioError, message := "mock close failure" },
       { nextDbId := 2, openDbs := [], openCalls := [(":memory:", {})], failMode := .failClose .ioError }) := rfl
  have hFinExec : Internal.execOp mockRawOps { id := 1 } "DELETE FROM items" #[]
      { openDbs := [1], nextDbId := 2, failMode := .failFinalize .ioError } =
      (.error { kind := .ioError, message := "mock finalize failure" },
       { openDbs := [1], nextDbId := 2, nextStmtId := 2, openStmts := [],
         committedWrites := [("DELETE FROM items", #[])],
         boundCalls := [("DELETE FROM items", #[])],
         failMode := .failFinalize .ioError }) := by
    have hp : mockRawOps.prepare { id := 1 } "DELETE FROM items"
        { openDbs := [1], nextDbId := 2, failMode := .failFinalize .ioError } =
        (.ok { id := 1, dbId := 1 },
         { openDbs := [1], nextDbId := 2, nextStmtId := 2,
           openStmts := [{ id := 1, dbId := 1, sql := "DELETE FROM items" }],
           failMode := .failFinalize .ioError }) := rfl
    have hb : mockRawOps.bind { id := 1, dbId := 1 } #[]
        { openDbs := [1], nextDbId := 2, nextStmtId := 2,
          openStmts := [{ id := 1, dbId := 1, sql := "DELETE FROM items" }],
          failMode := .failFinalize .ioError } =
        (.ok (),
         { openDbs := [1], nextDbId := 2, nextStmtId := 2,
           openStmts := [{ id := 1, dbId := 1, sql := "DELETE FROM items", boundParams := some #[] }],
           boundCalls := [("DELETE FROM items", #[])],
           failMode := .failFinalize .ioError }) := rfl
    have hs : mockRawOps.step { id := 1, dbId := 1 }
        { openDbs := [1], nextDbId := 2, nextStmtId := 2,
          openStmts := [{ id := 1, dbId := 1, sql := "DELETE FROM items", boundParams := some #[] }],
          boundCalls := [("DELETE FROM items", #[])],
          failMode := .failFinalize .ioError } =
        (.ok .done,
         { openDbs := [1], nextDbId := 2, nextStmtId := 2,
           openStmts := [{ id := 1, dbId := 1, sql := "DELETE FROM items", boundParams := some #[] }],
           committedWrites := [("DELETE FROM items", #[])],
           boundCalls := [("DELETE FROM items", #[])],
           failMode := .failFinalize .ioError }) := rfl
    have hf : mockRawOps.finalize { id := 1, dbId := 1 }
        { openDbs := [1], nextDbId := 2, nextStmtId := 2,
          openStmts := [{ id := 1, dbId := 1, sql := "DELETE FROM items", boundParams := some #[] }],
          committedWrites := [("DELETE FROM items", #[])],
          boundCalls := [("DELETE FROM items", #[])],
          failMode := .failFinalize .ioError } =
        (.error { kind := .ioError, message := "mock finalize failure" },
         { openDbs := [1], nextDbId := 2, nextStmtId := 2, openStmts := [],
           committedWrites := [("DELETE FROM items", #[])],
           boundCalls := [("DELETE FROM items", #[])],
           failMode := .failFinalize .ioError }) := rfl
    have hLoop : Internal.execLoop mockRawOps { id := 1, dbId := 1 } Internal.maxStepFuel
        { openDbs := [1], nextDbId := 2, nextStmtId := 2,
          openStmts := [{ id := 1, dbId := 1, sql := "DELETE FROM items", boundParams := some #[] }],
          boundCalls := [("DELETE FROM items", #[])],
          failMode := .failFinalize .ioError } =
        (.ok (),
         { openDbs := [1], nextDbId := 2, nextStmtId := 2,
           openStmts := [{ id := 1, dbId := 1, sql := "DELETE FROM items", boundParams := some #[] }],
           committedWrites := [("DELETE FROM items", #[])],
           boundCalls := [("DELETE FROM items", #[])],
           failMode := .failFinalize .ioError }) := by
      change Internal.execLoop mockRawOps { id := 1, dbId := 1 } (99999999 + 1) _ = _
      exact execLoop_done mockRawOps { id := 1, dbId := 1 } 99999999 _ _ hs
    simp [Internal.execOp, Internal.execMaybeBindOp, bind, pure, StateT.bind, StateT.pure,
      state_tryFinally_eq, hp, hb, hLoop, hf]
  have hFinQuery : Internal.queryOp mockRawOps { id := 1 } "SELECT id FROM items" #[]
      { openDbs := [1], nextDbId := 2, failMode := .failFinalize .ioError } =
      (Except.error { kind := .ioError, message := "mock finalize failure" },
       { openDbs := [1], nextDbId := 2, nextStmtId := 2, openStmts := [],
         boundCalls := [("SELECT id FROM items", #[])],
         failMode := .failFinalize .ioError }) := by
    have hp : mockRawOps.prepare { id := 1 } "SELECT id FROM items"
        { openDbs := [1], nextDbId := 2, failMode := .failFinalize .ioError } =
        (.ok { id := 1, dbId := 1 },
         { openDbs := [1], nextDbId := 2, nextStmtId := 2,
           openStmts := [{ id := 1, dbId := 1, sql := "SELECT id FROM items" }],
           failMode := .failFinalize .ioError }) := rfl
    have hb : mockRawOps.bind { id := 1, dbId := 1 } #[]
        { openDbs := [1], nextDbId := 2, nextStmtId := 2,
          openStmts := [{ id := 1, dbId := 1, sql := "SELECT id FROM items" }],
          failMode := .failFinalize .ioError } =
        (.ok (),
         { openDbs := [1], nextDbId := 2, nextStmtId := 2,
           openStmts := [{ id := 1, dbId := 1, sql := "SELECT id FROM items", boundParams := some #[] }],
           boundCalls := [("SELECT id FROM items", #[])],
           failMode := .failFinalize .ioError }) := rfl
    have hs : mockRawOps.step { id := 1, dbId := 1 }
        { openDbs := [1], nextDbId := 2, nextStmtId := 2,
          openStmts := [{ id := 1, dbId := 1, sql := "SELECT id FROM items", boundParams := some #[] }],
          boundCalls := [("SELECT id FROM items", #[])],
          failMode := .failFinalize .ioError } =
        (.ok .done,
         { openDbs := [1], nextDbId := 2, nextStmtId := 2,
           openStmts := [{ id := 1, dbId := 1, sql := "SELECT id FROM items", boundParams := some #[] }],
           boundCalls := [("SELECT id FROM items", #[])],
           failMode := .failFinalize .ioError }) := rfl
    have hf : mockRawOps.finalize { id := 1, dbId := 1 }
        { openDbs := [1], nextDbId := 2, nextStmtId := 2,
          openStmts := [{ id := 1, dbId := 1, sql := "SELECT id FROM items", boundParams := some #[] }],
          boundCalls := [("SELECT id FROM items", #[])],
          failMode := .failFinalize .ioError } =
        (.error { kind := .ioError, message := "mock finalize failure" },
         { openDbs := [1], nextDbId := 2, nextStmtId := 2, openStmts := [],
           boundCalls := [("SELECT id FROM items", #[])],
           failMode := .failFinalize .ioError }) := rfl
    have hLoop : Internal.queryLoop mockRawOps { id := 1, dbId := 1 } #[] Internal.maxStepFuel
        { openDbs := [1], nextDbId := 2, nextStmtId := 2,
          openStmts := [{ id := 1, dbId := 1, sql := "SELECT id FROM items", boundParams := some #[] }],
          boundCalls := [("SELECT id FROM items", #[])],
          failMode := .failFinalize .ioError } =
        (.ok #[],
         { openDbs := [1], nextDbId := 2, nextStmtId := 2,
           openStmts := [{ id := 1, dbId := 1, sql := "SELECT id FROM items", boundParams := some #[] }],
           boundCalls := [("SELECT id FROM items", #[])],
           failMode := .failFinalize .ioError }) := by
      change Internal.queryLoop mockRawOps { id := 1, dbId := 1 } #[] (99999999 + 1) _ = _
      exact queryLoop_done mockRawOps { id := 1, dbId := 1 } #[] 99999999 _ _ hs
    simp [Internal.queryOp, bind, pure, StateT.bind, StateT.pure, state_tryFinally_eq,
      hp, hb, hLoop, hf]
  have hFinQueryOne : Internal.queryOneOp mockRawOps { id := 1 } "SELECT id FROM items" #[]
      { openDbs := [1], nextDbId := 2, failMode := .failFinalize .ioError } =
      (Except.error { kind := .ioError, message := "mock finalize failure" },
       { openDbs := [1], nextDbId := 2, nextStmtId := 2, openStmts := [],
         boundCalls := [("SELECT id FROM items", #[])],
         failMode := .failFinalize .ioError }) := rfl
  let sRbErr : MockDb := { openDbs := [1], nextDbId := 2, failMode := .failRollback .ioError }
  let sRb1 : MockDb := { sRbErr with nextStmtId := 2, inTransaction := true }
  let sRb2a : MockDb := { sRb1 with nextStmtId := 3, openStmts := [{ id := 2, dbId := 1, sql := "ROLLBACK" }] }
  let sRb2 : MockDb := { sRb1 with nextStmtId := 3 }
  have hRbBeg := execControlOp_ok mockRawOps { id := 1 } "BEGIN IMMEDIATE" sRbErr _ _ sRb1 { id := 1, dbId := 1 } rfl rfl rfl
  have hRbStep := execControlOp_step_err mockRawOps { id := 1 } "ROLLBACK" sRb1 sRb2a sRb2a sRb2 { id := 2, dbId := 1 }
    { kind := .ioError, message := "mock rollback failure" } (.ok ()) rfl rfl rfl
  have hTxBodyRb : Internal.withTransactionOp (α := String) mockRawOps { id := 1 }
      (fun _ => StateT.pure (.error bodyErr)) sRbErr =
      (.error bodyErr, sRb2) := by
    simp only [Internal.withTransactionOp, bind, StateT.bind, hRbBeg, state_tryFinally_eq, pure, StateT.pure, hRbStep]
  let sComRbErr : MockDb := { openDbs := [1], nextDbId := 2, failMode := .failCommitThenRollback .busy .ioError }
  let sCR1 : MockDb := { sComRbErr with nextStmtId := 2, inTransaction := true }
  let sCR2a : MockDb := { sCR1 with nextStmtId := 3, openStmts := [{ id := 2, dbId := 1, sql := "COMMIT" }] }
  let sCR2 : MockDb := { sCR1 with nextStmtId := 3 }
  let sCR3a : MockDb := { sCR2 with nextStmtId := 4, openStmts := [{ id := 3, dbId := 1, sql := "ROLLBACK" }] }
  let sCR3 : MockDb := { sCR2 with nextStmtId := 4 }
  have hCRBeg := execControlOp_ok mockRawOps { id := 1 } "BEGIN IMMEDIATE" sComRbErr _ _ sCR1 { id := 1, dbId := 1 } rfl rfl rfl
  have hCRCom := execControlOp_step_err mockRawOps { id := 1 } "COMMIT" sCR1 sCR2a sCR2a sCR2 { id := 2, dbId := 1 }
    { kind := .busy, message := "mock commit failure" } (.ok ()) rfl rfl rfl
  have hCRRb := execControlOp_step_err mockRawOps { id := 1 } "ROLLBACK" sCR2 sCR3a sCR3a sCR3 { id := 3, dbId := 1 }
    { kind := .ioError, message := "mock rollback failure" } (.ok ()) rfl rfl rfl
  have hTxComRb : Internal.withTransactionOp (α := String) mockRawOps { id := 1 }
      (fun _ => StateT.pure (.ok "done")) sComRbErr =
      (.error { kind := .busy, message := "mock commit failure" }, sCR3) := by
    simp only [Internal.withTransactionOp, bind, StateT.bind, hCRBeg, state_tryFinally_eq, pure, StateT.pure, hCRCom, hCRRb]
  rw [hFinExec, hFinQuery, hFinQueryOne, hTxBodyRb, hTxComRb]
  dsimp only [Internal.withDbOp, Internal.validateConfigWith]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  have hNotGt : ¬ (5000 > maxBusyTimeoutMs) := by decide
  rw [ite_eq_right hNotGt]
  simp only [bind, StateT.bind, hOpen]
  cases failOnBody <;>
    · simp only [Bool.false_eq_true, ↓reduceIte, state_tryFinally_eq, pure, StateT.pure, hClose]
      simp [mockRawOps, assert, sRb2, sRb1, sRbErr, sCR3, sCR2, sCR1, sComRbErr]

/-- Non-vacuity `CanReach` witness for `test_sqlite_cleanupFailuresPropagate`. -/
theorem reach_sqlite_cleanupFailuresPropagate :
    CanReach (test_sqlite_cleanupFailuresPropagate Internal.mkApiM) :=
  ⟨false, { kind := .ioError, message := "b" }, proof_sqlite_cleanupFailuresPropagate false { kind := .ioError, message := "b" }⟩

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
