import LeanSwe.Sqlite.Raw.Types
import LeanSwe.Sqlite.Raw.Interface
import LeanSwe.Sqlite.Raw.Impl
import LeanSwe.Sqlite.Raw.SpecTests

namespace LeanSwe.Sqlite.Raw.Proofs

open Core
open Core.NondetTest
open LeanSwe.Sqlite.Raw

private theorem nonEmptyMsg_ne_empty (fallback msg : String) (hf : fallback ≠ "") :
    Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg
  split
  · exact hf
  · next h =>
    intro hem
    subst hem
    simp [String.isEmpty] at h

private theorem append_head_ne_empty (pre rest : String) (hp : pre ≠ "") :
    pre ++ rest ≠ "" := by
  simp [String.append_eq_empty_iff, hp]

/-- Proof of `test_sqliteraw_mapRawError_returnsNonEmptyMessage` for `defaultOps`. -/
theorem proof_sqliteraw_mapRawError_returnsNonEmptyMessage :
    AllPass (test_sqliteraw_mapRawError_returnsNonEmptyMessage defaultOps) := by
  intro raw
  simp only [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]
  refine ⟨?_, trivial⟩
  cases raw with
  | cantOpen _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | busy _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | constraint _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | misuse _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | invalidArgument _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | ioFailure code _ =>
    exact nonEmptyMsg_ne_empty _ _
      (append_head_ne_empty "sqlite io failure (" (toString code ++ ")") (by decide))
  | sqliteCodeError code _ =>
    exact nonEmptyMsg_ne_empty _ _
      (append_head_ne_empty "sqlite error (" (toString code ++ ")") (by decide))
  | userError _ => exact nonEmptyMsg_ne_empty _ _ (by decide)

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_mapRawError_returnsNonEmptyMessage`. -/
theorem reach_sqliteraw_mapRawError_returnsNonEmptyMessage :
    CanReach (test_sqliteraw_mapRawError_returnsNonEmptyMessage defaultOps) :=
  ⟨.userError "", proof_sqliteraw_mapRawError_returnsNonEmptyMessage (.userError "")⟩

/-- Proof of `test_sqliteraw_mapRawError_mapsKnownKinds` for `defaultOps`. -/
theorem proof_sqliteraw_mapRawError_mapsKnownKinds :
    AllPass (test_sqliteraw_mapRawError_mapsKnownKinds defaultOps) := by
  intro path? code detail
  dsimp only [test_sqliteraw_mapRawError_mapsKnownKinds, Bind.bind, Pure.pure,
    defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_mapRawError_mapsKnownKinds`. -/
theorem reach_sqliteraw_mapRawError_mapsKnownKinds :
    CanReach (test_sqliteraw_mapRawError_mapsKnownKinds defaultOps) := by
  refine ⟨none, 5, "locked", ?_⟩
  dsimp only [test_sqliteraw_mapRawError_mapsKnownKinds, Bind.bind, Pure.pure,
    defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- Deterministic handle-accounting state used to discharge single-step `RawSqliteOpsM` contracts. -/
structure RawModelState where
  /-- Currently open DB handle identifiers. -/
  openDbs : List UInt64 := []
  /-- Currently active prepared statement handles. -/
  openStmts : List StmtHandle := []
  /-- Next identifier to allocate. -/
  nextId : UInt64 := 1
  /-- Whether `openDb` fails. -/
  failOpen : Bool := false
  /-- Whether `prepare` fails. -/
  failPrepare : Bool := false
  /-- Whether `bind` fails. -/
  failBind : Bool := false
  /-- Whether `step` fails. -/
  failStep : Bool := false
  deriving Repr, BEq

private def eraseFirst {α : Type} (p : α → Bool) : List α → Option (List α)
  | [] => none
  | x :: xs =>
    if p x then
      some xs
    else
      (eraseFirst p xs).map (x :: ·)

private theorem eraseFirst_append_self {α : Type} (p : α → Bool) (xs : List α) (y : α)
    (hy : p y = true) :
    ∃ ys, eraseFirst p (xs ++ [y]) = some ys ∧ ys.length = xs.length := by
  induction xs with
  | nil => exact ⟨[], by simp [eraseFirst, hy], rfl⟩
  | cons x rest ih =>
    simp only [List.cons_append, eraseFirst]
    cases hx : p x with
    | true => exact ⟨rest ++ [y], by simp, by simp⟩
    | false =>
      rcases ih with ⟨ys, hEq, hLen⟩
      exact ⟨x :: ys, by simp [hEq], by simp [hLen]⟩

/-- Pure `StateM RawModelState` model satisfying `RawSqliteOpsM` handle-accounting contracts. -/
def modelRawOps : RawSqliteOpsM (StateM RawModelState) :=
  { mapRawError := defaultOps.mapRawError
    openDb := fun path cfg s =>
      if s.failOpen || path.isEmpty || (cfg.readOnly && cfg.createIfMissing) ||
          cfg.busyTimeoutMs > maxBusyTimeoutMs then
        (.error { kind := .invalidInput, message := "open failed" }, s)
      else
        (.ok { id := s.nextId },
          { s with openDbs := s.openDbs ++ [s.nextId], nextId := s.nextId + 1 })
    closeDb := fun db s =>
      match eraseFirst (· == db.id) s.openDbs with
      | none => (.error { kind := .misuse, message := "unknown db" }, s)
      | some dbs' => (.ok (), { s with openDbs := dbs' })
    prepare := fun db sql s =>
      if s.failPrepare || sql.isEmpty then
        (.error { kind := .invalidInput, message := "prepare failed" }, s)
      else
        (.ok { id := s.nextId, dbId := db.id },
          { s with openStmts := s.openStmts ++ [{ id := s.nextId, dbId := db.id }], nextId := s.nextId + 1 })
    bind := fun _ _ s =>
      if s.failBind then
        (.error { kind := .invalidInput, message := "bind failed" }, s)
      else
        (.ok (), s)
    step := fun _ s =>
      if s.failStep then
        (.error { kind := .busy, message := "busy" }, s)
      else
        (.ok .done, s)
    finalize := fun stmt s =>
      match eraseFirst (fun st => st.id == stmt.id && st.dbId == stmt.dbId) s.openStmts with
      | none => (.error { kind := .misuse, message := "unknown stmt" }, s)
      | some stmts' => (.ok (), { s with openStmts := stmts' })
    activeDbCount := fun s => (s.openDbs.length, s)
    activeStmtCount := fun s => (s.openStmts.length, s) }

/-- Proof of `test_sqliteraw_openClose_preservesActiveDbCount` for `modelRawOps`. -/
theorem proof_sqliteraw_openClose_preservesActiveDbCount :
    AllPass (test_sqliteraw_openClose_preservesActiveDbCount modelRawOps) := by
  intro s₀ path cfg _
  dsimp only [test_sqliteraw_openClose_preservesActiveDbCount, Bind.bind, StateT.run, modelRawOps]
  split
  · simp [assert]
  · simp only [List.length_append, List.length_nil, List.length_cons, Nat.zero_add,
      true_and, assert]
    rcases eraseFirst_append_self (· == s₀.nextId) s₀.openDbs s₀.nextId (beq_self_eq_true _) with
      ⟨ys, hEq, hLen⟩
    intro hClose
    rw [hEq]
    exact ⟨hLen, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_openClose_preservesActiveDbCount`. -/
theorem reach_sqliteraw_openClose_preservesActiveDbCount :
    CanReach (test_sqliteraw_openClose_preservesActiveDbCount modelRawOps) := by
  refine ⟨{}, "test.db", {}, rfl, ?_⟩
  dsimp only [test_sqliteraw_openClose_preservesActiveDbCount, Bind.bind, StateT.run, modelRawOps,
    assume, assert, eraseFirst]
  exact ⟨rfl, rfl, rfl, trivial⟩

/-- Proof of `test_sqliteraw_prepareFinalize_preservesActiveStmtCount` for `modelRawOps`. -/
theorem proof_sqliteraw_prepareFinalize_preservesActiveStmtCount :
    AllPass (test_sqliteraw_prepareFinalize_preservesActiveStmtCount modelRawOps) := by
  intro s₀ db sql _
  dsimp only [test_sqliteraw_prepareFinalize_preservesActiveStmtCount, Bind.bind, StateT.run, modelRawOps]
  split
  · simp [assert]
  · simp only [List.length_append, List.length_nil, List.length_cons, Nat.zero_add,
      true_and, assert]
    have hp : (fun st : StmtHandle => st.id == s₀.nextId && st.dbId == db.id)
        { id := s₀.nextId, dbId := db.id } = true := by simp
    rcases eraseFirst_append_self (fun st : StmtHandle => st.id == s₀.nextId && st.dbId == db.id)
        s₀.openStmts { id := s₀.nextId, dbId := db.id } hp with
      ⟨ys, hEq, hLen⟩
    intro hFin
    rw [hEq]
    exact ⟨hLen, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_prepareFinalize_preservesActiveStmtCount`. -/
theorem reach_sqliteraw_prepareFinalize_preservesActiveStmtCount :
    CanReach (test_sqliteraw_prepareFinalize_preservesActiveStmtCount modelRawOps) := by
  refine ⟨{}, { id := 1 }, "SELECT 1", rfl, ?_⟩
  dsimp only [test_sqliteraw_prepareFinalize_preservesActiveStmtCount, Bind.bind, StateT.run,
    modelRawOps, assume, assert, eraseFirst]
  exact ⟨rfl, rfl, rfl, trivial⟩

/-- Proof of `test_sqliteraw_bindStepFinalize_preservesActiveStmtCount` for `modelRawOps`. -/
theorem proof_sqliteraw_bindStepFinalize_preservesActiveStmtCount :
    AllPass (test_sqliteraw_bindStepFinalize_preservesActiveStmtCount modelRawOps) := by
  intro s₀ db sql params _
  dsimp only [test_sqliteraw_bindStepFinalize_preservesActiveStmtCount, Bind.bind, StateT.run, modelRawOps]
  split
  · simp [assert]
  · simp only
    have hp : (fun st : StmtHandle => st.id == s₀.nextId && st.dbId == db.id)
        { id := s₀.nextId, dbId := db.id } = true := by simp
    rcases eraseFirst_append_self (fun st : StmtHandle => st.id == s₀.nextId && st.dbId == db.id)
        s₀.openStmts { id := s₀.nextId, dbId := db.id } hp with
      ⟨ys, hEq, hLen⟩
    by_cases hb : s₀.failBind = true
    · simp only [hb, ↓reduceIte, assert]
      rw [hEq]
      intro _
      exact ⟨hLen, trivial⟩
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      by_cases hs : s₀.failStep = true
      · simp only [hs, ↓reduceIte, assert]
        rw [hEq]
        intro _
        exact ⟨hLen, trivial⟩
      · simp only [hs, Bool.false_eq_true, ↓reduceIte, assert]
        rw [hEq]
        intro _
        exact ⟨hLen, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_bindStepFinalize_preservesActiveStmtCount`. -/
theorem reach_sqliteraw_bindStepFinalize_preservesActiveStmtCount :
    CanReach (test_sqliteraw_bindStepFinalize_preservesActiveStmtCount modelRawOps) := by
  refine ⟨{}, { id := 1 }, "SELECT ?", #[.int 1], rfl, ?_⟩
  dsimp only [test_sqliteraw_bindStepFinalize_preservesActiveStmtCount, Bind.bind, StateT.run,
    modelRawOps, assume, assert, eraseFirst]
  exact ⟨rfl, rfl, trivial⟩

end LeanSwe.Sqlite.Raw.Proofs
