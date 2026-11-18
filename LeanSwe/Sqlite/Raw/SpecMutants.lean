import Core.NondetTest
import LeanSwe.Sqlite.Raw.Types
import LeanSwe.Sqlite.Raw.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Sqlite.Raw`. -/

namespace LeanSwe.Sqlite.Raw

open Core (NondetTest)
open Core.NondetTest

private def stubRawOps : RawSqliteOps :=
  { mapRawError := fun raw =>
      match raw with
      | .cantOpen p? c _ => { kind := .notFound, sqliteCode := some c, path := p?, message := "cantOpen" }
      | .busy c _ => { kind := .busy, sqliteCode := some c, message := "busy" }
      | .constraint c _ => { kind := .constraint, sqliteCode := some c, message := "constraint" }
      | .misuse c _ => { kind := .misuse, sqliteCode := some c, message := "misuse" }
      | .invalidArgument _ => { kind := .invalidInput, message := "invalidArgument" }
      | .ioFailure c _ => { kind := .ioError, sqliteCode := some c, message := "ioFailure" }
      | .sqliteCodeError c _ => { kind := .ioError, sqliteCode := some c, message := "sqliteCodeError" }
      | .userError _ => { kind := .ioError, message := "userError" }
    openDb := fun _ _ => pure (.ok { id := 1 })
    closeDb := fun _ => pure (.ok ())
    prepare := fun db _ => pure (.ok { id := 1, dbId := db.id })
    bind := fun _ _ => pure (.ok ())
    step := fun _ => pure (.ok .done)
    finalize := fun _ => pure (.ok ())
    activeDbCount := pure 0
    activeStmtCount := pure 0 }

private def buggyEmptyErrRaw (base : RawSqliteOps) : RawSqliteOps :=
  { base with mapRawError := fun _ => { kind := .ioError, message := "" } }

private def buggyKindRaw (base : RawSqliteOps) : RawSqliteOps :=
  { base with mapRawError := fun _ => { kind := .ioError, message := "bad" } }

private def stubStateRawOps : RawSqliteOpsM (StateM Nat) :=
  { mapRawError := stubRawOps.mapRawError
    openDb := fun _ _ s => (.ok { id := 1 }, s + 1)
    closeDb := fun _ s => (.ok (), s - 1)
    prepare := fun db _ s => (.ok { id := 1, dbId := db.id }, s + 1)
    bind := fun _ _ s => (.ok (), s)
    step := fun _ s => (.ok .done, s)
    finalize := fun _ s => (.ok (), s - 1)
    activeDbCount := fun s => (s, s)
    activeStmtCount := fun s => (s, s) }

private def buggyOpenLeakRaw (base : RawSqliteOpsM (StateM Nat)) : RawSqliteOpsM (StateM Nat) :=
  { base with closeDb := fun _ s => (.ok (), s) }

private def buggyPrepareLeakRaw (base : RawSqliteOpsM (StateM Nat)) : RawSqliteOpsM (StateM Nat) :=
  { base with finalize := fun _ s => (.ok (), s) }

private def buggyBindStepLeakRaw (base : RawSqliteOpsM (StateM Nat)) : RawSqliteOpsM (StateM Nat) :=
  { base with
    step := fun _ s => (.error { kind := .busy, message := "busy" }, s)
    finalize := fun _ s => (.ok (), s) }

example : ¬ Core.AllPass (test_sqliteraw_mapRawError_returnsNonEmptyMessage (buggyEmptyErrRaw stubRawOps)) := by
  intro h
  have h0 := h (.userError "boom")
  simp [buggyEmptyErrRaw, assert] at h0

example : ¬ Core.AllPass (test_sqliteraw_mapRawError_mapsKnownKinds (buggyKindRaw stubRawOps)) := by
  intro h
  have h0 := h none 5 "locked"
  simp [buggyKindRaw, bind, assert] at h0

example : ¬ Core.AllPass (test_sqliteraw_openClose_preservesActiveDbCount (buggyOpenLeakRaw stubStateRawOps)) := by
  intro h
  have h0 := h 0 ":memory:" {} rfl
  simp [buggyOpenLeakRaw, stubStateRawOps, StateT.run, bind, assume, assert] at h0

example : ¬ Core.AllPass (test_sqliteraw_prepareFinalize_preservesActiveStmtCount (buggyPrepareLeakRaw stubStateRawOps)) := by
  intro h
  have h0 := h 0 { id := 1 } "SELECT 1" rfl
  simp [buggyPrepareLeakRaw, stubStateRawOps, StateT.run, bind, assume, assert] at h0

example : ¬ Core.AllPass (test_sqliteraw_bindStepFinalize_preservesActiveStmtCount (buggyBindStepLeakRaw stubStateRawOps)) := by
  intro h
  have h0 := h 0 { id := 1 } "SELECT 1" #[] rfl rfl
  simp [buggyBindStepLeakRaw, stubStateRawOps, StateT.run, assert] at h0

end LeanSwe.Sqlite.Raw
