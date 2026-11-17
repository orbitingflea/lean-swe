import Core.NondetTest
import LeanSwe.Sqlite.Raw.Types

namespace LeanSwe.Sqlite.Raw

open Core (NondetTest)
open Core.NondetTest

/-- Every error returned by `ops.mapRawError` carries a non-empty diagnostic message. -/
def test_sqliteraw_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (ops : RawSqliteOps) : runner Unit := do
  let raw ← nondet SqliteRawError
  let err := ops.mapRawError raw
  NondetTest.assert (err.message ≠ "")

/-- Known `SqliteRawError` constructors map to their corresponding `SqliteErrorKind`. -/
def test_sqliteraw_mapRawError_mapsKnownKinds
    {runner} [NondetTest runner] (ops : RawSqliteOps) : runner Unit := do
  let path? ← nondet (Option String)
  let code ← nondet UInt32
  let detail ← nondet String
  NondetTest.assert ((ops.mapRawError (.cantOpen path? code detail)).kind = .notFound)
  NondetTest.assert ((ops.mapRawError (.busy code detail)).kind = .busy)
  NondetTest.assert ((ops.mapRawError (.constraint code detail)).kind = .constraint)
  NondetTest.assert ((ops.mapRawError (.misuse code detail)).kind = .misuse)
  NondetTest.assert ((ops.mapRawError (.invalidArgument detail)).kind = .invalidInput)
  NondetTest.assert ((ops.mapRawError (.ioFailure code detail)).kind = .ioError)

/-- `openDb` keeps `activeDbCount` unchanged on error and increments by 1 on success until `closeDb`. -/
def test_sqliteraw_openClose_preservesActiveDbCount
    {S : Type} {runner} [NondetTest runner] (ops : RawSqliteOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let cfg ← nondet OpenConfig
  let (c₀, s₀') := ops.activeDbCount.run s₀
  assume (s₀' = s₀)
  let (openRes, s₁) := (ops.openDb path cfg).run s₀
  match openRes with
  | .error _ =>
    let (c₁, _) := ops.activeDbCount.run s₁
    NondetTest.assert (c₁ = c₀)
  | .ok db =>
    let (c₁, _) := ops.activeDbCount.run s₁
    NondetTest.assert (c₁ = c₀ + 1)
    let (closeRes, s₂) := (ops.closeDb db).run s₁
    assume (closeRes = .ok ())
    let (c₂, _) := ops.activeDbCount.run s₂
    NondetTest.assert (c₂ = c₀)

/-- `prepare` keeps `activeStmtCount` unchanged on error and increments by 1 on success until `finalize`. -/
def test_sqliteraw_prepareFinalize_preservesActiveStmtCount
    {S : Type} {runner} [NondetTest runner] (ops : RawSqliteOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let db ← nondet DbHandle
  let sql ← nondet String
  let (c₀, s₀') := ops.activeStmtCount.run s₀
  assume (s₀' = s₀)
  let (prepRes, s₁) := (ops.prepare db sql).run s₀
  match prepRes with
  | .error _ =>
    let (c₁, _) := ops.activeStmtCount.run s₁
    NondetTest.assert (c₁ = c₀)
  | .ok stmt =>
    let (c₁, _) := ops.activeStmtCount.run s₁
    NondetTest.assert (c₁ = c₀ + 1)
    let (finRes, s₂) := (ops.finalize stmt).run s₁
    assume (finRes = .ok ())
    let (c₂, _) := ops.activeStmtCount.run s₂
    NondetTest.assert (c₂ = c₀)

/-- Running `bind` and `step` followed by `finalize` restores `activeStmtCount` regardless of `bind`/`step` failure. -/
def test_sqliteraw_bindStepFinalize_preservesActiveStmtCount
    {S : Type} {runner} [NondetTest runner] (ops : RawSqliteOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let db ← nondet DbHandle
  let sql ← nondet String
  let params ← nondet (Array SqliteValue)
  let (c₀, s₀') := ops.activeStmtCount.run s₀
  assume (s₀' = s₀)
  let (prepRes, s₁) := (ops.prepare db sql).run s₀
  match prepRes with
  | .error _ =>
    let (c₁, _) := ops.activeStmtCount.run s₁
    NondetTest.assert (c₁ = c₀)
  | .ok stmt =>
    let (bindRes, s₂) := (ops.bind stmt params).run s₁
    let s₃ :=
      match bindRes with
      | .error _ => s₂
      | .ok () => ((ops.step stmt).run s₂).2
    let (finRes, s₄) := (ops.finalize stmt).run s₃
    assume (finRes = .ok ())
    let (c₄, _) := ops.activeStmtCount.run s₄
    NondetTest.assert (c₄ = c₀)

end LeanSwe.Sqlite.Raw
