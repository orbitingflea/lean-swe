import LeanSwe.Sqlite.Raw.Proofs.Helpers

namespace LeanSwe.Sqlite.Raw.Proofs

open Core
open Core.NondetTest
open LeanSwe.Sqlite.Raw

/-- Shared non-WAL URI proof helper for `UriNoWalProofs` and `UriProofs`. -/
theorem uriNoWal_spec (path : String)
    (hBytes : path.toUTF8.data.toList.isEmpty = false)
    (hZero : Internal.hasZeroByte path.toUTF8.data.toList = false)
    (hWal :
      Internal.shouldEnableWal path
        { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false } = false) :
    (((Internal.mkRawOps mockCOps).openDb path
        { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).1 =
        .ok { id := 1 } ∧
      !((((Internal.mkRawOps mockCOps).openDb path
          { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).2.calls.contains
          (MockCCall.prepareV2 100 "PRAGMA journal_mode = WAL;")) := by
  dsimp only [Internal.mkRawOps, Internal.setupConnection, Internal.runSetupPragma,
    Internal.stepPragmaLoop, Internal.insertRawDb, maxBusyTimeoutMs, maxSqlByteLen,
    mockCOps, mockPrepareSuccess, rawDbToken, rawStmtToken]
  simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, pure,
    StateT.run, tryFinally', MonadFinally.tryFinally',
    hBytes, hZero, hWal, Bool.false_eq_true, ↓reduceIte]
  simp
  exact ⟨rfl, rfl, rfl⟩

/-- Helper lemma 1 for `proof_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets`. -/
theorem uriNoWal_1 :
    (((Internal.mkRawOps mockCOps).openDb "file::memory:%00extra?cache=shared"
        { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).1 =
        .ok { id := 1 } ∧
      !((((Internal.mkRawOps mockCOps).openDb "file::memory:%00extra?cache=shared"
          { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).2.calls.contains
          (MockCCall.prepareV2 100 "PRAGMA journal_mode = WAL;")) :=
  uriNoWal_spec "file::memory:%00extra?cache=shared" (by decide) (by decide) (by decide)

/-- Helper lemma 2 for `proof_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets`. -/
theorem uriNoWal_2 :
    (((Internal.mkRawOps mockCOps).openDb "file:mem.db?mode=memory%00extra"
        { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).1 =
        .ok { id := 1 } ∧
      !((((Internal.mkRawOps mockCOps).openDb "file:mem.db?mode=memory%00extra"
          { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).2.calls.contains
          (MockCCall.prepareV2 100 "PRAGMA journal_mode = WAL;")) :=
  uriNoWal_spec "file:mem.db?mode=memory%00extra" (by decide) (by decide) (by decide)

/-- Helper lemma 3 for `proof_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets`. -/
theorem uriNoWal_3 :
    (((Internal.mkRawOps mockCOps).openDb "file::memory:?mode=rwc"
        { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).1 =
        .ok { id := 1 } ∧
      !((((Internal.mkRawOps mockCOps).openDb "file::memory:?mode=rwc"
          { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).2.calls.contains
          (MockCCall.prepareV2 100 "PRAGMA journal_mode = WAL;")) :=
  uriNoWal_spec "file::memory:?mode=rwc" (by decide) (by decide) (by decide)

/-- Helper lemma 4 for `proof_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets`. -/
theorem uriNoWal_4 :
    (((Internal.mkRawOps mockCOps).openDb "file://localhost/mem.db?mode=memory"
        { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).1 =
        .ok { id := 1 } ∧
      !((((Internal.mkRawOps mockCOps).openDb "file://localhost/mem.db?mode=memory"
          { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).2.calls.contains
          (MockCCall.prepareV2 100 "PRAGMA journal_mode = WAL;")) :=
  uriNoWal_spec "file://localhost/mem.db?mode=memory" (by decide) (by decide) (by decide)

/-- Helper lemma 5 for `proof_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets`. -/
theorem uriNoWal_5 :
    (((Internal.mkRawOps mockCOps).openDb "file:///mem.db?mode=memory"
        { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).1 =
        .ok { id := 1 } ∧
      !((((Internal.mkRawOps mockCOps).openDb "file:///mem.db?mode=memory"
          { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).2.calls.contains
          (MockCCall.prepareV2 100 "PRAGMA journal_mode = WAL;")) :=
  uriNoWal_spec "file:///mem.db?mode=memory" (by decide) (by decide) (by decide)

end LeanSwe.Sqlite.Raw.Proofs
