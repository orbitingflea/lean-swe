import LeanSweProofs.Sqlite.Raw.Proofs.Helpers

namespace LeanSwe.Sqlite.Raw.Proofs

open Core
open Core.NondetTest
open LeanSwe.Sqlite.Raw

/-- Shared WAL-enabled URI proof helper used across `UriHasWalProofs` and `UriProofs`. -/
theorem uriHasWal_spec (path : String)
    (hBytes : path.toUTF8.data.toList.isEmpty = false)
    (hZero : Internal.hasZeroByte path.toUTF8.data.toList = false)
    (hWal :
      Internal.shouldEnableWal path
        { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false } = true) :
    (((Internal.mkRawOps mockCOps).openDb path
        { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).1 =
        .ok { id := 1 } ∧
      ((((Internal.mkRawOps mockCOps).openDb path
          { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).2.calls.contains
          (MockCCall.prepareV2 100 "PRAGMA journal_mode = WAL;")) := by
  dsimp only [Internal.mkRawOps, Internal.setupConnection, Internal.runSetupPragma,
    Internal.stepPragmaLoop, Internal.insertRawDb, maxBusyTimeoutMs, maxSqlByteLen,
    mockCOps, mockPrepareSuccess, rawDbToken, rawStmtToken]
  simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, pure,
    StateT.run, tryFinally', MonadFinally.tryFinally',
    byteArray_size_eq_zero, hasZeroByteBa_zero,
    hBytes, hZero, hWal, Bool.false_eq_true, ↓reduceIte]
  simp [hasLiveRawStmt]
  exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))

/-- WAL case 1 (`file://localhost/:memory:?cache=shared`). -/
theorem uriHasWal_1 :
    (((Internal.mkRawOps mockCOps).openDb "file://localhost/:memory:?cache=shared"
        { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).1 =
        .ok { id := 1 } ∧
      ((((Internal.mkRawOps mockCOps).openDb "file://localhost/:memory:?cache=shared"
          { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).2.calls.contains
          (MockCCall.prepareV2 100 "PRAGMA journal_mode = WAL;")) :=
  uriHasWal_spec "file://localhost/:memory:?cache=shared" (by decide) (by decide) (by decide)

/-- WAL case 2 (`file:disk.db?%00mode=memory`). -/
theorem uriHasWal_2 :
    (((Internal.mkRawOps mockCOps).openDb "file:disk.db?%00mode=memory"
        { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).1 =
        .ok { id := 1 } ∧
      ((((Internal.mkRawOps mockCOps).openDb "file:disk.db?%00mode=memory"
          { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).2.calls.contains
          (MockCCall.prepareV2 100 "PRAGMA journal_mode = WAL;")) :=
  uriHasWal_spec "file:disk.db?%00mode=memory" (by decide) (by decide) (by decide)

/-- WAL case 3 (`file:disk.db?mode=memory&mode=rwc`). -/
theorem uriHasWal_3 :
    (((Internal.mkRawOps mockCOps).openDb "file:disk.db?mode=memory&mode=rwc"
        { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).1 =
        .ok { id := 1 } ∧
      ((((Internal.mkRawOps mockCOps).openDb "file:disk.db?mode=memory&mode=rwc"
          { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).2.calls.contains
          (MockCCall.prepareV2 100 "PRAGMA journal_mode = WAL;")) :=
  uriHasWal_spec "file:disk.db?mode=memory&mode=rwc" (by decide) (by decide) (by decide)

/-- WAL case 4 (`file:mode=memory`). -/
theorem uriHasWal_4 :
    (((Internal.mkRawOps mockCOps).openDb "file:mode=memory"
        { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).1 =
        .ok { id := 1 } ∧
      ((((Internal.mkRawOps mockCOps).openDb "file:mode=memory"
          { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).2.calls.contains
          (MockCCall.prepareV2 100 "PRAGMA journal_mode = WAL;")) :=
  uriHasWal_spec "file:mode=memory" (by decide) (by decide) (by decide)

/-- WAL case 5 (`disk_mode=memory.db`). -/
theorem uriHasWal_5 :
    (((Internal.mkRawOps mockCOps).openDb "disk_mode=memory.db"
        { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).1 =
        .ok { id := 1 } ∧
      ((((Internal.mkRawOps mockCOps).openDb "disk_mode=memory.db"
          { readOnly := false, createIfMissing := true, walMode := true, foreignKeys := false }).run {}).2.calls.contains
          (MockCCall.prepareV2 100 "PRAGMA journal_mode = WAL;")) :=
  uriHasWal_spec "disk_mode=memory.db" (by decide) (by decide) (by decide)

end LeanSwe.Sqlite.Raw.Proofs
