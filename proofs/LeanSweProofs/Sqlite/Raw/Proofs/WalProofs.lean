import LeanSweProofs.Sqlite.Raw.Proofs.Helpers

namespace LeanSwe.Sqlite.Raw.Proofs

open Core
open Core.NondetTest
open LeanSwe.Sqlite.Raw

/-- Proof of `test_sqliteraw_openDb_skipsWalOnMemoryAndReadOnlyTargets` for `Internal.mkRawOps`. -/
theorem proof_sqliteraw_openDb_skipsWalOnMemoryAndReadOnlyTargets :
    AllPass (test_sqliteraw_openDb_skipsWalOnMemoryAndReadOnlyTargets Internal.mkRawOps) := by
  intro name h1 h2
  rcases h1 with ⟨hNoNul, hNoQ, hNoHash⟩
  have hSymZero : Internal.hasZeroByte ("file:" ++ name ++ "?mode=memory").toUTF8.data.toList = false := by
    rw [toUTF8_append_data_toList, toUTF8_append_data_toList, hasZeroByte_append, hasZeroByte_append]
    have hz1 : Internal.hasZeroByte "file:".toUTF8.data.toList = false := by decide
    have hz3 : Internal.hasZeroByte "?mode=memory".toUTF8.data.toList = false := by decide
    have hz2 : Internal.hasZeroByte name.toUTF8.data.toList = false := by
      cases hz : Internal.hasZeroByte name.toUTF8.data.toList
      · rfl
      · exact absurd ((hasZeroByte_toUTF8_iff name).mp hz) hNoNul
    rw [hz1, hz2, hz3]
    decide
  have hNoQBytes : (0x3F : UInt8) ∉ name.toUTF8.data.toList := by
    intro hmem
    exact hNoQ (by simpa using (mem_toUTF8_iff_of_lt 0x3F (by decide) name).mp hmem)
  have hNoHashBytes : (0x23 : UInt8) ∉ name.toUTF8.data.toList := by
    intro hmem
    exact hNoHash (by simpa using (mem_toUTF8_iff_of_lt 0x23 (by decide) name).mp hmem)
  have hNotSlashSlash : (name.toUTF8.data.toList ++ "?mode=memory".toUTF8.data.toList).take 2 ≠ [0x2F, 0x2F] := by
    intro heq
    have hTakeName : name.toUTF8.data.toList.take 2 ≠ [0x2F, 0x2F] := by
      simpa [bne_iff_ne] using h2
    match hnb : name.toUTF8.data.toList with
    | [] =>
      rw [hnb] at heq
      exact (by decide : ("?mode=memory".toUTF8.data.toList).take 2 ≠ [0x2F, 0x2F]) heq
    | [b0] =>
      rw [hnb] at heq
      have hMode : "?mode=memory".toUTF8.data.toList =
          0x3F :: [0x6D, 0x6F, 0x64, 0x65, 0x3D, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79] := by decide
      rw [hMode] at heq
      simp only [List.singleton_append, List.take_succ_cons, List.take_zero,
        List.cons.injEq, and_true] at heq
      exact (by decide : (0x3F : UInt8) ≠ 0x2F) heq.2
    | b0 :: b1 :: rest =>
      rw [hnb] at heq hTakeName
      exact hTakeName heq
  have hClassifySym :
      Internal.classifyPathBytes ("file:" ++ name ++ "?mode=memory").toUTF8.data.toList = (true, false) := by
    rw [toUTF8_append_data_toList, toUTF8_append_data_toList]
    have hFile : "file:".toUTF8.data.toList = [0x66, 0x69, 0x6C, 0x65, 0x3A] := by decide
    have hMode : "?mode=memory".toUTF8.data.toList =
        0x3F :: [0x6D, 0x6F, 0x64, 0x65, 0x3D, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79] := by decide
    rw [hFile, hMode]
    change Internal.classifyPathBytes
      ([0x66, 0x69, 0x6C, 0x65, 0x3A] ++ (name.toUTF8.data.toList ++
        0x3F :: [0x6D, 0x6F, 0x64, 0x65, 0x3D, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79])) = (true, false)
    have hNeCol : (([0x66, 0x69, 0x6C, 0x65, 0x3A] ++ (name.toUTF8.data.toList ++
        0x3F :: [0x6D, 0x6F, 0x64, 0x65, 0x3D, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79])) ==
        Internal.colonMemoryColonBytes) = false := by
      simp [Internal.colonMemoryColonBytes]
    have hStrip : Internal.stripFileScheme
        ([0x66, 0x69, 0x6C, 0x65, 0x3A] ++ (name.toUTF8.data.toList ++
          0x3F :: [0x6D, 0x6F, 0x64, 0x65, 0x3D, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79])) =
        some (name.toUTF8.data.toList ++
          0x3F :: [0x6D, 0x6F, 0x64, 0x65, 0x3D, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79]) := rfl
    simp only [Internal.classifyPathBytes, hNeCol, Bool.false_eq_true, ↓reduceIte, hStrip]
    have hNoHashAll : (0x23 : UInt8) ∉ name.toUTF8.data.toList ++
        0x3F :: [0x6D, 0x6F, 0x64, 0x65, 0x3D, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79] := by
      intro hm
      rcases List.mem_append.mp hm with hm1 | hm2
      · exact hNoHashBytes hm1
      · exact absurd hm2 (by decide)
    rw [takeBeforeByte_eq_self 0x23 _ hNoHashAll]
    have hNotSlashSlash' : (name.toUTF8.data.toList ++
        (0x3F :: [0x6D, 0x6F, 0x64, 0x65, 0x3D, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79])).take 2 ≠ [0x2F, 0x2F] := by
      simpa [← hMode] using hNotSlashSlash
    rw [stripAuthority_eq_self_of_take2 _ hNotSlashSlash']
    rw [splitFirstByte_append_left 0x3F _ _ hNoQBytes]
    have hMemMode : (Internal.extractLastUriMode (Internal.splitOnByte 0x26
        [0x6D, 0x6F, 0x64, 0x65, 0x3D, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79]) ==
        some Internal.memoryModeBytes) = true := by decide
    have hRoMode : (Internal.extractLastUriMode (Internal.splitOnByte 0x26
        [0x6D, 0x6F, 0x64, 0x65, 0x3D, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79]) ==
        some Internal.roModeBytes) = false := by decide
    dsimp only
    rw [hMemMode, hRoMode]
    simp
  have hFileListNotEmpty : ("file:" ++ name ++ "?mode=memory").toList.isEmpty = false := by
    simp [String.toList_append]
  have hSymNotEmpty : (("file:" ++ name ++ "?mode=memory").toUTF8.data.toList.isEmpty) = false := by
    have hFile : "file:".toUTF8.data.toList = [0x66, 0x69, 0x6C, 0x65, 0x3A] := by decide
    rw [toUTF8_append_data_toList, toUTF8_append_data_toList, hFile]
    rfl
  have hNoWalCall :
      !([MockCCall.openV2 ("file:" ++ name ++ "?mode=memory")
            (sqliteOpenFullMutex ||| sqliteOpenUri ||| sqliteOpenReadWrite ||| sqliteOpenCreate),
          MockCCall.extendedResultCodes 100 true,
          MockCCall.busyTimeout 100 5000].contains
        (MockCCall.prepareV2 100 "PRAGMA journal_mode = WAL;")) = true := rfl
  dsimp only [test_sqliteraw_openDb_skipsWalOnMemoryAndReadOnlyTargets,
    Internal.mkRawOps, Internal.setupConnection, Internal.shouldEnableWal, Internal.insertRawDb,
    Internal.computeOpenFlags, Internal.runSetupPragma, Internal.stepPragmaLoop,
    maxBusyTimeoutMs, mockCOps, mockPrepareSuccess, rawDbToken, rawStmtToken, assert]
  dsimp only [Bind.bind, StateT.bind, bind, Pure.pure, StateT.pure, pure,
    StateT.run, tryFinally', MonadFinally.tryFinally']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · simp only [byteArray_size_eq_zero, hasZeroByteBa_zero, classifyPathBytesBa_eq,
      hSymNotEmpty, hSymZero, hClassifySym, Bool.false_eq_true, ↓reduceIte]
    exact ⟨rfl, hNoWalCall⟩
  all_goals exact ⟨rfl, rfl⟩

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_openDb_skipsWalOnMemoryAndReadOnlyTargets`. -/
theorem reach_sqliteraw_openDb_skipsWalOnMemoryAndReadOnlyTargets :
    CanReach (test_sqliteraw_openDb_skipsWalOnMemoryAndReadOnlyTargets Internal.mkRawOps) :=
  ⟨"app.db", ⟨by decide, by decide, by decide⟩, by decide,
    proof_sqliteraw_openDb_skipsWalOnMemoryAndReadOnlyTargets "app.db"
      ⟨by decide, by decide, by decide⟩ (by decide)⟩

/-- Proof of `test_sqliteraw_openDb_closesHandleOnAnySetupFailure` for `Internal.mkRawOps`. -/
theorem proof_sqliteraw_openDb_closesHandleOnAnySetupFailure :
    AllPass (test_sqliteraw_openDb_closesHandleOnAnySetupFailure Internal.mkRawOps) := by
  intro code detail
  have hLiveNil : hasLiveRawStmtForDb 100 [] = false := rfl
  have hLive200 : hasLiveRawStmt 200 [(100, 200)] = true := rfl
  have hLive201 : hasLiveRawStmt 201 [(100, 201)] = true := rfl
  have hAppCls : Internal.classifyPathBytes "app.db".toByteArray.data.toList = (false, false) := by decide
  have hAppZero : Internal.hasZeroByte "app.db".toByteArray.data.toList = false := by decide
  dsimp only [test_sqliteraw_openDb_closesHandleOnAnySetupFailure,
    Internal.mkRawOps, Internal.setupConnection, Internal.runSetupPragma, Internal.stepPragmaLoop,
    Internal.shouldEnableWal, Internal.computeOpenFlags, maxBusyTimeoutMs, maxSqlByteLen,
    mockCOps, mockPrepareSuccess, rawDbToken, rawStmtToken, assert]
  dsimp only [Bind.bind, StateT.bind, bind, Pure.pure, StateT.pure, pure,
    StateT.run, tryFinally', MonadFinally.tryFinally']
  simp [Internal.mapRawError, Internal.attachOpenPath, Internal.nonEmptyMsg,
    hAppCls, hAppZero, hLiveNil, hLive200, hLive201]

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_openDb_closesHandleOnAnySetupFailure`. -/
theorem reach_sqliteraw_openDb_closesHandleOnAnySetupFailure :
    CanReach (test_sqliteraw_openDb_closesHandleOnAnySetupFailure Internal.mkRawOps) :=
  ⟨5, "busy", proof_sqliteraw_openDb_closesHandleOnAnySetupFailure 5 "busy"⟩

/-- Proof of `test_sqliteraw_openClose_preservesActiveDbCountAndRejectsClosedOrBusy` for `Internal.mkRawOps`. -/
theorem proof_sqliteraw_openClose_preservesActiveDbCountAndRejectsClosedOrBusy :
    AllPass (test_sqliteraw_openClose_preservesActiveDbCountAndRejectsClosedOrBusy Internal.mkRawOps) := by
  intro unknownId hNe
  rcases hNe with ⟨hNe1, hNe2⟩
  have hBeq1 : (1 == unknownId) = false := beq_false_of_ne (Ne.symm hNe1)
  have hBeq2 : (2 == unknownId) = false := beq_false_of_ne (Ne.symm hNe2)
  have hSel1Ok : ("SELECT 1".utf8ByteSize < mockConsumedBytesUpToSemi "SELECT 1".toByteArray.data.toList ∨
      Internal.scanSqlTail .normal
        (List.drop (mockConsumedBytesUpToSemi "SELECT 1".toByteArray.data.toList)
          "SELECT 1".toByteArray.data.toList) = false) ↔ False := by decide
  have hSel1Zero : Internal.hasZeroByte "SELECT 1".toByteArray.data.toList = false := by decide
  have hAct1Live : Internal.hasActiveStmtForDb 1 [({ id := 1, dbId := 1 }, RawStmtHandle.mock 200)] = true := rfl
  have hAct2Live : Internal.hasActiveStmtForDb 2 [({ id := 1, dbId := 1 }, RawStmtHandle.mock 200)] = false := rfl
  have hAct1Nil : Internal.hasActiveStmtForDb 1 [] = false := rfl
  dsimp only [test_sqliteraw_openClose_preservesActiveDbCountAndRejectsClosedOrBusy,
    Internal.mkRawOps, Internal.withStmtLock, Internal.lookupRawDb, Internal.eraseRawDb,
    Internal.insertRawDb, Internal.lookupRawStmt, Internal.eraseRawStmt, Internal.insertRawStmt,
    Internal.setupConnection, Internal.shouldEnableWal, Internal.computeOpenFlags,
    Internal.runSetupPragma, Internal.stepPragmaLoop, maxBusyTimeoutMs, maxSqlByteLen,
    mockCOps, mockPrepareSuccess, rawDbToken, rawStmtToken, assert]
  dsimp only [Bind.bind, StateT.bind, bind, Pure.pure, StateT.pure, pure,
    StateT.run, tryFinally', MonadFinally.tryFinally']
  simp [Internal.mapRawError, Internal.nonEmptyMsg, Internal.lookupRawDb, Internal.lookupRawStmt,
    Internal.eraseRawDbAux, Internal.eraseRawStmtAux,
    hasLiveRawStmt, hasLiveRawStmtForDb,
    hBeq1, hBeq2, hSel1Ok, hSel1Zero, hAct1Live, hAct2Live, hAct1Nil]

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_openClose_preservesActiveDbCountAndRejectsClosedOrBusy`. -/
theorem reach_sqliteraw_openClose_preservesActiveDbCountAndRejectsClosedOrBusy :
    CanReach (test_sqliteraw_openClose_preservesActiveDbCountAndRejectsClosedOrBusy Internal.mkRawOps) :=
  ⟨99, ⟨by decide, by decide⟩,
    proof_sqliteraw_openClose_preservesActiveDbCountAndRejectsClosedOrBusy 99 ⟨by decide, by decide⟩⟩

end LeanSwe.Sqlite.Raw.Proofs
