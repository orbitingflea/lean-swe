import LeanSweProofs.Sqlite.Raw.Proofs.Helpers

namespace LeanSwe.Sqlite.Raw.Proofs

open Core
open Core.NondetTest
open LeanSwe.Sqlite.Raw

/-- Proof of `test_sqliteraw_prepare_rejectsNulClosedDbAndEmptySql` for `Internal.mkRawOps`. -/
theorem proof_sqliteraw_prepare_rejectsNulClosedDbAndEmptySql :
    AllPass (test_sqliteraw_prepare_rejectsNulClosedDbAndEmptySql Internal.mkRawOps) := by
  intro pre suf closedId hNe1
  have hNul : Internal.hasZeroByte (pre ++ String.ofList [Char.ofNat 0] ++ suf).toUTF8.data.toList = true := by
    rw [toUTF8_append_data_toList, toUTF8_append_data_toList, hasZeroByte_append, hasZeroByte_append]
    have hMid : Internal.hasZeroByte (String.ofList [Char.ofNat 0]).toUTF8.data.toList = true := by decide
    rw [hMid]
    simp
  have hBeq1 : (1 == closedId) = false := beq_false_of_ne (Ne.symm hNe1)
  dsimp only [test_sqliteraw_prepare_rejectsNulClosedDbAndEmptySql,
    Internal.mkRawOps, mockStateWithOpenDb, mockCOps, mockPrepareSuccess, rawDbToken, maxSqlByteLen, assert]
  dsimp only [Bind.bind, StateT.bind, bind, Pure.pure, StateT.pure, pure, StateT.run]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · by_cases hSz : (pre ++ String.ofList [Char.ofNat 0] ++ suf).utf8ByteSize > 2147483647
    · simp only [hSz, ↓reduceIte, Internal.mapRawError]
      exact ⟨assert_invalidInput_record _, rfl, rfl⟩
    · simp only [hSz, ↓reduceIte, hasZeroByteBa_zero, hNul, Internal.mapRawError]
      exact ⟨assert_invalidInput_record _, rfl, rfl⟩
  · simp [Internal.lookupRawDb, hBeq1, Internal.mapRawError, Internal.nonEmptyMsg]
  · exact ⟨errKind_eq_of_isErrorKind _ _ rfl, rfl⟩
  · exact ⟨errKind_eq_of_isErrorKind _ _ rfl, rfl⟩

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_prepare_rejectsNulClosedDbAndEmptySql`. -/
theorem reach_sqliteraw_prepare_rejectsNulClosedDbAndEmptySql :
    CanReach (test_sqliteraw_prepare_rejectsNulClosedDbAndEmptySql Internal.mkRawOps) :=
  ⟨"SELECT ", "1", 99, by decide,
    proof_sqliteraw_prepare_rejectsNulClosedDbAndEmptySql "SELECT " "1" 99 (by decide)⟩

/-- Proof of `test_sqliteraw_prepare_acceptsCommentsAndWhitespaceInTail` for `Internal.mkRawOps`. -/
theorem proof_sqliteraw_prepare_acceptsCommentsAndWhitespaceInTail :
    AllPass (test_sqliteraw_prepare_acceptsCommentsAndWhitespaceInTail Internal.mkRawOps) := by
  intro lineBody blockBody hLine hBlock
  rcases hLine with ⟨hL0, hLnl, hLsz⟩
  rcases hBlock with ⟨hB0, hBstar, hBsz⟩
  simp only [String.toUTF8] at hLsz hBsz
  have hLineZero : Internal.hasZeroByte lineBody.toUTF8.data.toList = false := by
    cases hz : Internal.hasZeroByte lineBody.toUTF8.data.toList
    · rfl
    · exact absurd ((hasZeroByte_toUTF8_iff lineBody).mp hz) hL0
  have hBlockZero : Internal.hasZeroByte blockBody.toUTF8.data.toList = false := by
    cases hz : Internal.hasZeroByte blockBody.toUTF8.data.toList
    · rfl
    · exact absurd ((hasZeroByte_toUTF8_iff blockBody).mp hz) hB0
  have hNoNl : (0x0A : UInt8) ∉ lineBody.toUTF8.data.toList := by
    intro hm
    exact hLnl (by simpa using (mem_toUTF8_iff_of_lt 0x0A (by decide) lineBody).mp hm)
  have hNoStar : (0x2A : UInt8) ∉ blockBody.toUTF8.data.toList := by
    intro hm
    exact hBstar (by simpa using (mem_toUTF8_iff_of_lt 0x2A (by decide) blockBody).mp hm)
  dsimp only [test_sqliteraw_prepare_acceptsCommentsAndWhitespaceInTail,
    Internal.mkRawOps, Internal.isIgnorableSqlTail,
    mockStateWithOpenDb, mockCOps, mockPrepareSuccess, rawDbToken, maxSqlByteLen, assert]
  dsimp only [Bind.bind, StateT.bind, bind, Pure.pure, StateT.pure, pure, StateT.run]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · have hCons : mockConsumedBytesUpToSemi ("SELECT 1; --" ++ lineBody).toUTF8.data.toList = 9 := by
      rw [toUTF8_append_data_toList]
      have hPre : "SELECT 1; --".toUTF8.data.toList =
          "SELECT 1;".toUTF8.data.toList ++ " --".toUTF8.data.toList := by decide
      rw [hPre, List.append_assoc]
      exact mockConsumedBytesUpToSemi_select1 _
    have hSzLe : ("SELECT 1; --" ++ lineBody).toUTF8.size ≤ 2147483647 := by
      simp only [String.toUTF8, String.toByteArray_append, ByteArray.size_append]
      have : "SELECT 1; --".toByteArray.size = 12 := by decide
      omega
    have hZero : Internal.hasZeroByte ("SELECT 1; --" ++ lineBody).toUTF8.data.toList = false := by
      rw [toUTF8_append_data_toList, hasZeroByte_append, hLineZero]
      decide
    have hTail : Internal.scanSqlTail .normal
        (("SELECT 1; --" ++ lineBody).toUTF8.data.toList.drop 9) = true := by
      rw [toUTF8_append_data_toList]
      have hPre : "SELECT 1; --".toUTF8.data.toList =
          [0x53, 0x45, 0x4C, 0x45, 0x43, 0x54, 0x20, 0x31, 0x3B, 0x20, 0x2D, 0x2D] := by decide
      rw [hPre]
      change Internal.scanSqlTail .normal (0x20 :: 0x2D :: 0x2D :: lineBody.toUTF8.data.toList) = true
      rw [scanSqlTail_space_dash_dash]
      exact scanSqlTail_inLineComment _ hNoNl
    have hNotGt : ¬ (("SELECT 1; --" ++ lineBody).toUTF8.size > 2147483647) := Nat.not_lt.mpr hSzLe
    have hNotEmptyStr : ("SELECT 1; --" ++ lineBody).toList.isEmpty = false := by
      simp [String.toList_append]
    simp only [stateT_bind_apply, utf8ByteSize_eq, hasZeroByteBa_zero, scanSqlTailBa_eq,
      Bool.not_true, hNotEmptyStr, hZero, Bool.false_eq_true, ↓reduceIte,
      hNotGt, hCons, hTail, Internal.lookupRawDb, Internal.insertRawStmt, beq_self_eq_true,
      List.contains_cons, List.contains_nil, Bool.or_false]
    exact ⟨rfl, rfl, rfl⟩
  · have hCons : mockConsumedBytesUpToSemi
        (("SELECT 1; --" ++ lineBody) ++ "\n \t\r\x0c").toUTF8.data.toList = 9 := by
      rw [toUTF8_append_data_toList, toUTF8_append_data_toList]
      have hPre : "SELECT 1; --".toUTF8.data.toList =
          "SELECT 1;".toUTF8.data.toList ++ " --".toUTF8.data.toList := by decide
      rw [hPre, List.append_assoc, List.append_assoc]
      exact mockConsumedBytesUpToSemi_select1 _
    have hSzLe : ("SELECT 1; --" ++ lineBody ++ "\n \t\r\x0c").toUTF8.size ≤ 2147483647 := by
      simp only [String.toUTF8, String.toByteArray_append, ByteArray.size_append]
      have h1 : "SELECT 1; --".toByteArray.size = 12 := by decide
      have h2 : "\n \t\r\x0c".toByteArray.size = 5 := by decide
      omega
    have hZero : Internal.hasZeroByte
        ("SELECT 1; --" ++ lineBody ++ "\n \t\r\x0c").toUTF8.data.toList = false := by
      rw [toUTF8_append_data_toList, toUTF8_append_data_toList,
        hasZeroByte_append, hasZeroByte_append, hLineZero]
      decide
    have hTail : Internal.scanSqlTail .normal
        (("SELECT 1; --" ++ lineBody ++ "\n \t\r\x0c").toUTF8.data.toList.drop 9) = true := by
      rw [toUTF8_append_data_toList, toUTF8_append_data_toList]
      have hPre : "SELECT 1; --".toUTF8.data.toList =
          [0x53, 0x45, 0x4C, 0x45, 0x43, 0x54, 0x20, 0x31, 0x3B, 0x20, 0x2D, 0x2D] := by decide
      have hSuf : "\n \t\r\x0c".toUTF8.data.toList = [0x0A, 0x20, 0x09, 0x0D, 0x0C] := by decide
      rw [hPre, hSuf]
      change Internal.scanSqlTail .normal
        (0x20 :: 0x2D :: 0x2D :: (lineBody.toUTF8.data.toList ++ 0x0A :: [0x20, 0x09, 0x0D, 0x0C])) = true
      rw [scanSqlTail_space_dash_dash, scanSqlTail_inLineComment_append_nl _ _ hNoNl]
      decide
    have hNotGt : ¬ (("SELECT 1; --" ++ lineBody ++ "\n \t\r\x0c").toUTF8.size > 2147483647) :=
      Nat.not_lt.mpr hSzLe
    have hNotEmptyStr : ("SELECT 1; --" ++ lineBody ++ "\n \t\r\x0c").toList.isEmpty = false := by
      simp [String.toList_append]
    simp only [stateT_bind_apply, utf8ByteSize_eq, hasZeroByteBa_zero, scanSqlTailBa_eq,
      Bool.not_true, hNotEmptyStr, hZero, Bool.false_eq_true, ↓reduceIte,
      hNotGt, hCons, hTail, Internal.lookupRawDb, Internal.insertRawStmt, beq_self_eq_true,
      List.contains_cons, List.contains_nil, Bool.or_false]
    exact ⟨rfl, rfl, rfl⟩
  · have hCons : mockConsumedBytesUpToSemi ("SELECT 1; /*" ++ blockBody ++ "*/ \n").toUTF8.data.toList = 9 := by
      rw [toUTF8_append_data_toList, toUTF8_append_data_toList]
      have hPre : "SELECT 1; /*".toUTF8.data.toList =
          "SELECT 1;".toUTF8.data.toList ++ " /*".toUTF8.data.toList := by decide
      rw [hPre, List.append_assoc, List.append_assoc]
      exact mockConsumedBytesUpToSemi_select1 _
    have hSzLe : ("SELECT 1; /*" ++ blockBody ++ "*/ \n").toUTF8.size ≤ 2147483647 := by
      simp only [String.toUTF8, String.toByteArray_append, ByteArray.size_append]
      have h1 : "SELECT 1; /*".toByteArray.size = 12 := by decide
      have h2 : "*/ \n".toByteArray.size = 4 := by decide
      omega
    have hZero : Internal.hasZeroByte
        ("SELECT 1; /*" ++ blockBody ++ "*/ \n").toUTF8.data.toList = false := by
      rw [toUTF8_append_data_toList, toUTF8_append_data_toList,
        hasZeroByte_append, hasZeroByte_append, hBlockZero]
      decide
    have hTail : Internal.scanSqlTail .normal
        (("SELECT 1; /*" ++ blockBody ++ "*/ \n").toUTF8.data.toList.drop 9) = true := by
      rw [toUTF8_append_data_toList, toUTF8_append_data_toList]
      have hPre : "SELECT 1; /*".toUTF8.data.toList =
          [0x53, 0x45, 0x4C, 0x45, 0x43, 0x54, 0x20, 0x31, 0x3B, 0x20, 0x2F, 0x2A] := by decide
      have hSuf : "*/ \n".toUTF8.data.toList = [0x2A, 0x2F, 0x20, 0x0A] := by decide
      rw [hPre, hSuf]
      change Internal.scanSqlTail .normal
        (0x20 :: 0x2F :: 0x2A :: (blockBody.toUTF8.data.toList ++ [0x2A, 0x2F, 0x20, 0x0A])) = true
      rw [scanSqlTail_space_slash_star, scanSqlTail_inBlockComment_append _ _ hNoStar]
      decide
    have hNotGt : ¬ (("SELECT 1; /*" ++ blockBody ++ "*/ \n").toUTF8.size > 2147483647) :=
      Nat.not_lt.mpr hSzLe
    have hNotEmptyStr : ("SELECT 1; /*" ++ blockBody ++ "*/ \n").toList.isEmpty = false := by
      simp [String.toList_append]
    simp only [stateT_bind_apply, utf8ByteSize_eq, hasZeroByteBa_zero, scanSqlTailBa_eq,
      Bool.not_true, hNotEmptyStr, hZero, Bool.false_eq_true, ↓reduceIte,
      hNotGt, hCons, hTail, Internal.lookupRawDb, Internal.insertRawStmt, beq_self_eq_true,
      List.contains_cons, List.contains_nil, Bool.or_false]
    exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_prepare_acceptsCommentsAndWhitespaceInTail`. -/
theorem reach_sqliteraw_prepare_acceptsCommentsAndWhitespaceInTail :
    CanReach (test_sqliteraw_prepare_acceptsCommentsAndWhitespaceInTail Internal.mkRawOps) :=
  ⟨"ok", "ok", ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    proof_sqliteraw_prepare_acceptsCommentsAndWhitespaceInTail "ok" "ok"
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩⟩

/-- Proof of `test_sqliteraw_prepare_rejectsMultiStmtAndUnclosedBlockCommentAndFinalizes` for `Internal.mkRawOps`. -/
theorem proof_sqliteraw_prepare_rejectsMultiStmtAndUnclosedBlockCommentAndFinalizes :
    AllPass (test_sqliteraw_prepare_rejectsMultiStmtAndUnclosedBlockCommentAndFinalizes Internal.mkRawOps) := by
  intro unclosedBody hAssume
  rcases hAssume with ⟨h0, hSlash, hSz⟩
  simp only [String.toUTF8] at hSz
  have hZero : Internal.hasZeroByte unclosedBody.toUTF8.data.toList = false := by
    cases hz : Internal.hasZeroByte unclosedBody.toUTF8.data.toList
    · rfl
    · exact absurd ((hasZeroByte_toUTF8_iff unclosedBody).mp hz) h0
  have hNoSlash : (0x2F : UInt8) ∉ unclosedBody.toUTF8.data.toList := by
    intro hm
    exact hSlash (by simpa using (mem_toUTF8_iff_of_lt 0x2F (by decide) unclosedBody).mp hm)
  dsimp only [test_sqliteraw_prepare_rejectsMultiStmtAndUnclosedBlockCommentAndFinalizes,
    Internal.mkRawOps, Internal.isIgnorableSqlTail,
    mockStateWithOpenDb, mockCOps, mockPrepareSuccess, rawDbToken, rawStmtToken,
    maxSqlByteLen, assert]
  dsimp only [Bind.bind, StateT.bind, bind, Pure.pure, StateT.pure, pure, StateT.run]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · have hCons : mockConsumedBytesUpToSemi ("SELECT 1; /*" ++ unclosedBody).toUTF8.data.toList = 9 := by
      rw [toUTF8_append_data_toList]
      have hPre : "SELECT 1; /*".toUTF8.data.toList =
          "SELECT 1;".toUTF8.data.toList ++ " /*".toUTF8.data.toList := by decide
      rw [hPre, List.append_assoc]
      exact mockConsumedBytesUpToSemi_select1 _
    have hSzLe : ("SELECT 1; /*" ++ unclosedBody).toUTF8.size ≤ 2147483647 := by
      simp only [String.toUTF8, String.toByteArray_append, ByteArray.size_append]
      have h1 : "SELECT 1; /*".toByteArray.size = 12 := by decide
      omega
    have hAllZero : Internal.hasZeroByte ("SELECT 1; /*" ++ unclosedBody).toUTF8.data.toList = false := by
      rw [toUTF8_append_data_toList, hasZeroByte_append, hZero]
      decide
    have hTailFalse : Internal.scanSqlTail .normal
        (("SELECT 1; /*" ++ unclosedBody).toUTF8.data.toList.drop 9) = false := by
      rw [toUTF8_append_data_toList]
      have hPre : "SELECT 1; /*".toUTF8.data.toList =
          [0x53, 0x45, 0x4C, 0x45, 0x43, 0x54, 0x20, 0x31, 0x3B, 0x20, 0x2F, 0x2A] := by decide
      rw [hPre]
      change Internal.scanSqlTail .normal (0x20 :: 0x2F :: 0x2A :: unclosedBody.toUTF8.data.toList) = false
      rw [scanSqlTail_space_slash_star]
      exact scanSqlTail_unclosed _ hNoSlash .inBlockComment (Or.inl rfl)
    have hNotGt : ¬ (("SELECT 1; /*" ++ unclosedBody).toUTF8.size > 2147483647) := Nat.not_lt.mpr hSzLe
    have hNotEmptyStr : ("SELECT 1; /*" ++ unclosedBody).toList.isEmpty = false := by
      simp [String.toList_append]
    simp only [stateT_bind_apply, utf8ByteSize_eq, hasZeroByteBa_zero, scanSqlTailBa_eq,
      Bool.not_true, hNotEmptyStr, hAllZero, Bool.false_eq_true, ↓reduceIte,
      hNotGt, hCons, hTailFalse, Internal.lookupRawDb, Internal.mapRawError, Internal.nonEmptyMsg,
      beq_self_eq_true, List.contains_cons, List.contains_nil, Bool.or_false, String.isEmpty]
    exact ⟨⟨_, rfl, rfl⟩, rfl, rfl⟩
  all_goals
    exact ⟨errKind_eq_of_isErrorKind _ _ rfl, rfl, rfl⟩

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_prepare_rejectsMultiStmtAndUnclosedBlockCommentAndFinalizes`. -/
theorem reach_sqliteraw_prepare_rejectsMultiStmtAndUnclosedBlockCommentAndFinalizes :
    CanReach (test_sqliteraw_prepare_rejectsMultiStmtAndUnclosedBlockCommentAndFinalizes Internal.mkRawOps) :=
  ⟨"unclosed", ⟨by decide, by decide, by decide⟩,
    proof_sqliteraw_prepare_rejectsMultiStmtAndUnclosedBlockCommentAndFinalizes "unclosed"
      ⟨by decide, by decide, by decide⟩⟩

private theorem bindLoop_5_none (iVal : Int64) (fVal : Float) (sVal : String) (bVal : ByteArray)
    (calls0 : List MockCCall) :
    (Internal.bindLoop mockCOps (.mock 200) #[.null, .int iVal, .real fVal, .text sVal, .bytes bVal] 5).run
      { (mockStateWithOpenStmt 5) with calls := calls0 } =
    (.ok (),
      { (mockStateWithOpenStmt 5) with
        calls := calls0 ++
          [ MockCCall.bindNull 200 1
          , MockCCall.bindInt64 200 2 iVal
          , MockCCall.bindDouble 200 3 fVal
          , MockCCall.bindText 200 4 sVal
          , MockCCall.bindBlob 200 5 bVal ] }) := by
  have hLive : hasLiveRawStmt 200 [(100, 200)] = true := rfl
  simp only [Internal.bindLoop, Internal.bindOneParam, Bind.bind, StateT.bind, Pure.pure,
    pure, StateT.run, Array.getD, Array.size, mockStateWithOpenStmt, mockCOps, rawStmtToken]
  simp [hLive]

private theorem bindLoop_5_fail4 (iVal : Int64) (fVal : Float) (sVal : String) (bVal : ByteArray)
    (calls0 : List MockCCall) :
    (Internal.bindLoop mockCOps (.mock 200) #[.null, .int iVal, .real fVal, .text sVal, .bytes bVal] 5).run
      { (mockStateWithOpenStmt 5) with
        failStep := .bindAt 4 (.ioFailure 10 "bind text ioerr")
        calls := calls0 } =
    (.error { kind := .ioError, sqliteCode := some 10, message := "bind text ioerr" },
      { (mockStateWithOpenStmt 5) with
        failStep := .bindAt 4 (.ioFailure 10 "bind text ioerr")
        calls := calls0 ++
          [ MockCCall.bindNull 200 1
          , MockCCall.bindInt64 200 2 iVal
          , MockCCall.bindDouble 200 3 fVal
          , MockCCall.bindText 200 4 sVal ] }) := by
  have hLive : hasLiveRawStmt 200 [(100, 200)] = true := rfl
  simp only [Internal.bindLoop, Internal.bindOneParam, Bind.bind, StateT.bind, Pure.pure,
    pure, StateT.run, Array.getD, Array.size, mockStateWithOpenStmt, mockCOps, rawStmtToken,
    Internal.mapRawError, Internal.nonEmptyMsg]
  simp [hLive]

private theorem mockCOps_modifyTable_eq {α : Type} (f : RawHandleTable → α × RawHandleTable)
    (s : MockCState) :
    mockCOps.modifyTable f s =
      ((f s.table).1, { s with table := (f s.table).2 }) := rfl

private theorem mockCOps_reset_eq (rawStmt : RawStmtHandle) (s : MockCState) :
    mockCOps.reset rawStmt s =
      (let stTok := rawStmtToken rawStmt
       let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.reset stTok] }
       if !(hasLiveRawStmt stTok s1.liveRawStmts) then
         (.error (.misuse 21 "raw statement handle not live"), s1)
       else
         match s1.failStep with
         | .reset err => (.error err, s1)
         | _ => (.ok (), s1)) := rfl

private theorem mockCOps_clearBindings_eq (rawStmt : RawStmtHandle) (s : MockCState) :
    mockCOps.clearBindings rawStmt s =
      (let stTok := rawStmtToken rawStmt
       let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.clearBindings stTok] }
       if !(hasLiveRawStmt stTok s1.liveRawStmts) then
         (.error (.misuse 21 "raw statement handle not live"), s1)
       else
         match s1.failStep with
         | .clearBindings err => (.error err, s1)
         | _ => (.ok (), s1)) := rfl

private theorem mockCOps_bindParamCount_eq (rawStmt : RawStmtHandle) (s : MockCState) :
    mockCOps.bindParamCount rawStmt s =
      (let stTok := rawStmtToken rawStmt
       let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.bindParamCount stTok] }
       if !(hasLiveRawStmt stTok s1.liveRawStmts) then
         (.error (.misuse 21 "raw statement handle not live"), s1)
       else
         match s1.failStep with
         | .bindParamCount err => (.error err, s1)
         | _ => (.ok s1.expectedBindParams, s1)) := rfl

private theorem mockCOps_step_eq (rawStmt : RawStmtHandle) (s : MockCState) :
    mockCOps.step rawStmt s =
      (let stTok := rawStmtToken rawStmt
       let idx := s.stepCount
       let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.step stTok], stepCount := idx + 1 }
       if !(hasLiveRawStmt stTok s1.liveRawStmts) then
         (.error (.misuse 21 "raw statement handle not live"), s1)
       else
         match s1.failStep with
         | .stepAt nth err =>
           if nth == idx then (.error err, s1)
           else match s1.stepQueue with
             | [] => (.ok .done, s1)
             | tag :: rest => (.ok tag, { s1 with stepQueue := rest })
         | _ =>
           match s1.stepQueue with
           | [] => (.ok .done, s1)
           | tag :: rest => (.ok tag, { s1 with stepQueue := rest })) := rfl

private theorem mockCOps_columnCount_eq (rawStmt : RawStmtHandle) (s : MockCState) :
    mockCOps.columnCount rawStmt s =
      (let stTok := rawStmtToken rawStmt
       let s1 : MockCState := { s with calls := s.calls ++ [MockCCall.columnCount stTok] }
       if !(hasLiveRawStmt stTok s1.liveRawStmts) then
         (.error (.misuse 21 "raw statement handle not live"), s1)
       else
         match s1.failStep with
         | .columnCount err => (.error err, s1)
         | _ => (.ok (UInt32.ofNat s1.mockColumns.size), s1)) := rfl

private theorem withStmtLock_mockCOps {α : Type} (stmt : StmtHandle)
    (act : StateM MockCState α) :
    Internal.withStmtLock mockCOps stmt act = act := by
  funext s
  rfl

/-- Proof of `test_sqliteraw_bind_resetsValidatesCountAndBindsAllFiveTypes` for `Internal.mkRawOps`. -/
theorem proof_sqliteraw_bind_resetsValidatesCountAndBindsAllFiveTypes :
    AllPass (test_sqliteraw_bind_resetsValidatesCountAndBindsAllFiveTypes Internal.mkRawOps) := by
  intro iVal fVal sVal bVal
  have hSz5 : (#[.null, .int iVal, .real fVal, .text sVal, .bytes bVal] : Array SqliteValue).size = 5 := rfl
  have hB3 := bindLoop_5_none iVal fVal sVal bVal
    [MockCCall.reset 200, MockCCall.clearBindings 200, MockCCall.bindParamCount 200]
  have hB5 := bindLoop_5_fail4 iVal fVal sVal bVal
    [MockCCall.reset 200, MockCCall.clearBindings 200, MockCCall.bindParamCount 200]
  dsimp only [StateT.run, mockStateWithOpenStmt] at hB3 hB5
  have hLive200 : hasLiveRawStmt 200 [(100, 200)] = true := rfl
  dsimp only [test_sqliteraw_bind_resetsValidatesCountAndBindsAllFiveTypes,
    Internal.mkRawOps, mockStateWithOpenStmt, rawStmtToken, assert]
  simp only [withStmtLock_mockCOps]
  dsimp only [Bind.bind, StateT.bind, bind, Pure.pure, StateT.pure, pure, StateT.run]
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
  · simp [Internal.lookupRawStmt, Internal.mapRawError, Internal.nonEmptyMsg, mockCOps]
  · simp [Internal.lookupRawStmt, Internal.mapRawError, Internal.nonEmptyMsg, mockCOps, rawStmtToken, hLive200]
  · simp [Internal.lookupRawStmt, mockCOps_modifyTable_eq, mockCOps_reset_eq,
      mockCOps_clearBindings_eq, mockCOps_bindParamCount_eq, rawStmtToken, hLive200, hSz5]
    rw [hB3]
    exact ⟨rfl, rfl⟩
  · simp [Internal.lookupRawStmt, Internal.mapRawError, Internal.nonEmptyMsg, mockCOps, rawStmtToken, hLive200]
  · simp [Internal.lookupRawStmt, mockCOps_modifyTable_eq, mockCOps_reset_eq,
      mockCOps_clearBindings_eq, mockCOps_bindParamCount_eq, rawStmtToken, hLive200, hSz5]
    rw [hB5]
    exact ⟨_, rfl, rfl⟩

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_bind_resetsValidatesCountAndBindsAllFiveTypes`. -/
theorem reach_sqliteraw_bind_resetsValidatesCountAndBindsAllFiveTypes :
    CanReach (test_sqliteraw_bind_resetsValidatesCountAndBindsAllFiveTypes Internal.mkRawOps) :=
  ⟨42, 3.5, "ok", ByteArray.empty,
    proof_sqliteraw_bind_resetsValidatesCountAndBindsAllFiveTypes 42 3.5 "ok" ByteArray.empty⟩

private theorem decodeCols5_step (iVal : Int64) (fVal : Float) (sVal : String) (badUtf8 : ByteArray)
    (st : MockCState)
    (hLive : hasLiveRawStmt 200 st.liveRawStmts = true)
    (hFail : st.failStep = .none)
    (hCols : st.mockColumns = #[.sqlNull, .sqlInt iVal, .sqlDouble fVal,
      .sqlTextBytes sVal.toUTF8, .sqlBlobBytes badUtf8]) :
    (Internal.decodeColumns mockCOps (.mock 200) 5 5 #[]).run st =
    (.ok #[.null, .int iVal, .real fVal, .text sVal, .bytes badUtf8],
      { st with
        calls := st.calls ++
          [ MockCCall.columnType 200 0
          , MockCCall.columnType 200 1, MockCCall.columnInt64 200 1
          , MockCCall.columnType 200 2, MockCCall.columnDouble 200 2
          , MockCCall.columnType 200 3, MockCCall.columnTextBytes 200 3
          , MockCCall.columnType 200 4, MockCCall.columnBlob 200 4 ] }) := by
  dsimp only [Internal.decodeColumns, Bind.bind, StateT.bind, Pure.pure, StateT.pure, pure,
    StateT.run, mockCOps, rawStmtToken]
  simp [hLive, hFail, hCols, fromUTF8?_toByteArray]

/-- Proof of `test_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors` for `Internal.mkRawOps`. -/
theorem proof_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors :
    AllPass (test_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors Internal.mkRawOps) := by
  intro iVal fVal sVal badUtf8 hBad
  have hSz5 : (#[MockCColumn.sqlNull, .sqlInt iVal, .sqlDouble fVal,
      .sqlTextBytes sVal.toUTF8, .sqlBlobBytes badUtf8] : Array MockCColumn).size = 5 := rfl
  have hSz1 : (#[MockCColumn.sqlTextBytes badUtf8] : Array MockCColumn).size = 1 := rfl
  have hLive200 : hasLiveRawStmt 200 [(100, 200)] = true := rfl
  dsimp only [test_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors,
    Internal.mkRawOps, mockStateWithOpenStmt, rawStmtToken, assert]
  simp only [withStmtLock_mockCOps]
  dsimp only [Bind.bind, StateT.bind, bind, Pure.pure, StateT.pure, pure, StateT.run]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · simp [Internal.lookupRawStmt, Internal.mapRawError, Internal.nonEmptyMsg, mockCOps]
  · simp [Internal.lookupRawStmt, mockCOps, rawStmtToken, hLive200]
  · let stRow : MockCState :=
      { mockStateWithOpenStmt 0 with
        calls := [MockCCall.step 200, MockCCall.columnCount 200]
        stepCount := 1
        stepQueue := []
        mockColumns := #[.sqlNull, .sqlInt iVal, .sqlDouble fVal,
          .sqlTextBytes sVal.toUTF8, .sqlBlobBytes badUtf8] }
    have hDc := decodeCols5_step iVal fVal sVal badUtf8 stRow rfl rfl rfl
    dsimp only [StateT.run, mockStateWithOpenStmt, stRow, String.toUTF8] at hDc
    simp [Internal.lookupRawStmt, mockCOps_modifyTable_eq, mockCOps_step_eq,
      mockCOps_columnCount_eq, rawStmtToken, hLive200]
    rw [hDc]
    simp
    exact ⟨by decide, by decide⟩
  · simp [Internal.lookupRawStmt, Internal.decodeColumns, Bind.bind, StateT.bind,
      StateT.pure, Pure.pure, pure, mockCOps, rawStmtToken,
      hLive200, hSz1, hBad, Internal.mapRawError, Internal.nonEmptyMsg]
  · simp [Internal.lookupRawStmt, mockCOps, rawStmtToken, hLive200,
      Internal.mapRawError, Internal.nonEmptyMsg]
  · simp [Internal.lookupRawStmt, Internal.decodeColumns, Bind.bind, StateT.bind,
      Pure.pure, pure, mockCOps, rawStmtToken, hLive200,
      Internal.mapRawError, Internal.nonEmptyMsg]
  · simp [Internal.lookupRawStmt, Internal.decodeColumns, Bind.bind, StateT.bind,
      Pure.pure, pure, mockCOps, rawStmtToken, hLive200,
      Internal.mapRawError, Internal.nonEmptyMsg]
  · simp [Internal.lookupRawStmt, Internal.decodeColumns, Bind.bind, StateT.bind,
      Pure.pure, pure, mockCOps, rawStmtToken, hLive200,
      Internal.mapRawError, Internal.nonEmptyMsg]
  · simp [Internal.lookupRawStmt, Internal.decodeColumns, Bind.bind, StateT.bind,
      Pure.pure, pure, mockCOps, rawStmtToken, hLive200,
      Internal.mapRawError, Internal.nonEmptyMsg]
  · simp [Internal.lookupRawStmt, Internal.decodeColumns, Bind.bind, StateT.bind,
      Pure.pure, pure, mockCOps, rawStmtToken, hLive200,
      Internal.mapRawError, Internal.nonEmptyMsg, fromUTF8?_toByteArray]

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors`. -/
theorem reach_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors :
    CanReach (test_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors Internal.mkRawOps) :=
  ⟨1, 2.0, "hi", ByteArray.mk #[0xFF], by decide,
    proof_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors 1 2.0 "hi"
      (ByteArray.mk #[0xFF]) (by decide)⟩

/-- Proof of `test_sqliteraw_finalize_releasesStmtEvenOnStickyErrorAndRejectsDoubleFinalize` for `Internal.mkRawOps`. -/
theorem proof_sqliteraw_finalize_releasesStmtEvenOnStickyErrorAndRejectsDoubleFinalize :
    AllPass (test_sqliteraw_finalize_releasesStmtEvenOnStickyErrorAndRejectsDoubleFinalize Internal.mkRawOps) := by
  intro code detail
  have hLive200 : hasLiveRawStmt 200 [(100, 200)] = true := rfl
  have hLiveDbNil : hasLiveRawStmtForDb 100 [] = false := rfl
  have hActNil : Internal.hasActiveStmtForDb 1 [] = false := rfl
  dsimp only [test_sqliteraw_finalize_releasesStmtEvenOnStickyErrorAndRejectsDoubleFinalize,
    Internal.mkRawOps, assert]
  simp only [withStmtLock_mockCOps]
  dsimp only [mockStateWithOpenStmt, mockCOps, rawStmtToken, rawDbToken,
    Bind.bind, StateT.bind, bind, Pure.pure, StateT.pure, pure, StateT.run]
  simp [Internal.lookupRawStmt, Internal.lookupRawDb, Internal.eraseRawStmt,
    Internal.eraseRawStmtAux, Internal.eraseRawDb, Internal.eraseRawDbAux,
    Internal.mapRawError, Internal.nonEmptyMsg,
    hLive200, hLiveDbNil, hActNil]

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_finalize_releasesStmtEvenOnStickyErrorAndRejectsDoubleFinalize`. -/
theorem reach_sqliteraw_finalize_releasesStmtEvenOnStickyErrorAndRejectsDoubleFinalize :
    CanReach (test_sqliteraw_finalize_releasesStmtEvenOnStickyErrorAndRejectsDoubleFinalize Internal.mkRawOps) :=
  ⟨19, "constraint",
    proof_sqliteraw_finalize_releasesStmtEvenOnStickyErrorAndRejectsDoubleFinalize 19 "constraint"⟩

end LeanSwe.Sqlite.Raw.Proofs
