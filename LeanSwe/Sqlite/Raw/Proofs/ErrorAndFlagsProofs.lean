import LeanSwe.Sqlite.Raw.Proofs.Helpers

namespace LeanSwe.Sqlite.Raw.Proofs

open Core
open Core.NondetTest
open LeanSwe.Sqlite.Raw

/-- Proof of `test_sqliteraw_mapRawError_returnsNonEmptyMessage` for `defaultOps`. -/
theorem proof_sqliteraw_mapRawError_returnsNonEmptyMessage :
    AllPass (test_sqliteraw_mapRawError_returnsNonEmptyMessage defaultOps) := by
  intro raw
  simp only [Bind.bind, Pure.pure, defaultOps, Internal.mkRawOps, assert]
  exact ⟨mapRawError_ne_empty raw, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_mapRawError_returnsNonEmptyMessage`. -/
theorem reach_sqliteraw_mapRawError_returnsNonEmptyMessage :
    CanReach (test_sqliteraw_mapRawError_returnsNonEmptyMessage defaultOps) :=
  ⟨.userError "", proof_sqliteraw_mapRawError_returnsNonEmptyMessage (.userError "")⟩

/-- Proof of `test_sqliteraw_mapRawError_mapsKnownKinds` for `defaultOps`. -/
theorem proof_sqliteraw_mapRawError_mapsKnownKinds :
    AllPass (test_sqliteraw_mapRawError_mapsKnownKinds defaultOps) := by
  intro raw
  cases raw with
  | cantOpen path? code detail =>
    dsimp only [test_sqliteraw_mapRawError_mapsKnownKinds, defaultOps, Internal.mkRawOps,
      Internal.mapRawError, assert]
    exact ⟨⟨rfl, rfl, rfl, nonEmptyMsg_ne_empty _ _ (by decide)⟩, trivial⟩
  | busy code detail =>
    dsimp only [test_sqliteraw_mapRawError_mapsKnownKinds, defaultOps, Internal.mkRawOps,
      Internal.mapRawError, assert]
    exact ⟨⟨rfl, rfl, rfl, nonEmptyMsg_ne_empty _ _ (by decide)⟩, trivial⟩
  | constraint code detail =>
    dsimp only [test_sqliteraw_mapRawError_mapsKnownKinds, defaultOps, Internal.mkRawOps,
      Internal.mapRawError, assert]
    exact ⟨⟨rfl, rfl, rfl, nonEmptyMsg_ne_empty _ _ (by decide)⟩, trivial⟩
  | misuse code detail =>
    dsimp only [test_sqliteraw_mapRawError_mapsKnownKinds, defaultOps, Internal.mkRawOps,
      Internal.mapRawError, assert]
    exact ⟨⟨rfl, rfl, rfl, nonEmptyMsg_ne_empty _ _ (by decide)⟩, trivial⟩
  | invalidArgument detail =>
    dsimp only [test_sqliteraw_mapRawError_mapsKnownKinds, defaultOps, Internal.mkRawOps,
      Internal.mapRawError, assert]
    exact ⟨⟨rfl, rfl, rfl, nonEmptyMsg_ne_empty _ _ (by decide)⟩, trivial⟩
  | ioFailure code detail =>
    dsimp only [test_sqliteraw_mapRawError_mapsKnownKinds, defaultOps, Internal.mkRawOps,
      Internal.mapRawError, assert]
    exact ⟨⟨rfl, rfl, rfl, nonEmptyMsg_ne_empty _ _
      (append_head_ne_empty "sqlite io failure (" (toString code ++ ")") (by decide))⟩, trivial⟩
  | sqliteCodeError code detail =>
    dsimp only [test_sqliteraw_mapRawError_mapsKnownKinds, defaultOps, Internal.mkRawOps,
      Internal.mapRawError, Internal.classifySqliteCode, assert]
    refine ⟨⟨?_, rfl, rfl, ?_⟩, trivial⟩
    · generalize (code &&& 0xFF).toNat = low
      match low with
      | 5 => rfl
      | 6 => rfl
      | 14 => rfl
      | 19 => rfl
      | 21 => rfl
      | 25 => rfl
      | _ => rfl
    · exact nonEmptyMsg_ne_empty _ _
        (append_head_ne_empty "sqlite error (" (toString code ++ ")") (by decide))
  | userError detail =>
    dsimp only [test_sqliteraw_mapRawError_mapsKnownKinds, defaultOps, Internal.mkRawOps,
      Internal.mapRawError, assert]
    exact ⟨⟨rfl, rfl, rfl, nonEmptyMsg_ne_empty _ _ (by decide)⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_mapRawError_mapsKnownKinds`. -/
theorem reach_sqliteraw_mapRawError_mapsKnownKinds :
    CanReach (test_sqliteraw_mapRawError_mapsKnownKinds defaultOps) :=
  ⟨.busy 5 "locked", proof_sqliteraw_mapRawError_mapsKnownKinds (.busy 5 "locked")⟩

/-- Proof of `test_sqliteraw_mapRawError_consistentAcrossBackends`. -/
theorem proof_sqliteraw_mapRawError_consistentAcrossBackends :
    AllPass (test_sqliteraw_mapRawError_consistentAcrossBackends defaultOps Internal.mkRawOps) := by
  intro raw
  exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_mapRawError_consistentAcrossBackends`. -/
theorem reach_sqliteraw_mapRawError_consistentAcrossBackends :
    CanReach (test_sqliteraw_mapRawError_consistentAcrossBackends defaultOps Internal.mkRawOps) :=
  ⟨.userError "err", rfl, trivial⟩

/-- Proof of `test_sqliteraw_openDb_rejectsInvalidPathAndConfigWithoutCallingC` for `Internal.mkRawOps`. -/
theorem proof_sqliteraw_openDb_rejectsInvalidPathAndConfigWithoutCallingC :
    AllPass (test_sqliteraw_openDb_rejectsInvalidPathAndConfigWithoutCallingC Internal.mkRawOps) := by
  intro path cfg hAssume
  dsimp only [test_sqliteraw_openDb_rejectsInvalidPathAndConfigWithoutCallingC,
    Internal.mkRawOps, Internal.mapRawError, assert]
  dsimp only [Bind.bind, StateT.bind, bind, Pure.pure, StateT.pure, pure, StateT.run]
  rcases hAssume with hEmpty | hNul | ⟨hRO, hCr⟩ | hGt
  · subst hEmpty
    exact ⟨⟨assert_invalidInput_record _, rfl, rfl, rfl⟩, trivial⟩
  · have hZero : Internal.hasZeroByte path.toUTF8.data.toList = true :=
      (hasZeroByte_toUTF8_iff path).mpr hNul
    cases path.toUTF8.data.toList.isEmpty
    · simp only [Bool.false_eq_true, ↓reduceIte, hZero]
      exact ⟨⟨assert_invalidInput_record _, rfl, rfl, rfl⟩, trivial⟩
    · simp only [↓reduceIte]
      exact ⟨⟨assert_invalidInput_record _, rfl, rfl, rfl⟩, trivial⟩
  · rw [hRO, hCr]
    cases path.toUTF8.data.toList.isEmpty
    · cases Internal.hasZeroByte path.toUTF8.data.toList
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_self]
        exact ⟨⟨assert_invalidInput_record _, rfl, rfl, rfl⟩, trivial⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨⟨assert_invalidInput_record _, rfl, rfl, rfl⟩, trivial⟩
    · simp only [↓reduceIte]
      exact ⟨⟨assert_invalidInput_record _, rfl, rfl, rfl⟩, trivial⟩
  · cases path.toUTF8.data.toList.isEmpty
    · cases Internal.hasZeroByte path.toUTF8.data.toList
      · cases (cfg.readOnly && cfg.createIfMissing)
        · simp only [Bool.false_eq_true, ↓reduceIte, hGt]
          exact ⟨⟨assert_invalidInput_record _, rfl, rfl, rfl⟩, trivial⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨⟨assert_invalidInput_record _, rfl, rfl, rfl⟩, trivial⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨⟨assert_invalidInput_record _, rfl, rfl, rfl⟩, trivial⟩
    · simp only [↓reduceIte]
      exact ⟨⟨assert_invalidInput_record _, rfl, rfl, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_openDb_rejectsInvalidPathAndConfigWithoutCallingC`. -/
theorem reach_sqliteraw_openDb_rejectsInvalidPathAndConfigWithoutCallingC :
    CanReach (test_sqliteraw_openDb_rejectsInvalidPathAndConfigWithoutCallingC Internal.mkRawOps) :=
  ⟨"", {}, Or.inl rfl, proof_sqliteraw_openDb_rejectsInvalidPathAndConfigWithoutCallingC "" {} (Or.inl rfl)⟩

/-- Proof of `test_sqliteraw_openDb_computesExactOpenFlagsAndSetupOrder` for `Internal.mkRawOps`. -/
theorem proof_sqliteraw_openDb_computesExactOpenFlagsAndSetupOrder :
    AllPass (test_sqliteraw_openDb_computesExactOpenFlagsAndSetupOrder Internal.mkRawOps) := by
  intro path cfg h1 h2 h3
  rcases h1 with ⟨hNeEmpty, hNoNul⟩
  rcases h2 with ⟨hNotMemStr, hNotFile⟩
  rcases h3 with ⟨hNotCombo, hTimeout⟩
  have hNotNil : path.toUTF8.data.toList ≠ [] :=
    fun hNil => hNeEmpty ((toUTF8_data_toList_eq_nil_iff path).mp hNil)
  have hIsEmptyFalse : path.toUTF8.data.toList.isEmpty = false := by
    cases hList : path.toUTF8.data.toList with
    | nil => exact absurd hList hNotNil
    | cons _ _ => rfl
  have hHasZeroFalse : Internal.hasZeroByte path.toUTF8.data.toList = false := by
    cases hz : Internal.hasZeroByte path.toUTF8.data.toList
    · rfl
    · exact absurd ((hasZeroByte_toUTF8_iff path).mp hz) hNoNul
  have hNotComboFalse : (cfg.readOnly && cfg.createIfMissing) = false := by
    cases hc : cfg.readOnly && cfg.createIfMissing
    · rfl
    · simp [hc] at hNotCombo
  have hNotGt : ¬ (cfg.busyTimeoutMs > maxBusyTimeoutMs) := Nat.not_lt.mpr hTimeout
  have hTake5 : path.toUTF8.data.toList.take 5 ≠ [0x66, 0x69, 0x6C, 0x65, 0x3A] := by
    intro heq
    have hf : "file:".toUTF8.data.toList = [0x66, 0x69, 0x6C, 0x65, 0x3A] := by decide
    have heq' : path.toUTF8.data.toList.take 5 = "file:".toUTF8.data.toList := heq.trans hf.symm
    exact absurd heq' (by simpa [bne_iff_ne] using hNotFile)
  have hStripNone : Internal.stripFileScheme path.toUTF8.data.toList = none :=
    stripFileScheme_eq_none_of_take5 _ hTake5
  have hNotMem : (path.toUTF8.data.toList == Internal.colonMemoryColonBytes) = false := by
    cases hm : path.toUTF8.data.toList == Internal.colonMemoryColonBytes
    · rfl
    · exfalso
      have hEq : path.toUTF8.data.toList = Internal.colonMemoryColonBytes := beq_iff_eq.mp hm
      have hCol : Internal.colonMemoryColonBytes = ":memory:".toUTF8.data.toList := by decide
      have hMemEq : path.toUTF8 = ":memory:".toUTF8 :=
        ByteArray.ext (Array.toList_inj.mp (hEq.trans hCol))
      exact absurd hMemEq (by simpa [bne_iff_ne] using hNotMemStr)
  dsimp only [test_sqliteraw_openDb_computesExactOpenFlagsAndSetupOrder,
    Internal.mkRawOps, Internal.setupConnection, Internal.shouldEnableWal, Internal.classifyPathBytes,
    Internal.runSetupPragma, Internal.stepPragmaLoop, Internal.computeOpenFlags,
    Internal.insertRawDb, mockCOps, mockPrepareSuccess, rawDbToken, rawStmtToken, assert]
  dsimp only [Bind.bind, StateT.bind, bind, Pure.pure, StateT.pure, pure,
    StateT.run, tryFinally', MonadFinally.tryFinally']
  simp only [hIsEmptyFalse, hHasZeroFalse, hNotComboFalse, Bool.false_eq_true, ↓reduceIte,
    hNotGt, hNotMem, hStripNone]
  cases cfg.readOnly <;> cases cfg.createIfMissing <;> cases cfg.foreignKeys <;> cases cfg.walMode <;>
    (simp [hasLiveRawStmt]; try decide)

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_openDb_computesExactOpenFlagsAndSetupOrder`. -/
theorem reach_sqliteraw_openDb_computesExactOpenFlagsAndSetupOrder :
    CanReach (test_sqliteraw_openDb_computesExactOpenFlagsAndSetupOrder Internal.mkRawOps) :=
  ⟨"app.db", {}, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    proof_sqliteraw_openDb_computesExactOpenFlagsAndSetupOrder "app.db" {}
      ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩⟩

end LeanSwe.Sqlite.Raw.Proofs
