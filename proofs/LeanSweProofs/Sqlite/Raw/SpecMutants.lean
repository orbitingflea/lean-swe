import Core.NondetTest
import Core.Assumptions
import LeanSwe.Sqlite.Raw.Types
import LeanSweProofs.Sqlite.Raw.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Sqlite.Raw`. -/

namespace LeanSwe.Sqlite.Raw

open Core (NondetTest)
open Core.NondetTest

private def stubClassifyCode (code : UInt32) : SqliteErrorKind :=
  match (code &&& 0xFF).toNat with
  | 5 | 6 => .busy
  | 14 => .notFound
  | 19 => .constraint
  | 21 => .misuse
  | 25 => .invalidInput
  | _ => .ioError

private def stubMapRawError : SqliteRawError → SqliteError
  | .cantOpen path? code _ =>
    { kind := .notFound, sqliteCode := some code, path := path?, message := "cantOpen" }
  | .busy code _ =>
    { kind := .busy, sqliteCode := some code, message := "busy" }
  | .constraint code _ =>
    { kind := .constraint, sqliteCode := some code, message := "constraint" }
  | .misuse code _ =>
    { kind := .misuse, sqliteCode := some code, message := "misuse" }
  | .invalidArgument _ =>
    { kind := .invalidInput, message := "invalidArgument" }
  | .ioFailure code _ =>
    { kind := .ioError, sqliteCode := some code, message := "ioFailure" }
  | .sqliteCodeError code _ =>
    { kind := stubClassifyCode code, sqliteCode := some code, message := "sqliteCodeError" }
  | .userError _ =>
    { kind := .ioError, message := "userError" }

private def stubRawOps : RawSqliteOps :=
  { mapRawError := stubMapRawError
    openDb := fun _ _ => pure (.error { kind := .ioError, message := "stub" })
    closeDb := fun _ => pure (.ok ())
    prepare := fun _ _ => pure (.error { kind := .ioError, message := "stub" })
    bind := fun _ _ => pure (.ok ())
    step := fun _ => pure (.ok .done)
    finalize := fun _ => pure (.ok ())
    activeDbCount := pure 0
    activeStmtCount := pure 0 }

private def stubBaseMkRaw (cops : CSqliteOpsM (StateM MockCState)) : RawSqliteOpsM (StateM MockCState) :=
  { mapRawError := stubMapRawError
    openDb := fun _ _ => pure (.error { kind := .ioError, message := "stub" })
    closeDb := fun db => do
      let rawDb? ← cops.modifyTable fun t =>
        ((t.dbs.find? fun p => p.1 == db.id).map Prod.snd, t)
      match rawDb? with
      | none => pure (.error { kind := .misuse, sqliteCode := some 21, message := "closed" })
      | some rawDb =>
        match ← cops.close rawDb with
        | .error e => pure (.error (stubMapRawError e))
        | .ok () =>
          cops.modifyTable fun t => ((), { t with dbs := t.dbs.filter fun p => p.1 != db.id })
          pure (.ok ())
    prepare := fun _ _ => pure (.error { kind := .ioError, message := "stub" })
    bind := fun _ _ => pure (.ok ())
    step := fun _ => pure (.ok .done)
    finalize := fun _ => pure (.ok ())
    activeDbCount := cops.modifyTable fun t => (t.dbs.length, t)
    activeStmtCount := cops.modifyTable fun t => (t.stmts.length, t) }

example : ¬ Core.AllPass
    (test_sqliteraw_mapRawError_returnsNonEmptyMessage
      { stubRawOps with mapRawError := fun _ => { kind := .ioError, message := "" } }) := by
  intro h
  have h0 := h (.userError "boom")
  simp [assert] at h0

example : ¬ Core.AllPass
    (test_sqliteraw_mapRawError_mapsKnownKinds
      { stubRawOps with mapRawError := fun _ => { kind := .ioError, message := "wrong" } }) := by
  intro h
  have h0 := h (.cantOpen (some "a.db") 14 "missing")
  simp [assert] at h0

example : ¬ Core.AllPass
    (test_sqliteraw_mapRawError_mapsKnownKinds
      { stubRawOps with
        mapRawError := fun
          | .sqliteCodeError code _ =>
            let k : SqliteErrorKind := if code.toNat == 5 then .busy else .ioError
            { kind := k, sqliteCode := some code, message := "unmasked" }
          | other => stubMapRawError other }) := by
  intro h
  have h0 := h (.sqliteCodeError 261 "SQLITE_BUSY_RECOVERY")
  simp [assert] at h0

example : ¬ Core.AllPass
    (test_sqliteraw_mapRawError_consistentAcrossBackends stubRawOps fun cops =>
      { stubBaseMkRaw cops with mapRawError := fun _ => { kind := .misuse, message := "diverged" } }) := by
  intro h
  have h0 := h (.userError "x")
  simp [stubRawOps, stubMapRawError, assert] at h0

example : ¬ Core.AllPass
    (test_sqliteraw_openDb_rejectsInvalidPathAndConfigWithoutCallingC fun cops =>
      { stubBaseMkRaw cops with
        openDb := fun path _ => do
          let _ ← cops.openV2 path sqliteOpenFullMutex
          pure (.error { kind := .invalidInput, message := "called openV2 on NUL path" }) }) := by
  intro h
  have h0 := h (String.ofList ['a', Char.ofNat 0]) {} (Or.inr (Or.inl (by decide)))
  dsimp only [test_sqliteraw_openDb_rejectsInvalidPathAndConfigWithoutCallingC,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  have hBad := h0.1.2.1
  injection hBad

example : ¬ Core.AllPass
    (test_sqliteraw_openDb_rejectsInvalidPathAndConfigWithoutCallingC fun cops =>
      { stubBaseMkRaw cops with
        openDb := fun _ _ => pure (.ok { id := 1 }) }) := by
  intro h
  have h0 := h "a.db" { readOnly := true, createIfMissing := true }
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  dsimp only [test_sqliteraw_openDb_rejectsInvalidPathAndConfigWithoutCallingC,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  rcases h0.1.1 with ⟨_, hEq, _⟩
  cases hEq

example : ¬ Core.AllPass
    (test_sqliteraw_openDb_computesExactOpenFlagsAndSetupOrder fun cops =>
      { stubBaseMkRaw cops with
        openDb := fun path _ => do
          let r ← cops.openV2 path (sqliteOpenFullMutex ||| sqliteOpenReadWrite ||| sqliteOpenCreate)
          match r with
          | .error e => pure (.error (stubMapRawError e))
          | .ok rawDb =>
            let id ← cops.modifyTable fun t =>
              (t.nextDbId, { t with nextDbId := t.nextDbId + 1, dbs := t.dbs ++ [(t.nextDbId, rawDb)] })
            pure (.ok { id := id }) }) := by
  intro h
  have h0 := h "app.db" { foreignKeys := false, walMode := false }
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  dsimp only [test_sqliteraw_openDb_computesExactOpenFlagsAndSetupOrder,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  have hBad := h0.1.2.1
  injection hBad with hHead _
  injection hHead with _ hFlags
  exact absurd hFlags (by decide)

example : ¬ Core.AllPass
    (test_sqliteraw_openDb_skipsWalOnMemoryAndReadOnlyTargets fun cops =>
      { stubBaseMkRaw cops with
        openDb := fun path _ => do
          let r ← cops.openV2 path (sqliteOpenFullMutex ||| sqliteOpenUri ||| sqliteOpenReadWrite ||| sqliteOpenCreate)
          match r with
          | .error e => pure (.error (stubMapRawError e))
          | .ok rawDb =>
            if path.toUTF8 != ":memory:".toUTF8 then
              let p ← cops.prepareV2 rawDb "PRAGMA journal_mode = WAL;"
              if let .ok (some st, _) := p then
                let _ ← cops.finalize st
            let id ← cops.modifyTable fun t =>
              (t.nextDbId, { t with nextDbId := t.nextDbId + 1, dbs := t.dbs ++ [(t.nextDbId, rawDb)] })
            pure (.ok { id := id }) }) := by
  intro h
  have h0 := h "mem" ⟨by decide, by decide, by decide⟩ (by decide)
  dsimp only [test_sqliteraw_openDb_skipsWalOnMemoryAndReadOnlyTargets,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  exact absurd h0.1.2 (by decide)

example : ¬ Core.AllPass
    (test_sqliteraw_openDb_skipsWalOnMemoryAndReadOnlyTargets fun cops =>
      { stubBaseMkRaw cops with
        openDb := fun path _ => do
          let r ← cops.openV2 path (sqliteOpenFullMutex ||| sqliteOpenUri ||| sqliteOpenReadWrite ||| sqliteOpenCreate)
          match r with
          | .error e => pure (.error (stubMapRawError e))
          | .ok rawDb =>
            if path.toUTF8 == "file:mem.db?mode=%6Demory".toUTF8 then
              let p ← cops.prepareV2 rawDb "PRAGMA journal_mode = WAL;"
              if let .ok (some st, _) := p then
                let _ ← cops.finalize st
            let id ← cops.modifyTable fun t =>
              (t.nextDbId, { t with nextDbId := t.nextDbId + 1, dbs := t.dbs ++ [(t.nextDbId, rawDb)] })
            pure (.ok { id := id }) }) := by
  intro h
  have h0 := h "mem" ⟨by decide, by decide, by decide⟩ (by decide)
  dsimp only [test_sqliteraw_openDb_skipsWalOnMemoryAndReadOnlyTargets,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  have hPctHi := h0.2.2.2.2.2.1.2
  exact absurd hPctHi (by decide)

example : ¬ Core.AllPass
    (test_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets fun cops =>
      { stubBaseMkRaw cops with
        openDb := fun path _ => do
          let r ← cops.openV2 path (sqliteOpenFullMutex ||| sqliteOpenUri ||| sqliteOpenReadWrite ||| sqliteOpenCreate)
          match r with
          | .error e => pure (.error (stubMapRawError e))
          | .ok rawDb =>
            let id ← cops.modifyTable fun t =>
              (t.nextDbId, { t with nextDbId := t.nextDbId + 1, dbs := t.dbs ++ [(t.nextDbId, rawDb)] })
            pure (.ok { id := id }) }) := by
  intro h
  dsimp only [test_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets,
    Bind.bind, Pure.pure, StateT.run, assert] at h
  have hAuthSlash := h.2.2.2.2.2.1.2
  exact absurd hAuthSlash (by decide)

example : ¬ Core.AllPass
    (test_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets fun cops =>
      { stubBaseMkRaw cops with
        openDb := fun path _ => do
          let r ← cops.openV2 path (sqliteOpenFullMutex ||| sqliteOpenUri ||| sqliteOpenReadWrite ||| sqliteOpenCreate)
          match r with
          | .error e => pure (.error (stubMapRawError e))
          | .ok rawDb =>
            let p ← cops.prepareV2 rawDb "PRAGMA journal_mode = WAL;"
            if let .ok (some st, _) := p then
              let _ ← cops.finalize st
            let id ← cops.modifyTable fun t =>
              (t.nextDbId, { t with nextDbId := t.nextDbId + 1, dbs := t.dbs ++ [(t.nextDbId, rawDb)] })
            pure (.ok { id := id }) }) := by
  intro h
  dsimp only [test_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets,
    Bind.bind, Pure.pure, StateT.run, assert] at h
  have hNulFile := h.1.2
  exact absurd hNulFile (by decide)

example : ¬ Core.AllPass
    (test_sqliteraw_openDb_closesHandleOnAnySetupFailure fun cops =>
      { stubBaseMkRaw cops with
        openDb := fun path _ => do
          match ← cops.openV2 path sqliteOpenFullMutex with
          | .error e =>
            let e' := match e with
              | .cantOpen none c d => .cantOpen (some path) c d
              | other => other
            pure (.error (stubMapRawError e'))
          | .ok rawDb =>
            match ← cops.extendedResultCodes rawDb true with
            | .error e => pure (.error (stubMapRawError e))
            | .ok () => pure (.ok { id := 1 }) }) := by
  intro h
  have h0 := h 5 "locked"
  dsimp only [test_sqliteraw_openDb_closesHandleOnAnySetupFailure,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  have hLeak := h0.2.1.2.1
  injection hLeak

example : ¬ Core.AllPass
    (test_sqliteraw_openClose_preservesActiveDbCountAndRejectsClosedOrBusy fun cops =>
      { stubBaseMkRaw cops with
        openDb := fun path _ => do
          match ← cops.openV2 path sqliteOpenFullMutex with
          | .error e => pure (.error (stubMapRawError e))
          | .ok rawDb =>
            let id ← cops.modifyTable fun t =>
              (t.nextDbId, { t with nextDbId := t.nextDbId + 1, dbs := t.dbs ++ [(t.nextDbId, rawDb)] })
            pure (.ok { id := id })
        closeDb := fun db => do
          cops.modifyTable fun t => ((), { t with dbs := t.dbs.filter fun p => p.1 != db.id })
          pure (.ok ()) }) := by
  intro h
  have h0 := h 99 ⟨by decide, by decide⟩
  dsimp only [test_sqliteraw_openClose_preservesActiveDbCountAndRejectsClosedOrBusy,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  rcases h0.2.1.1 with ⟨_, hErr, _⟩
  cases hErr

example : ¬ Core.AllPass
    (test_sqliteraw_prepare_rejectsNulClosedDbAndEmptySql fun cops =>
      { stubBaseMkRaw cops with
        prepare := fun _ sql => do
          let _ ← cops.prepareV2 (.mock 100) sql
          pure (.error { kind := .invalidInput, message := "called C on NUL" }) }) := by
  intro h
  have h0 := h "SELECT " "1" 99 (by decide)
  dsimp only [test_sqliteraw_prepare_rejectsNulClosedDbAndEmptySql,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  have hCalls := h0.1.2.1
  injection hCalls

example : ¬ Core.AllPass
    (test_sqliteraw_prepare_acceptsCommentsAndWhitespaceInTail fun cops =>
      { stubBaseMkRaw cops with
        prepare := fun _ sql => do
          match ← cops.prepareV2 (.mock 100) sql with
          | .error e => pure (.error (stubMapRawError e))
          | .ok (none, _) => pure (.error { kind := .misuse, message := "empty" })
          | .ok (some rawStmt, consumed) =>
            let tail := sql.toUTF8.data.toList.drop consumed
            if tail.all (fun b => b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D) then
              let sh ← cops.modifyTable fun t =>
                let sh : StmtHandle := { id := t.nextStmtId, dbId := 1 }
                (sh, { t with nextStmtId := t.nextStmtId + 1, stmts := t.stmts ++ [(sh, rawStmt)] })
              pure (.ok sh)
            else
              let _ ← cops.finalize rawStmt
              pure (.error { kind := .misuse, message := "rejected comment in tail" }) }) := by
  intro h
  have h0 := h " ok" " ok " ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
  dsimp only [test_sqliteraw_prepare_acceptsCommentsAndWhitespaceInTail,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  cases h0.1.1

example : ¬ Core.AllPass
    (test_sqliteraw_prepare_rejectsMultiStmtAndUnclosedBlockCommentAndFinalizes fun cops =>
      { stubBaseMkRaw cops with
        prepare := fun _ sql => do
          match ← cops.prepareV2 (.mock 100) sql with
          | .error e => pure (.error (stubMapRawError e))
          | .ok (none, _) => pure (.error { kind := .misuse, message := "empty" })
          | .ok (some rawStmt, _) =>
            let sh ← cops.modifyTable fun t =>
              let sh : StmtHandle := { id := t.nextStmtId, dbId := 1 }
              (sh, { t with nextStmtId := t.nextStmtId + 1, stmts := t.stmts ++ [(sh, rawStmt)] })
            pure (.ok sh) }) := by
  intro h
  have h0 := h " unclosed" ⟨by decide, by decide, by decide⟩
  dsimp only [test_sqliteraw_prepare_rejectsMultiStmtAndUnclosedBlockCommentAndFinalizes,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  rcases h0.1.1 with ⟨_, hErr, _⟩
  cases hErr

example : ¬ Core.AllPass
    (test_sqliteraw_prepare_rejectsMultiStmtAndUnclosedBlockCommentAndFinalizes fun cops =>
      { stubBaseMkRaw cops with
        prepare := fun _ sql => do
          match ← cops.prepareV2 (.mock 100) sql with
          | .error e => pure (.error (stubMapRawError e))
          | .ok _ =>
            pure (.error { kind := .misuse, message := "forgot to finalize rawStmt" }) }) := by
  intro h
  have h0 := h " unclosed" ⟨by decide, by decide, by decide⟩
  dsimp only [test_sqliteraw_prepare_rejectsMultiStmtAndUnclosedBlockCommentAndFinalizes,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  have hLeak := h0.1.2.1
  injection hLeak

example : ¬ Core.AllPass
    (test_sqliteraw_bind_resetsValidatesCountAndBindsAllFiveTypes fun cops =>
      { stubBaseMkRaw cops with
        bind := fun stmt params => do
          let rawStmt? ← cops.modifyTable fun t =>
            ((t.stmts.find? fun p => p.1 == stmt).map Prod.snd, t)
          match rawStmt? with
          | none => pure (.error { kind := .misuse, message := "unknown" })
          | some rawStmt =>
            match ← cops.bindParamCount rawStmt with
            | .error e => pure (.error (stubMapRawError e))
            | .ok cnt =>
              if params.size != cnt.toNat then
                pure (.error { kind := .invalidInput, message := "mismatch" })
              else
                pure (.ok ()) }) := by
  intro h
  have h0 := h 1 1.0 "a" ByteArray.empty
  dsimp only [test_sqliteraw_bind_resetsValidatesCountAndBindsAllFiveTypes,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  have hCalls := h0.2.1.2
  injection hCalls with hHead _
  cases hHead

example : ¬ Core.AllPass
    (test_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors fun cops =>
      { stubBaseMkRaw cops with
        step := fun stmt => do
          let rawStmt? ← cops.modifyTable fun t =>
            ((t.stmts.find? fun p => p.1 == stmt).map Prod.snd, t)
          match rawStmt? with
          | none => pure (.error { kind := .misuse, message := "unknown" })
          | some rawStmt =>
            match ← cops.step rawStmt with
            | .error e => pure (.error (stubMapRawError e))
            | .ok .done => pure (.ok .done)
            | .ok .row =>
              pure (.ok (.row #[.text "lossy-fabricated"])) }) := by
  intro h
  have h0 := h 42 3.5 "ok" (ByteArray.mk #[0xFF, 0xFE]) rfl
  dsimp only [test_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  rcases h0.2.2.2.1 with ⟨_, hErr, _⟩
  cases hErr

example : ¬ Core.AllPass
    (test_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors fun cops =>
      { stubBaseMkRaw cops with
        step := fun stmt => do
          let rawStmt? ← cops.modifyTable fun t =>
            ((t.stmts.find? fun p => p.1 == stmt).map Prod.snd, t)
          match rawStmt? with
          | none => pure (.error { kind := .misuse, message := "unknown" })
          | some rawStmt =>
            match ← cops.step rawStmt with
            | .error e => pure (.error (stubMapRawError e))
            | .ok .done => pure (.ok .done)
            | .ok .row =>
              match ← cops.columnCount rawStmt with
              | .error _ => pure (.ok (.row #[]))
              | .ok _ => pure (.error { kind := .ioError, message := "err" }) }) := by
  intro h
  have h0 := h 42 3.5 "ok" (ByteArray.mk #[0xFF, 0xFE]) rfl
  dsimp only [test_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  rcases h0.2.2.2.2.1 with ⟨_, hErr, _⟩
  cases hErr

example : ¬ Core.AllPass
    (test_sqliteraw_finalize_releasesStmtEvenOnStickyErrorAndRejectsDoubleFinalize fun cops =>
      { stubBaseMkRaw cops with
        finalize := fun stmt => do
          let rawStmt? ← cops.modifyTable fun t =>
            ((t.stmts.find? fun p => p.1 == stmt).map Prod.snd, t)
          match rawStmt? with
          | none => pure (.error { kind := .misuse, message := "unknown" })
          | some rawStmt =>
            match ← cops.finalize rawStmt with
            | .finalized none =>
              cops.modifyTable fun t => ((), { t with stmts := t.stmts.filter fun p => p.1 != stmt })
              pure (.ok ())
            | .finalized (some stickyErr) =>
              pure (.error (stubMapRawError stickyErr))
            | .rejected err =>
              pure (.error (stubMapRawError err)) }) := by
  intro h
  have h0 := h 19 "UNIQUE failed"
  dsimp only [test_sqliteraw_finalize_releasesStmtEvenOnStickyErrorAndRejectsDoubleFinalize,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  have hCnt := h0.2.1.2.2.1
  cases hCnt

example : ¬ Core.AllPass
    (test_sqliteraw_openDb_computesExactOpenFlagsAndSetupOrder fun cops =>
      { stubBaseMkRaw cops with
        openDb := fun path cfg => do
          let flags : UInt32 :=
            sqliteOpenFullMutex ||| sqliteOpenUri |||
              (if cfg.readOnly then sqliteOpenReadOnly
               else if cfg.createIfMissing then sqliteOpenReadWrite ||| sqliteOpenCreate
               else sqliteOpenReadWrite)
          match ← cops.openV2 path flags with
          | .error e => pure (.error (stubMapRawError e))
          | .ok rawDb =>
            let _ ← cops.extendedResultCodes rawDb true
            let _ ← cops.busyTimeout rawDb (UInt32.ofNat cfg.busyTimeoutMs)
            if !cfg.readOnly && cfg.walMode then
              match ← cops.prepareV2 rawDb "PRAGMA journal_mode = WAL;" with
              | .ok (some st, _) =>
                let _ ← cops.step st
                let _ ← cops.finalize st
              | _ => pure ()
            let id ← cops.modifyTable fun t =>
              (t.nextDbId, { t with nextDbId := t.nextDbId + 1, dbs := t.dbs ++ [(t.nextDbId, rawDb)] })
            pure (.ok { id := id }) }) := by
  intro h
  have h0 := h "app.db" { foreignKeys := false, walMode := true }
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  dsimp only [test_sqliteraw_openDb_computesExactOpenFlagsAndSetupOrder,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  have hCalls := h0.1.2.1
  injection hCalls with _ t1
  injection t1 with _ t2
  injection t2 with _ t3
  injection t3 with _ t4
  injection t4 with _ t5
  injection t5 with hWrong _
  cases hWrong

example : ¬ Core.AllPass
    (test_sqliteraw_prepare_rejectsMultiStmtAndUnclosedBlockCommentAndFinalizes fun cops =>
      { stubBaseMkRaw cops with
        prepare := fun _ sql => do
          match ← cops.prepareV2 (.mock 100) sql with
          | .error e => pure (.error (stubMapRawError e))
          | .ok (none, _) => pure (.error { kind := .misuse, message := "empty" })
          | .ok (some rawStmt, _) =>
            if sql.toUTF8 == "SELECT 1; /*/".toUTF8 then
              let sh ← cops.modifyTable fun t =>
                let sh : StmtHandle := { id := t.nextStmtId, dbId := 1 }
                (sh, { t with nextStmtId := t.nextStmtId + 1, stmts := t.stmts ++ [(sh, rawStmt)] })
              pure (.ok sh)
            else
              let _ ← cops.finalize rawStmt
              pure (.error { kind := .misuse, message := "rejected" }) }) := by
  intro h
  have h0 := h " unclosed" ⟨by decide, by decide, by decide⟩
  dsimp only [test_sqliteraw_prepare_rejectsMultiStmtAndUnclosedBlockCommentAndFinalizes,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  rcases h0.2.1.1 with ⟨_, hErr, _⟩
  cases hErr

example : ¬ Core.AllPass
    (test_sqliteraw_bind_resetsValidatesCountAndBindsAllFiveTypes fun cops =>
      { stubBaseMkRaw cops with
        bind := fun stmt params => do
          let rawStmt? ← cops.modifyTable fun t =>
            ((t.stmts.find? fun p => p.1 == stmt).map Prod.snd, t)
          match rawStmt? with
          | none => pure (.error { kind := .misuse, message := "unknown" })
          | some rawStmt =>
            let _ ← cops.reset rawStmt
            let _ ← cops.clearBindings rawStmt
            match ← cops.bindParamCount rawStmt with
            | .error e => pure (.error (stubMapRawError e))
            | .ok cnt =>
              if params.size != cnt.toNat then
                pure (.error { kind := .invalidInput, message := "mismatch" })
              else
                let _ ← cops.bindNull rawStmt 0
                pure (.ok ()) }) := by
  intro h
  have h0 := h 1 1.0 "a" ByteArray.empty
  dsimp only [test_sqliteraw_bind_resetsValidatesCountAndBindsAllFiveTypes,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  have hCalls := h0.2.2.1.2
  injection hCalls with _ t1
  injection t1 with _ t2
  injection t2 with _ t3
  injection t3 with hIdx _
  injection hIdx with _ hZero
  exact absurd hZero (by decide)

example : ¬ Core.AllPass
    (test_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors fun cops =>
      { stubBaseMkRaw cops with
        step := fun stmt => do
          let rawStmt? ← cops.modifyTable fun t =>
            ((t.stmts.find? fun p => p.1 == stmt).map Prod.snd, t)
          match rawStmt? with
          | none => pure (.error { kind := .misuse, message := "unknown" })
          | some rawStmt =>
            match ← cops.step rawStmt with
            | .error e => pure (.error (stubMapRawError e))
            | .ok .done => pure (.ok .done)
            | .ok .row =>
              pure (.error { kind := .ioError, message := "rejected valid row or blob" }) }) := by
  intro h
  have h0 := h 42 3.5 "ok" (ByteArray.mk #[0xFF, 0xFE]) rfl
  dsimp only [test_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  cases h0.2.2.1.1

example : ¬ Core.AllPass
    (test_sqliteraw_finalize_releasesStmtEvenOnStickyErrorAndRejectsDoubleFinalize fun cops =>
      { stubBaseMkRaw cops with
        finalize := fun stmt => do
          let rawStmt? ← cops.modifyTable fun t =>
            ((t.stmts.find? fun p => p.1 == stmt).map Prod.snd, t)
          match rawStmt? with
          | none => pure (.error { kind := .misuse, message := "unknown" })
          | some rawStmt =>
            cops.modifyTable fun t => ((), { t with stmts := t.stmts.filter fun p => p.1 != stmt })
            match ← cops.finalize rawStmt with
            | .finalized none => pure (.ok ())
            | .finalized (some stickyErr) => pure (.error (stubMapRawError stickyErr))
            | .rejected err => pure (.error (stubMapRawError err)) }) := by
  intro h
  have h0 := h 5 "busy"
  dsimp only [test_sqliteraw_finalize_releasesStmtEvenOnStickyErrorAndRejectsDoubleFinalize,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  have hRejCnt := h0.2.2.1.2.2
  cases hRejCnt

example : ¬ Core.AllPass
    (test_sqliteraw_openClose_preservesActiveDbCountAndRejectsClosedOrBusy fun cops =>
      { stubBaseMkRaw cops with
        openDb := fun path _ => do
          match ← cops.openV2 path sqliteOpenFullMutex with
          | .error e => pure (.error (stubMapRawError e))
          | .ok rawDb =>
            let id ← cops.modifyTable fun t =>
              (t.nextDbId, { t with nextDbId := t.nextDbId + 1, dbs := t.dbs ++ [(t.nextDbId, rawDb)] })
            pure (.ok { id := id })
        prepare := fun db sql => do
          let rawDb? ← cops.modifyTable fun t =>
            ((t.dbs.find? fun p => p.1 == db.id).map Prod.snd, t)
          match rawDb? with
          | none => pure (.error { kind := .misuse, message := "closed" })
          | some rawDb =>
            match ← cops.prepareV2 rawDb sql with
            | .ok (some rawStmt, _) =>
              let sh ← cops.modifyTable fun t =>
                let sh : StmtHandle := { id := t.nextStmtId, dbId := db.id }
                (sh, { t with nextStmtId := t.nextStmtId + 1, stmts := t.stmts ++ [(sh, rawStmt)] })
              pure (.ok sh)
            | _ => pure (.error { kind := .misuse, message := "empty" }) }) := by
  intro h
  have h0 := h 99 ⟨by decide, by decide⟩
  dsimp only [test_sqliteraw_openClose_preservesActiveDbCountAndRejectsClosedOrBusy,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  have hCalledC := h0.2.2.2.1.2.1
  injection hCalledC

example : ¬ Core.AllPass
    (test_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors fun cops =>
      { stubBaseMkRaw cops with
        step := fun stmt => do
          let rawStmt? ← cops.modifyTable fun t =>
            ((t.stmts.find? fun p => p.1 == stmt).map Prod.snd, t)
          match rawStmt? with
          | none => pure (.error { kind := .misuse, message := "unknown" })
          | some rawStmt =>
            match ← cops.step rawStmt with
            | .error e => pure (.error (stubMapRawError e))
            | .ok .done => pure (.ok .done)
            | .ok .row =>
              match ← cops.columnCount rawStmt with
              | .error e => pure (.error (stubMapRawError e))
              | .ok cnt =>
                if cnt == 1 then
                  pure (.error { kind := .ioError, sqliteCode := some 11, message := "fabricated code" })
                else
                  pure (.error { kind := .misuse, message := "other" }) }) := by
  intro h
  have h0 := h 42 3.5 "ok" (ByteArray.mk #[0xFF, 0xFE]) rfl
  dsimp only [test_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  rcases h0.2.2.2.1 with ⟨e, hEq, _, hCode, _⟩
  injection hEq with hE
  rw [← hE] at hCode
  cases hCode

example : ¬ Core.AllPass
    (test_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors fun cops =>
      { stubBaseMkRaw cops with
        step := fun stmt => do
          let rawStmt? ← cops.modifyTable fun t =>
            ((t.stmts.find? fun p => p.1 == stmt).map Prod.snd, t)
          match rawStmt? with
          | none => pure (.error { kind := .misuse, message := "unknown" })
          | some rawStmt =>
            match ← cops.step rawStmt with
            | .error e => pure (.error (stubMapRawError e))
            | .ok .done => pure (.ok .done)
            | .ok .row =>
              let _ ← cops.columnBlob rawStmt 3
              let _ ← cops.columnBlob rawStmt 4
              pure (.ok (.row #[.null, .int 42, .real 3.5, .text "ok", .bytes (ByteArray.mk #[0xFF, 0xFE])])) }) := by
  intro h
  have h0 := h 42 3.5 "ok" (ByteArray.mk #[0xFF, 0xFE]) rfl
  dsimp only [test_sqliteraw_step_decodesColumnsValidatesUtf8AndPropagatesColumnErrors,
    Bind.bind, Pure.pure, StateT.run, assert] at h0
  have hHasTextCall := h0.2.2.1.2.1
  exact absurd hHasTextCall (by decide)

end LeanSwe.Sqlite.Raw
