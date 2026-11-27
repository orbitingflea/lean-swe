import LeanSweProofs.Sqlite.Raw.Model.Refines

namespace LeanSwe.Sqlite.Raw.Proofs

open LeanSwe.Sqlite.Raw

private def PreservesLocks {α : Type} (m : StateM Model.SqliteRawState α) : Prop :=
  ∀ s : Model.SqliteRawState, (m.run s).2.heldStmtLocks = s.heldStmtLocks

private theorem PreservesLocks.pure {α : Type} (x : α) : PreservesLocks (Pure.pure x) :=
  fun _ => rfl

private theorem PreservesLocks.bind {α β : Type} {ma : StateM Model.SqliteRawState α}
    {k : α → StateM Model.SqliteRawState β}
    (hma : PreservesLocks ma) (hk : ∀ a, PreservesLocks (k a)) :
    PreservesLocks (ma >>= k) :=
  fun s => (hk (ma.run s).1 (ma.run s).2).trans (hma s)

private theorem PreservesLocks.map {α β : Type} (f : α → β)
    {ma : StateM Model.SqliteRawState α} (hma : PreservesLocks ma) :
    PreservesLocks (f <$> ma) :=
  hma

private theorem PreservesLocks.tryFinally' {α β : Type} {ma : StateM Model.SqliteRawState α}
    {fin : Option α → StateM Model.SqliteRawState β}
    (hma : PreservesLocks ma) (hfin : ∀ o, PreservesLocks (fin o)) :
    PreservesLocks (tryFinally' ma fin) :=
  PreservesLocks.bind hma (fun a =>
    PreservesLocks.bind (hfin (some a)) (fun b => PreservesLocks.pure (a, b)))

private theorem preservesLocks_modifyTable {α : Type}
    (f : RawHandleTable → α × RawHandleTable) :
    PreservesLocks (Model.modelCSqliteOps.modifyTable f) :=
  fun _ => rfl

private theorem preservesLocks_openV2 (path : String) (flags : UInt32) :
    PreservesLocks (Model.modelCSqliteOps.openV2 path flags) :=
  fun _ => rfl

private theorem preservesLocks_close (rawDb : RawDbHandle) :
    PreservesLocks (Model.modelCSqliteOps.close rawDb) := by
  intro s
  dsimp only [Model.modelCSqliteOps, StateT.run]
  split
  · rfl
  · split <;> rfl

private theorem preservesLocks_extendedResultCodes (rawDb : RawDbHandle) (onoff : Bool) :
    PreservesLocks (Model.modelCSqliteOps.extendedResultCodes rawDb onoff) := by
  intro s
  dsimp only [Model.modelCSqliteOps, StateT.run]
  split <;> rfl

private theorem preservesLocks_busyTimeout (rawDb : RawDbHandle) (ms : UInt32) :
    PreservesLocks (Model.modelCSqliteOps.busyTimeout rawDb ms) := by
  intro s
  dsimp only [Model.modelCSqliteOps, StateT.run]
  split <;> rfl

private theorem preservesLocks_prepareV2 (rawDb : RawDbHandle) (sql : String) :
    PreservesLocks (Model.modelCSqliteOps.prepareV2 rawDb sql) := by
  intro s
  dsimp only [Model.modelCSqliteOps, StateT.run]
  split
  · rfl
  · split <;> rfl

private theorem preservesLocks_step (rawStmt : RawStmtHandle) :
    PreservesLocks (Model.modelCSqliteOps.step rawStmt) := by
  intro s
  dsimp only [Model.modelCSqliteOps, StateT.run]
  split
  · rfl
  · cases s.stepQueue <;> rfl

private theorem preservesLocks_reset (rawStmt : RawStmtHandle) :
    PreservesLocks (Model.modelCSqliteOps.reset rawStmt) := by
  intro s
  dsimp only [Model.modelCSqliteOps, StateT.run]
  split <;> rfl

private theorem preservesLocks_clearBindings (rawStmt : RawStmtHandle) :
    PreservesLocks (Model.modelCSqliteOps.clearBindings rawStmt) := by
  intro s
  dsimp only [Model.modelCSqliteOps, StateT.run]
  split <;> rfl

private theorem preservesLocks_finalize (rawStmt : RawStmtHandle) :
    PreservesLocks (Model.modelCSqliteOps.finalize rawStmt) := by
  intro s
  dsimp only [Model.modelCSqliteOps, StateT.run]
  split <;> rfl

private theorem preservesLocks_bindParamCount (rawStmt : RawStmtHandle) :
    PreservesLocks (Model.modelCSqliteOps.bindParamCount rawStmt) := by
  intro s
  dsimp only [Model.modelCSqliteOps, StateT.run]
  split <;> rfl

private theorem preservesLocks_bindOneParam (rawStmt : RawStmtHandle) (idx : UInt32)
    (val : SqliteValue) :
    PreservesLocks (Model.bindOneParamModel Model.modelCSqliteOps rawStmt idx val) := by
  intro s
  cases val <;> (dsimp only [Model.bindOneParamModel, Model.modelCSqliteOps, StateT.run]; split <;> rfl)

private theorem preservesLocks_columnCount (rawStmt : RawStmtHandle) :
    PreservesLocks (Model.modelCSqliteOps.columnCount rawStmt) := by
  intro s
  dsimp only [Model.modelCSqliteOps, StateT.run]
  split <;> rfl

private theorem preservesLocks_columnType (rawStmt : RawStmtHandle) (col : UInt32) :
    PreservesLocks (Model.modelCSqliteOps.columnType rawStmt col) := by
  intro s
  dsimp only [Model.modelCSqliteOps, StateT.run]
  split <;> rfl

private theorem preservesLocks_columnInt64 (rawStmt : RawStmtHandle) (col : UInt32) :
    PreservesLocks (Model.modelCSqliteOps.columnInt64 rawStmt col) := by
  intro s
  dsimp only [Model.modelCSqliteOps, StateT.run]
  split
  · rfl
  · cases s.columns[col.toNat]? with
    | none => rfl
    | some c => cases c <;> rfl

private theorem preservesLocks_columnDouble (rawStmt : RawStmtHandle) (col : UInt32) :
    PreservesLocks (Model.modelCSqliteOps.columnDouble rawStmt col) := by
  intro s
  dsimp only [Model.modelCSqliteOps, StateT.run]
  split
  · rfl
  · cases s.columns[col.toNat]? with
    | none => rfl
    | some c => cases c <;> rfl

private theorem preservesLocks_columnTextBytes (rawStmt : RawStmtHandle) (col : UInt32) :
    PreservesLocks (Model.modelCSqliteOps.columnTextBytes rawStmt col) := by
  intro s
  dsimp only [Model.modelCSqliteOps, StateT.run]
  split
  · rfl
  · cases s.columns[col.toNat]? with
    | none => rfl
    | some c => cases c <;> rfl

private theorem preservesLocks_columnBlob (rawStmt : RawStmtHandle) (col : UInt32) :
    PreservesLocks (Model.modelCSqliteOps.columnBlob rawStmt col) := by
  intro s
  dsimp only [Model.modelCSqliteOps, StateT.run]
  split
  · rfl
  · cases s.columns[col.toNat]? with
    | none => rfl
    | some c => cases c <;> rfl

private theorem preservesLocks_stepPragmaLoop (rawStmt : RawStmtHandle) (fuel : Nat) :
    PreservesLocks (Model.stepPragmaLoopModel Model.modelCSqliteOps rawStmt fuel) := by
  induction fuel with
  | zero => exact PreservesLocks.pure _
  | succ f ih =>
    unfold Model.stepPragmaLoopModel
    refine PreservesLocks.bind (preservesLocks_step rawStmt) ?_
    intro res
    cases res with
    | error _ => exact PreservesLocks.pure _
    | ok tag =>
      cases tag with
      | done => exact PreservesLocks.pure _
      | row => exact ih

private theorem preservesLocks_runSetupPragma (rawDb : RawDbHandle) (sql : String) :
    PreservesLocks (Model.runSetupPragmaModel Model.modelCSqliteOps rawDb sql) := by
  unfold Model.runSetupPragmaModel
  refine PreservesLocks.bind (preservesLocks_prepareV2 rawDb sql) ?_
  intro res
  cases res with
  | error _ => exact PreservesLocks.pure _
  | ok pair =>
    rcases pair with ⟨stmt?, _⟩
    cases stmt? with
    | none => exact PreservesLocks.pure _
    | some rawStmt =>
      refine PreservesLocks.bind
        (PreservesLocks.tryFinally' (preservesLocks_stepPragmaLoop rawStmt 4)
          (fun _ => preservesLocks_finalize rawStmt)) ?_
      intro sf
      rcases sf with ⟨stepRes, finOut⟩
      cases stepRes with
      | error _ => exact PreservesLocks.pure _
      | ok _ =>
        cases finOut with
        | finalized st? => cases st? <;> exact PreservesLocks.pure _
        | rejected _ => exact PreservesLocks.pure _

private theorem preservesLocks_setupConnection (path : String) (cfg : OpenConfig)
    (rawDb : RawDbHandle) :
    PreservesLocks (Model.setupConnectionModel Model.modelCSqliteOps path cfg rawDb) := by
  unfold Model.setupConnectionModel
  refine PreservesLocks.bind (preservesLocks_extendedResultCodes rawDb true) ?_
  intro r1
  cases r1 with
  | error _ => exact PreservesLocks.pure _
  | ok _ =>
    refine PreservesLocks.bind
      (preservesLocks_busyTimeout rawDb (UInt32.ofNat cfg.busyTimeoutMs)) ?_
    intro r2
    cases r2 with
    | error _ => exact PreservesLocks.pure _
    | ok _ =>
      cases cfg.foreignKeys with
      | false =>
        cases Model.shouldEnableWalModel path cfg with
        | false => exact PreservesLocks.pure _
        | true => exact preservesLocks_runSetupPragma rawDb "PRAGMA journal_mode = WAL;"
      | true =>
        refine PreservesLocks.bind (preservesLocks_runSetupPragma rawDb "PRAGMA foreign_keys = ON;") ?_
        intro fkRes
        cases fkRes with
        | error _ => exact PreservesLocks.pure _
        | ok _ =>
          cases Model.shouldEnableWalModel path cfg with
          | false => exact PreservesLocks.pure _
          | true => exact preservesLocks_runSetupPragma rawDb "PRAGMA journal_mode = WAL;"

private theorem preservesLocks_bindLoop (rawStmt : RawStmtHandle) (params : Array SqliteValue)
    (rem : Nat) :
    PreservesLocks (Model.bindLoopModel Model.modelCSqliteOps rawStmt params rem) := by
  induction rem with
  | zero => exact PreservesLocks.pure _
  | succ r ih =>
    unfold Model.bindLoopModel
    refine PreservesLocks.bind (preservesLocks_bindOneParam rawStmt _ _) ?_
    intro res
    cases res with
    | error _ => exact PreservesLocks.pure _
    | ok _ => exact ih

private theorem preservesLocks_decodeColumns (rawStmt : RawStmtHandle) (total rem : Nat)
    (acc : Array SqliteValue) :
    PreservesLocks (Model.decodeColumnsModel Model.modelCSqliteOps rawStmt total rem acc) := by
  induction rem generalizing acc with
  | zero => exact PreservesLocks.pure _
  | succ r ih =>
    unfold Model.decodeColumnsModel
    let colU := UInt32.ofNat (total - (r + 1))
    refine PreservesLocks.bind (preservesLocks_columnType rawStmt colU) ?_
    intro tyRes
    cases tyRes with
    | error _ => exact PreservesLocks.pure _
    | ok ty =>
      dsimp only
      rcases hTy : ty.toNat with _ | _ | _ | _ | _ | n
      · exact ih (acc.push .null)
      · refine PreservesLocks.bind (preservesLocks_columnInt64 rawStmt colU) ?_
        intro rInt
        cases rInt with
        | error _ => exact PreservesLocks.pure _
        | ok v => exact ih (acc.push (.int v))
      · refine PreservesLocks.bind (preservesLocks_columnDouble rawStmt colU) ?_
        intro rFlt
        cases rFlt with
        | error _ => exact PreservesLocks.pure _
        | ok d => exact ih (acc.push (.real d))
      · refine PreservesLocks.bind (preservesLocks_columnTextBytes rawStmt colU) ?_
        intro rTxt
        cases rTxt with
        | error _ => exact PreservesLocks.pure _
        | ok bs =>
          dsimp only
          cases String.fromUTF8? bs with
          | none => exact PreservesLocks.pure _
          | some s => exact ih (acc.push (.text s))
      · refine PreservesLocks.bind (preservesLocks_columnBlob rawStmt colU) ?_
        intro rBlb
        cases rBlb with
        | error _ => exact PreservesLocks.pure _
        | ok bs => exact ih (acc.push (.bytes bs))
      · exact ih (acc.push .null)

private theorem stmtHandle_beq_self (sh : StmtHandle) : (sh == sh) = true := by
  cases sh
  simp [BEq.beq, instBEqStmtHandle.beq]

private theorem stateM_bind_run {W α β : Type} (m : StateM W α) (k : α → StateM W β) (w : W) :
    (m >>= k).run w = (k (m.run w).1).run (m.run w).2 := rfl

private theorem stateM_pure_run {W α : Type} (a : α) (w : W) :
    (Pure.pure a : StateM W α).run w = (a, w) := rfl

private theorem stateM_tryFinally_run {W α β : Type} (m : StateM W α)
    (fin : Option α → StateM W β) (w : W) :
    (tryFinally' m fin).run w =
      (((m.run w).1, ((fin (some (m.run w).1)).run (m.run w).2).1),
        ((fin (some (m.run w).1)).run (m.run w).2).2) := rfl

private theorem map_run_snd {α β : Type} (f : α → β) (m : StateM Model.SqliteRawState α)
    (s : Model.SqliteRawState) :
    ((f <$> m).run s).2 = (m.run s).2 := rfl

private theorem withStmtLockModel_wf {α : Type} (stmt : StmtHandle)
    {act : StateM Model.SqliteRawState α} (hAct : PreservesLocks act)
    (s : Model.SqliteRawState) (hWf : Model.rawStepWf s = true) :
    Model.rawStepWf ((Model.withStmtLockModel Model.modelCSqliteOps stmt act).run s).2 = true := by
  have hNil : s.heldStmtLocks = [] := List.isEmpty_iff.mp hWf
  unfold Model.withStmtLockModel
  dsimp only [Model.rawStepWf]
  rw [stateM_bind_run]
  have hLock : (Model.modelCSqliteOps.lockStmt stmt).run s =
      if (Model.lookupRawStmtModel stmt s.table.stmts).isSome then
        (true, { s with heldStmtLocks := stmt :: s.heldStmtLocks })
      else
        (false, s) := rfl
  rw [hLock]
  cases (Model.lookupRawStmtModel stmt s.table.stmts).isSome with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, stateM_tryFinally_run]
    dsimp only
    rw [stateM_pure_run, stateM_pure_run]
    dsimp only
    rw [hAct s, hNil]
    rfl
  | true =>
    simp only [↓reduceIte]
    rw [stateM_bind_run, stateM_tryFinally_run]
    dsimp only
    have hUnlock (w : Model.SqliteRawState) :
        (Model.modelCSqliteOps.unlockStmt stmt).run w =
          ((), { w with heldStmtLocks := Model.eraseStmtLockModel stmt w.heldStmtLocks }) := rfl
    rw [hUnlock, stateM_pure_run]
    dsimp only
    rw [hAct { s with heldStmtLocks := stmt :: s.heldStmtLocks }]
    dsimp only
    rw [hNil]
    dsimp only [Model.eraseStmtLockModel]
    rw [stmtHandle_beq_self stmt]
    rfl

private theorem wf_of_preservesLocks {α : Type} {m : StateM Model.SqliteRawState α}
    (hm : PreservesLocks m) (s : Model.SqliteRawState) (hWf : Model.rawStepWf s = true) :
    Model.rawStepWf (m.run s).2 = true := by
  dsimp only [Model.rawStepWf] at hWf ⊢
  rw [hm s]
  exact hWf

/-- Every `Model.modelRawSqliteOps` step preserves `Model.rawStepWf` (`heldStmtLocks.isEmpty`). -/
theorem modelRawSqliteOps_preserves_wf (s : Model.SqliteRawState) (req : Model.RawStepReq)
    (hWf : Model.rawStepWf s = true) :
    Model.rawStepWf ((Model.execRawStep Model.modelRawSqliteOps req).run s).2 = true := by
  cases req with
  | mapRawError _ => exact hWf
  | openDb path cfg =>
    apply wf_of_preservesLocks _ s hWf
    apply PreservesLocks.map
    dsimp only [Model.modelRawSqliteOps, Model.mkRawOpsModel]
    split
    · exact PreservesLocks.pure _
    · split
      · exact PreservesLocks.pure _
      · split
        · exact PreservesLocks.pure _
        · split
          · exact PreservesLocks.pure _
          · refine PreservesLocks.bind
              (preservesLocks_openV2 path (Model.computeOpenFlagsModel cfg)) ?_
            intro openRes
            cases openRes with
            | error _ => exact PreservesLocks.pure _
            | ok rawDb =>
              refine PreservesLocks.bind
                (PreservesLocks.tryFinally' (preservesLocks_setupConnection path cfg rawDb) fun o => by
                  cases o with
                  | none =>
                    exact PreservesLocks.bind (preservesLocks_close rawDb)
                      (fun _ => PreservesLocks.pure ())
                  | some r =>
                    cases r with
                    | error _ =>
                      exact PreservesLocks.bind (preservesLocks_close rawDb)
                        (fun _ => PreservesLocks.pure ())
                    | ok u =>
                      cases u
                      exact PreservesLocks.pure ()) ?_
              intro pair
              rcases pair with ⟨setupRes, _⟩
              cases setupRes with
              | error _ => exact PreservesLocks.pure _
              | ok _ =>
                exact PreservesLocks.bind
                  (preservesLocks_modifyTable (Model.tableInsertDb rawDb))
                  (fun _ => PreservesLocks.pure _)
  | closeDb db =>
    apply wf_of_preservesLocks _ s hWf
    apply PreservesLocks.map
    dsimp only [Model.modelRawSqliteOps, Model.mkRawOpsModel]
    refine PreservesLocks.bind (preservesLocks_modifyTable (Model.tableCheckCloseDb db.id)) ?_
    intro chkRes
    cases chkRes with
    | error _ => exact PreservesLocks.pure _
    | ok rawDb =>
      refine PreservesLocks.bind (preservesLocks_close rawDb) ?_
      intro clsRes
      cases clsRes with
      | error _ => exact PreservesLocks.pure _
      | ok _ =>
        exact PreservesLocks.bind (preservesLocks_modifyTable (Model.tableEraseDb db.id))
          (fun _ => PreservesLocks.pure _)
  | prepare db sql =>
    apply wf_of_preservesLocks _ s hWf
    apply PreservesLocks.map
    dsimp only [Model.modelRawSqliteOps, Model.mkRawOpsModel]
    split
    · exact PreservesLocks.pure _
    · split
      · exact PreservesLocks.pure _
      · refine PreservesLocks.bind (preservesLocks_modifyTable (Model.tableLookupDb db.id)) ?_
        intro dbOpt
        cases dbOpt with
        | none => exact PreservesLocks.pure _
        | some rawDb =>
          refine PreservesLocks.bind (preservesLocks_prepareV2 rawDb sql) ?_
          intro prepRes
          cases prepRes with
          | error _ => exact PreservesLocks.pure _
          | ok pair =>
            rcases pair with ⟨stmt?, consumed⟩
            cases stmt? with
            | none => exact PreservesLocks.pure _
            | some rawStmt =>
              dsimp only
              cases (consumed ≤ sql.toUTF8.size &&
                  Model.scanSqlTailBaModel .normal sql.toUTF8 consumed) with
              | false =>
                exact PreservesLocks.bind (preservesLocks_finalize rawStmt)
                  (fun _ => PreservesLocks.pure _)
              | true =>
                exact PreservesLocks.bind
                  (preservesLocks_modifyTable (Model.tableInsertStmt db.id rawStmt))
                  (fun _ => PreservesLocks.pure _)
  | bind stmt params =>
    dsimp only [Model.execRawStep, Model.modelRawSqliteOps, Model.mkRawOpsModel]
    rw [map_run_snd]
    apply withStmtLockModel_wf stmt _ s hWf
    refine PreservesLocks.bind (preservesLocks_modifyTable (Model.tableLookupStmt stmt)) ?_
    intro stOpt
    cases stOpt with
    | none => exact PreservesLocks.pure _
    | some rawStmt =>
      refine PreservesLocks.bind (preservesLocks_reset rawStmt) ?_
      intro r1
      cases r1 with
      | error _ => exact PreservesLocks.pure _
      | ok _ =>
        refine PreservesLocks.bind (preservesLocks_clearBindings rawStmt) ?_
        intro r2
        cases r2 with
        | error _ => exact PreservesLocks.pure _
        | ok _ =>
          refine PreservesLocks.bind (preservesLocks_bindParamCount rawStmt) ?_
          intro r3
          cases r3 with
          | error _ => exact PreservesLocks.pure _
          | ok cnt =>
            dsimp only
            cases (params.size != cnt.toNat) with
            | true => exact PreservesLocks.pure _
            | false => exact preservesLocks_bindLoop rawStmt params params.size
  | step stmt =>
    dsimp only [Model.execRawStep, Model.modelRawSqliteOps, Model.mkRawOpsModel]
    rw [map_run_snd]
    apply withStmtLockModel_wf stmt _ s hWf
    refine PreservesLocks.bind (preservesLocks_modifyTable (Model.tableLookupStmt stmt)) ?_
    intro stOpt
    cases stOpt with
    | none => exact PreservesLocks.pure _
    | some rawStmt =>
      refine PreservesLocks.bind (preservesLocks_step rawStmt) ?_
      intro stRes
      cases stRes with
      | error _ => exact PreservesLocks.pure _
      | ok tag =>
        cases tag with
        | done => exact PreservesLocks.pure _
        | row =>
          refine PreservesLocks.bind (preservesLocks_columnCount rawStmt) ?_
          intro cntRes
          cases cntRes with
          | error _ => exact PreservesLocks.pure _
          | ok cnt =>
            refine PreservesLocks.bind (preservesLocks_decodeColumns rawStmt cnt.toNat cnt.toNat #[]) ?_
            intro colsRes
            cases colsRes <;> exact PreservesLocks.pure _
  | finalize stmt =>
    dsimp only [Model.execRawStep, Model.modelRawSqliteOps, Model.mkRawOpsModel]
    rw [map_run_snd]
    apply withStmtLockModel_wf stmt _ s hWf
    refine PreservesLocks.bind (preservesLocks_modifyTable (Model.tableLookupStmt stmt)) ?_
    intro stOpt
    cases stOpt with
    | none => exact PreservesLocks.pure _
    | some rawStmt =>
      refine PreservesLocks.bind (preservesLocks_finalize rawStmt) ?_
      intro finOut
      cases finOut with
      | finalized st? =>
        refine PreservesLocks.bind (preservesLocks_modifyTable (Model.tableEraseStmt stmt)) ?_
        intro _
        cases st? <;> exact PreservesLocks.pure _
      | rejected _ => exact PreservesLocks.pure _
  | activeDbCount =>
    exact wf_of_preservesLocks (preservesLocks_modifyTable Model.tableActiveDbCount) s hWf
  | activeStmtCount =>
    exact wf_of_preservesLocks (preservesLocks_modifyTable Model.tableActiveStmtCount) s hWf

end LeanSwe.Sqlite.Raw.Proofs
