import LeanSweProofs.Sqlite.Raw.Proofs.ObeysPureEquiv
import LeanSweProofs.Sqlite.Raw.Proofs.ObeysLocks

namespace LeanSwe.Sqlite.Raw.Proofs

open LeanSwe.Sqlite.Raw

private def Sim {W α : Type} (proj : W → Model.SqliteRawState)
    (mImpl : StateM W α) (mMod : StateM Model.SqliteRawState α) : Prop :=
  ∀ w : W,
    (mImpl.run w).1 = (mMod.run (proj w)).1 ∧
    proj (mImpl.run w).2 = (mMod.run (proj w)).2

private theorem Sim.pure {W α : Type} {proj : W → Model.SqliteRawState} (x : α) :
    Sim proj (Pure.pure x) (Pure.pure x) :=
  fun _ => ⟨rfl, rfl⟩

private theorem Sim.bind {W α β : Type} {proj : W → Model.SqliteRawState}
    {ma₁ : StateM W α} {ma₂ : StateM Model.SqliteRawState α}
    {k₁ : α → StateM W β} {k₂ : α → StateM Model.SqliteRawState β}
    (ha : Sim proj ma₁ ma₂) (hk : ∀ a, Sim proj (k₁ a) (k₂ a)) :
    Sim proj (ma₁ >>= k₁) (ma₂ >>= k₂) := by
  intro w
  rcases ha w with ⟨hVal, hSt⟩
  have hNext := hk (ma₁.run w).1 (ma₁.run w).2
  change ((k₁ (ma₁.run w).1).run (ma₁.run w).2).1 =
      ((k₂ (ma₂.run (proj w)).1).run (ma₂.run (proj w)).2).1 ∧
    proj ((k₁ (ma₁.run w).1).run (ma₁.run w).2).2 =
      ((k₂ (ma₂.run (proj w)).1).run (ma₂.run (proj w)).2).2
  rw [← hVal, ← hSt]
  exact hNext

private theorem Sim.map {W α β : Type} {proj : W → Model.SqliteRawState}
    (f : α → β) {ma₁ : StateM W α} {ma₂ : StateM Model.SqliteRawState α}
    (ha : Sim proj ma₁ ma₂) :
    Sim proj (f <$> ma₁) (f <$> ma₂) := by
  intro w
  rcases ha w with ⟨hVal, hSt⟩
  change f (ma₁.run w).1 = f (ma₂.run (proj w)).1 ∧
    proj (ma₁.run w).2 = (ma₂.run (proj w)).2
  rw [hVal, hSt]
  exact ⟨rfl, rfl⟩

private theorem Sim.tryFinally' {W α β : Type} {proj : W → Model.SqliteRawState}
    {ma₁ : StateM W α} {ma₂ : StateM Model.SqliteRawState α}
    {fin₁ : Option α → StateM W β} {fin₂ : Option α → StateM Model.SqliteRawState β}
    (ha : Sim proj ma₁ ma₂) (hf : ∀ o, Sim proj (fin₁ o) (fin₂ o)) :
    Sim proj (tryFinally' ma₁ fin₁) (tryFinally' ma₂ fin₂) :=
  Sim.bind ha (fun a => Sim.bind (hf (some a)) (fun b => Sim.pure (a, b)))

private theorem sim_of_cstep {W α : Type} {proj : W → Model.SqliteRawState}
    {cops : CSqliteOpsM (StateM W)}
    (hC : Core.ObeysStep proj Model.cStepWf (Model.execCStep cops) Model.allowedCStep)
    (req : Model.CStepReq) (wrap : α → Model.CStepOut)
    (hWrapInj : ∀ x y, wrap x = wrap y → x = y)
    {mImpl : StateM W α} {mMod : StateM Model.SqliteRawState α}
    (hImpl : Model.execCStep cops req = wrap <$> mImpl)
    (hMod : Model.execCStep Model.modelCSqliteOps req = wrap <$> mMod) :
    Sim proj mImpl mMod := by
  intro w
  have hStep := hC w req rfl
  dsimp only [Model.allowedCStep] at hStep
  rw [hImpl, hMod] at hStep
  have hMapImpl : ((wrap <$> mImpl).run w) = (wrap (mImpl.run w).1, (mImpl.run w).2) := rfl
  have hMapMod : ((wrap <$> mMod).run (proj w)) =
      (wrap (mMod.run (proj w)).1, (mMod.run (proj w)).2) := rfl
  rw [hMapImpl, hMapMod] at hStep
  exact ⟨hWrapInj _ _ hStep.1, hStep.2⟩

private theorem sim_unit_table {W : Type} {proj : W → Model.SqliteRawState}
    {cops : CSqliteOpsM (StateM W)}
    (hC : Core.ObeysStep proj Model.cStepWf (Model.execCStep cops) Model.allowedCStep)
    (req : Model.CStepReq)
    {mImpl : StateM W Unit} {mMod : StateM Model.SqliteRawState Unit}
    (hImpl : Model.execCStep cops req = (fun _ => Model.CStepOut.tableUnit) <$> mImpl)
    (hMod : Model.execCStep Model.modelCSqliteOps req =
      (fun _ => Model.CStepOut.tableUnit) <$> mMod) :
    Sim proj mImpl mMod := by
  intro w
  have hStep := hC w req rfl
  dsimp only [Model.allowedCStep] at hStep
  rw [hImpl, hMod] at hStep
  have hMapImpl : (((fun _ => Model.CStepOut.tableUnit) <$> mImpl).run w) =
      (Model.CStepOut.tableUnit, (mImpl.run w).2) := rfl
  have hMapMod : (((fun _ => Model.CStepOut.tableUnit) <$> mMod).run (proj w)) =
      (Model.CStepOut.tableUnit, (mMod.run (proj w)).2) := rfl
  rw [hMapImpl, hMapMod] at hStep
  exact ⟨Subsingleton.elim _ _, hStep.2⟩

private theorem sim_stepPragmaLoop {W : Type} {proj : W → Model.SqliteRawState}
    {cops : CSqliteOpsM (StateM W)}
    (hC : Core.ObeysStep proj Model.cStepWf (Model.execCStep cops) Model.allowedCStep)
    (rawStmt : RawStmtHandle) (fuel : Nat) :
    Sim proj (Model.stepPragmaLoopModel cops rawStmt fuel)
      (Model.stepPragmaLoopModel Model.modelCSqliteOps rawStmt fuel) := by
  induction fuel with
  | zero => exact Sim.pure _
  | succ f ih =>
    unfold Model.stepPragmaLoopModel
    refine Sim.bind
      (sim_of_cstep hC (.step rawStmt) Model.CStepOut.stepTagRes
        (fun _ _ h => Model.CStepOut.stepTagRes.inj h) rfl rfl) ?_
    intro res
    cases res with
    | error _ => exact Sim.pure _
    | ok tag =>
      cases tag with
      | done => exact Sim.pure _
      | row => exact ih

private theorem sim_runSetupPragma {W : Type} {proj : W → Model.SqliteRawState}
    {cops : CSqliteOpsM (StateM W)}
    (hC : Core.ObeysStep proj Model.cStepWf (Model.execCStep cops) Model.allowedCStep)
    (rawDb : RawDbHandle) (sql : String) :
    Sim proj (Model.runSetupPragmaModel cops rawDb sql)
      (Model.runSetupPragmaModel Model.modelCSqliteOps rawDb sql) := by
  unfold Model.runSetupPragmaModel
  refine Sim.bind
    (sim_of_cstep hC (.prepareV2 rawDb sql) Model.CStepOut.prepRes
      (fun _ _ h => Model.CStepOut.prepRes.inj h) rfl rfl) ?_
  intro res
  cases res with
  | error _ => exact Sim.pure _
  | ok pair =>
    rcases pair with ⟨stmt?, consumed⟩
    cases stmt? with
    | none => exact Sim.pure _
    | some rawStmt =>
      dsimp only
      refine Sim.bind
        (Sim.tryFinally' (sim_stepPragmaLoop hC rawStmt 4) fun _ =>
          sim_of_cstep hC (.finalize rawStmt) Model.CStepOut.finRes
            (fun _ _ h => Model.CStepOut.finRes.inj h) rfl rfl) ?_
      intro sf
      rcases sf with ⟨stepRes, finOut⟩
      cases stepRes with
      | error _ => exact Sim.pure _
      | ok _ =>
        cases finOut with
        | finalized st? => cases st? <;> exact Sim.pure _
        | rejected _ => exact Sim.pure _

private theorem sim_setupConnection {W : Type} {proj : W → Model.SqliteRawState}
    {cops : CSqliteOpsM (StateM W)}
    (hC : Core.ObeysStep proj Model.cStepWf (Model.execCStep cops) Model.allowedCStep)
    (path : String) (cfg : OpenConfig) (rawDb : RawDbHandle) :
    Sim proj (Model.setupConnectionModel cops path cfg rawDb)
      (Model.setupConnectionModel Model.modelCSqliteOps path cfg rawDb) := by
  unfold Model.setupConnectionModel
  refine Sim.bind
    (sim_of_cstep hC (.extendedResultCodes rawDb true) Model.CStepOut.unitRes
      (fun _ _ h => Model.CStepOut.unitRes.inj h) rfl rfl) ?_
  intro r1
  cases r1 with
  | error _ => exact Sim.pure _
  | ok _ =>
    dsimp only
    refine Sim.bind
      (sim_of_cstep hC (.busyTimeout rawDb (UInt32.ofNat cfg.busyTimeoutMs)) Model.CStepOut.unitRes
        (fun _ _ h => Model.CStepOut.unitRes.inj h) rfl rfl) ?_
    intro r2
    cases r2 with
    | error _ => exact Sim.pure _
    | ok _ =>
      dsimp only
      cases cfg.foreignKeys with
      | false =>
        cases Model.shouldEnableWalModel path cfg with
        | false => exact Sim.pure _
        | true => exact sim_runSetupPragma hC rawDb "PRAGMA journal_mode = WAL;"
      | true =>
        refine Sim.bind (sim_runSetupPragma hC rawDb "PRAGMA foreign_keys = ON;") ?_
        intro fkRes
        cases fkRes with
        | error _ => exact Sim.pure _
        | ok _ =>
          dsimp only
          cases Model.shouldEnableWalModel path cfg with
          | false => exact Sim.pure _
          | true => exact sim_runSetupPragma hC rawDb "PRAGMA journal_mode = WAL;"

private theorem sim_bindOneParam {W : Type} {proj : W → Model.SqliteRawState}
    {cops : CSqliteOpsM (StateM W)}
    (hC : Core.ObeysStep proj Model.cStepWf (Model.execCStep cops) Model.allowedCStep)
    (rawStmt : RawStmtHandle) (idx : UInt32) (val : SqliteValue) :
    Sim proj (Model.bindOneParamModel cops rawStmt idx val)
      (Model.bindOneParamModel Model.modelCSqliteOps rawStmt idx val) := by
  cases val with
  | null =>
    exact sim_of_cstep hC (.bindNull rawStmt idx) Model.CStepOut.unitRes
      (fun _ _ h => Model.CStepOut.unitRes.inj h) rfl rfl
  | int v =>
    exact sim_of_cstep hC (.bindInt64 rawStmt idx v) Model.CStepOut.unitRes
      (fun _ _ h => Model.CStepOut.unitRes.inj h) rfl rfl
  | real d =>
    exact sim_of_cstep hC (.bindDouble rawStmt idx d) Model.CStepOut.unitRes
      (fun _ _ h => Model.CStepOut.unitRes.inj h) rfl rfl
  | text s =>
    exact sim_of_cstep hC (.bindText rawStmt idx s) Model.CStepOut.unitRes
      (fun _ _ h => Model.CStepOut.unitRes.inj h) rfl rfl
  | bytes b =>
    exact sim_of_cstep hC (.bindBlob rawStmt idx b) Model.CStepOut.unitRes
      (fun _ _ h => Model.CStepOut.unitRes.inj h) rfl rfl

private theorem sim_bindLoop {W : Type} {proj : W → Model.SqliteRawState}
    {cops : CSqliteOpsM (StateM W)}
    (hC : Core.ObeysStep proj Model.cStepWf (Model.execCStep cops) Model.allowedCStep)
    (rawStmt : RawStmtHandle) (params : Array SqliteValue) (rem : Nat) :
    Sim proj (Model.bindLoopModel cops rawStmt params rem)
      (Model.bindLoopModel Model.modelCSqliteOps rawStmt params rem) := by
  induction rem with
  | zero => exact Sim.pure _
  | succ r ih =>
    unfold Model.bindLoopModel
    refine Sim.bind (sim_bindOneParam hC rawStmt _ _) ?_
    intro res
    cases res with
    | error _ => exact Sim.pure _
    | ok _ => exact ih

private theorem sim_decodeColumns {W : Type} {proj : W → Model.SqliteRawState}
    {cops : CSqliteOpsM (StateM W)}
    (hC : Core.ObeysStep proj Model.cStepWf (Model.execCStep cops) Model.allowedCStep)
    (rawStmt : RawStmtHandle) (total rem : Nat) (acc : Array SqliteValue) :
    Sim proj (Model.decodeColumnsModel cops rawStmt total rem acc)
      (Model.decodeColumnsModel Model.modelCSqliteOps rawStmt total rem acc) := by
  induction rem generalizing acc with
  | zero => exact Sim.pure _
  | succ r ih =>
    unfold Model.decodeColumnsModel
    let colU := UInt32.ofNat (total - (r + 1))
    refine Sim.bind
      (sim_of_cstep hC (.columnType rawStmt colU) Model.CStepOut.u32Res
        (fun _ _ h => Model.CStepOut.u32Res.inj h) rfl rfl) ?_
    intro tyRes
    cases tyRes with
    | error _ => exact Sim.pure _
    | ok ty =>
      dsimp only
      rcases hTy : ty.toNat with _ | _ | _ | _ | _ | n
      · exact ih (acc.push .null)
      · refine Sim.bind
          (sim_of_cstep hC (.columnInt64 rawStmt colU) Model.CStepOut.i64Res
            (fun _ _ h => Model.CStepOut.i64Res.inj h) rfl rfl) ?_
        intro rInt
        cases rInt with
        | error _ => exact Sim.pure _
        | ok v => exact ih (acc.push (.int v))
      · refine Sim.bind
          (sim_of_cstep hC (.columnDouble rawStmt colU) Model.CStepOut.floatRes
            (fun _ _ h => Model.CStepOut.floatRes.inj h) rfl rfl) ?_
        intro rFlt
        cases rFlt with
        | error _ => exact Sim.pure _
        | ok d => exact ih (acc.push (.real d))
      · refine Sim.bind
          (sim_of_cstep hC (.columnTextBytes rawStmt colU) Model.CStepOut.bytesRes
            (fun _ _ h => Model.CStepOut.bytesRes.inj h) rfl rfl) ?_
        intro rTxt
        cases rTxt with
        | error _ => exact Sim.pure _
        | ok bs =>
          dsimp only
          cases String.fromUTF8? bs with
          | none => exact Sim.pure _
          | some s => exact ih (acc.push (.text s))
      · refine Sim.bind
          (sim_of_cstep hC (.columnBlob rawStmt colU) Model.CStepOut.bytesRes
            (fun _ _ h => Model.CStepOut.bytesRes.inj h) rfl rfl) ?_
        intro rBlb
        cases rBlb with
        | error _ => exact Sim.pure _
        | ok bs => exact ih (acc.push (.bytes bs))
      · exact ih (acc.push .null)

private theorem sim_withStmtLock {W α : Type} {proj : W → Model.SqliteRawState}
    {cops : CSqliteOpsM (StateM W)}
    (hC : Core.ObeysStep proj Model.cStepWf (Model.execCStep cops) Model.allowedCStep)
    (stmt : StmtHandle) {act₁ : StateM W α} {act₂ : StateM Model.SqliteRawState α}
    (hAct : Sim proj act₁ act₂) :
    Sim proj (Model.withStmtLockModel cops stmt act₁)
      (Model.withStmtLockModel Model.modelCSqliteOps stmt act₂) := by
  unfold Model.withStmtLockModel
  refine Sim.bind
    (sim_of_cstep hC (.lockStmt stmt) Model.CStepOut.boolRes
      (fun _ _ h => Model.CStepOut.boolRes.inj h) rfl rfl) ?_
  intro locked
  refine Sim.bind
    (Sim.tryFinally' hAct fun _ => by
      cases locked with
      | false => exact Sim.pure ()
      | true => exact sim_unit_table hC (.unlockStmt stmt) rfl rfl) ?_
  intro pair
  exact Sim.pure pair.1

private theorem sim_mkRawOpsModel_step {W : Type} {proj : W → Model.SqliteRawState}
    {cops : CSqliteOpsM (StateM W)}
    (hC : Core.ObeysStep proj Model.cStepWf (Model.execCStep cops) Model.allowedCStep)
    (req : Model.RawStepReq) :
    Sim proj (Model.execRawStep (Model.mkRawOpsModel cops) req)
      (Model.execRawStep Model.modelRawSqliteOps req) := by
  unfold Model.modelRawSqliteOps
  cases req with
  | mapRawError _ =>
    exact Sim.pure _
  | openDb path cfg =>
    dsimp only [Model.execRawStep, Model.mkRawOpsModel]
    apply Sim.map Model.RawStepOut.openDb
    split
    · exact Sim.pure _
    · split
      · exact Sim.pure _
      · split
        · exact Sim.pure _
        · split
          · exact Sim.pure _
          · refine Sim.bind
              (sim_of_cstep hC (.openV2 path (Model.computeOpenFlagsModel cfg))
                Model.CStepOut.rawDbRes (fun _ _ h => Model.CStepOut.rawDbRes.inj h) rfl rfl) ?_
            intro openRes
            cases openRes with
            | error _ => exact Sim.pure _
            | ok rawDb =>
              dsimp only
              refine Sim.bind
                (Sim.tryFinally' (sim_setupConnection hC path cfg rawDb) fun o => by
                  cases o with
                  | none =>
                    dsimp only
                    exact Sim.bind
                      (sim_of_cstep hC (.close rawDb) Model.CStepOut.unitRes
                        (fun _ _ h => Model.CStepOut.unitRes.inj h) rfl rfl)
                      (fun _ => Sim.pure ())
                  | some r =>
                    cases r with
                    | error _ =>
                      dsimp only
                      exact Sim.bind
                        (sim_of_cstep hC (.close rawDb) Model.CStepOut.unitRes
                          (fun _ _ h => Model.CStepOut.unitRes.inj h) rfl rfl)
                        (fun _ => Sim.pure ())
                    | ok u =>
                      cases u
                      exact Sim.pure ()) ?_
              intro pair
              rcases pair with ⟨setupRes, _⟩
              cases setupRes with
              | error _ => exact Sim.pure _
              | ok _ =>
                dsimp only
                refine Sim.bind
                  (sim_of_cstep hC (.tableInsertDb rawDb) Model.CStepOut.dbHandle
                    (fun _ _ h => Model.CStepOut.dbHandle.inj h) rfl rfl)
                  (fun _ => Sim.pure _)
  | closeDb db =>
    dsimp only [Model.execRawStep, Model.mkRawOpsModel]
    apply Sim.map Model.RawStepOut.closeDb
    refine Sim.bind
      (sim_of_cstep hC (.tableCheckCloseDb db.id) Model.CStepOut.rawDbRes
        (fun _ _ h => Model.CStepOut.rawDbRes.inj h) rfl rfl) ?_
    intro chkRes
    cases chkRes with
    | error _ => exact Sim.pure _
    | ok rawDb =>
      dsimp only
      refine Sim.bind
        (sim_of_cstep hC (.close rawDb) Model.CStepOut.unitRes
          (fun _ _ h => Model.CStepOut.unitRes.inj h) rfl rfl) ?_
      intro clsRes
      cases clsRes with
      | error _ => exact Sim.pure _
      | ok _ =>
        dsimp only
        exact Sim.bind (sim_unit_table hC (.tableEraseDb db.id) rfl rfl) (fun _ => Sim.pure _)
  | prepare db sql =>
    dsimp only [Model.execRawStep, Model.mkRawOpsModel]
    apply Sim.map Model.RawStepOut.prepare
    split
    · exact Sim.pure _
    · split
      · exact Sim.pure _
      · refine Sim.bind
          (sim_of_cstep hC (.tableLookupDb db.id) Model.CStepOut.rawDbOpt
            (fun _ _ h => Model.CStepOut.rawDbOpt.inj h) rfl rfl) ?_
        intro dbOpt
        cases dbOpt with
        | none => exact Sim.pure _
        | some rawDb =>
          dsimp only
          refine Sim.bind
            (sim_of_cstep hC (.prepareV2 rawDb sql) Model.CStepOut.prepRes
              (fun _ _ h => Model.CStepOut.prepRes.inj h) rfl rfl) ?_
          intro prepRes
          cases prepRes with
          | error _ => exact Sim.pure _
          | ok pair =>
            rcases pair with ⟨stmt?, consumed⟩
            cases stmt? with
            | none => exact Sim.pure _
            | some rawStmt =>
              dsimp only
              cases (consumed ≤ sql.toUTF8.size &&
                  Model.scanSqlTailBaModel .normal sql.toUTF8 consumed) with
              | false =>
                refine Sim.bind
                  (sim_of_cstep hC (.finalize rawStmt) Model.CStepOut.finRes
                    (fun _ _ h => Model.CStepOut.finRes.inj h) rfl rfl)
                  (fun _ => Sim.pure _)
              | true =>
                refine Sim.bind
                  (sim_of_cstep hC (.tableInsertStmt db.id rawStmt) Model.CStepOut.stmtHandle
                    (fun _ _ h => Model.CStepOut.stmtHandle.inj h) rfl rfl)
                  (fun _ => Sim.pure _)
  | bind stmt params =>
    dsimp only [Model.execRawStep, Model.mkRawOpsModel]
    apply Sim.map Model.RawStepOut.bind
    apply sim_withStmtLock hC stmt
    refine Sim.bind
      (sim_of_cstep hC (.tableLookupStmt stmt) Model.CStepOut.rawStmtOpt
        (fun _ _ h => Model.CStepOut.rawStmtOpt.inj h) rfl rfl) ?_
    intro stOpt
    cases stOpt with
    | none => exact Sim.pure _
    | some rawStmt =>
      dsimp only
      refine Sim.bind
        (sim_of_cstep hC (.reset rawStmt) Model.CStepOut.unitRes
          (fun _ _ h => Model.CStepOut.unitRes.inj h) rfl rfl) ?_
      intro r1
      cases r1 with
      | error _ => exact Sim.pure _
      | ok _ =>
        dsimp only
        refine Sim.bind
          (sim_of_cstep hC (.clearBindings rawStmt) Model.CStepOut.unitRes
            (fun _ _ h => Model.CStepOut.unitRes.inj h) rfl rfl) ?_
        intro r2
        cases r2 with
        | error _ => exact Sim.pure _
        | ok _ =>
          dsimp only
          refine Sim.bind
            (sim_of_cstep hC (.bindParamCount rawStmt) Model.CStepOut.u32Res
              (fun _ _ h => Model.CStepOut.u32Res.inj h) rfl rfl) ?_
          intro r3
          cases r3 with
          | error _ => exact Sim.pure _
          | ok cnt =>
            dsimp only
            cases (params.size != cnt.toNat) with
            | true => exact Sim.pure _
            | false => exact sim_bindLoop hC rawStmt params params.size
  | step stmt =>
    dsimp only [Model.execRawStep, Model.mkRawOpsModel]
    apply Sim.map Model.RawStepOut.step
    apply sim_withStmtLock hC stmt
    refine Sim.bind
      (sim_of_cstep hC (.tableLookupStmt stmt) Model.CStepOut.rawStmtOpt
        (fun _ _ h => Model.CStepOut.rawStmtOpt.inj h) rfl rfl) ?_
    intro stOpt
    cases stOpt with
    | none => exact Sim.pure _
    | some rawStmt =>
      dsimp only
      refine Sim.bind
        (sim_of_cstep hC (.step rawStmt) Model.CStepOut.stepTagRes
          (fun _ _ h => Model.CStepOut.stepTagRes.inj h) rfl rfl) ?_
      intro stRes
      cases stRes with
      | error _ => exact Sim.pure _
      | ok tag =>
        cases tag with
        | done => exact Sim.pure _
        | row =>
          dsimp only
          refine Sim.bind
            (sim_of_cstep hC (.columnCount rawStmt) Model.CStepOut.u32Res
              (fun _ _ h => Model.CStepOut.u32Res.inj h) rfl rfl) ?_
          intro cntRes
          cases cntRes with
          | error _ => exact Sim.pure _
          | ok cnt =>
            dsimp only
            refine Sim.bind (sim_decodeColumns hC rawStmt cnt.toNat cnt.toNat #[]) ?_
            intro colsRes
            cases colsRes <;> exact Sim.pure _
  | finalize stmt =>
    dsimp only [Model.execRawStep, Model.mkRawOpsModel]
    apply Sim.map Model.RawStepOut.finalize
    apply sim_withStmtLock hC stmt
    refine Sim.bind
      (sim_of_cstep hC (.tableLookupStmt stmt) Model.CStepOut.rawStmtOpt
        (fun _ _ h => Model.CStepOut.rawStmtOpt.inj h) rfl rfl) ?_
    intro stOpt
    cases stOpt with
    | none => exact Sim.pure _
    | some rawStmt =>
      dsimp only
      refine Sim.bind
        (sim_of_cstep hC (.finalize rawStmt) Model.CStepOut.finRes
          (fun _ _ h => Model.CStepOut.finRes.inj h) rfl rfl) ?_
      intro finOut
      cases finOut with
      | finalized st? =>
        dsimp only
        refine Sim.bind (sim_unit_table hC (.tableEraseStmt stmt) rfl rfl) ?_
        intro _
        cases st? <;> exact Sim.pure _
      | rejected _ => exact Sim.pure _
  | activeDbCount =>
    dsimp only [Model.execRawStep, Model.mkRawOpsModel]
    apply Sim.map Model.RawStepOut.activeDbCount
    exact sim_of_cstep hC .tableActiveDbCount Model.CStepOut.count
      (fun _ _ h => Model.CStepOut.count.inj h) rfl rfl
  | activeStmtCount =>
    dsimp only [Model.execRawStep, Model.mkRawOpsModel]
    apply Sim.map Model.RawStepOut.activeStmtCount
    exact sim_of_cstep hC .tableActiveStmtCount Model.CStepOut.count
      (fun _ _ h => Model.CStepOut.count.inj h) rfl rfl

/-- `Internal.mkRawOps` satisfies `Core.ObeysStepFromFinally` from `CSqliteOpsM` to `RawSqliteOpsM`. -/
theorem mkRawOps_obeys :
    Core.ObeysStepFromFinally id Model.cStepWf
      Model.execCStep Model.allowedCStep Model.rawStepWf
      Internal.mkRawOps Model.execPkgStep Model.allowedPkgStep := by
  intro W proj cops hC w req hWf
  dsimp only [Model.execPkgStep, Model.allowedPkgStep, Function.comp, id]
  rw [mkRawOps_eq_model cops]
  rcases sim_mkRawOpsModel_step hC req w with ⟨hVal, hSt⟩
  refine ⟨hVal, hSt, ?_⟩
  rw [hSt]
  exact modelRawSqliteOps_preserves_wf (proj w) req hWf

/-- `Model.modelCSqliteOps` satisfies `Model.allowedCStep` at identity state projection. -/
theorem modelCSqliteOps_obeys :
    Core.ObeysStepId Model.cStepWf
      (Model.execCStep Model.modelCSqliteOps) Model.allowedCStep := by
  intro s req _
  exact ⟨rfl, rfl⟩

end LeanSwe.Sqlite.Raw.Proofs
