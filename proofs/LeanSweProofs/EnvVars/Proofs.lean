import Core.Assumptions
import Core.Obeys
import LeanSwe.EnvVars.Types
import LeanSwe.EnvVars.Impl
import LeanSwe.EnvVars.Interface
import LeanSweProofs.EnvVars.Model
import LeanSweProofs.EnvVars.Model.Refines

namespace LeanSwe.EnvVars.Proofs

open Core

private theorem baseIO_liftM_never_throws {α : Type} (act : BaseIO α) (w : Void IO.RealWorld) :
    ∃ a w', (liftM act : IO α) w = .ok a w' := by
  simp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, BaseIO.toEIO]
  cases act w with
  | mk a s => exact ⟨a, s, rfl⟩

private theorem io_pure_eq {α : Type} (a : α) (w : Void IO.RealWorld) :
    (pure a : IO α) w = EST.Out.ok a w := rfl

private theorem io_bind_baseIO {α β : Type} (act : BaseIO α) (k : α → IO β) (w : Void IO.RealWorld) :
    ((liftM act : IO α) >>= k) w = k (act w).val (act w).state := by
  rcases baseIO_liftM_never_throws act w with ⟨v, w', hv⟩
  have hst : act w = .mk v w' := by
    simp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, BaseIO.toEIO] at hv
    cases h : act w with
    | mk a s =>
      rw [h] at hv
      have ha : a = v := by injection hv
      have hs : s = w' := by injection hv
      subst ha hs
      rfl
  rw [hst]
  have hbind : ((liftM act : IO α) >>= k) w =
      match (liftM act : IO α) w with
      | EST.Out.ok a s => k a s
      | EST.Out.error e s => EST.Out.error e s := rfl
  rw [hbind, hv]

private theorem decodeEnvironAcc_only_invalidEncoding
    (accRev : List (String × String)) (xs : List ByteArray) {err : EnvVarsError}
    (herr : Internal.decodeEnvironAcc accRev xs = .error err) :
    err.kind = .invalidEncoding := by
  induction xs generalizing accRev with
  | nil => simp [Internal.decodeEnvironAcc] at herr
  | cons entry rest ih =>
    unfold Internal.decodeEnvironAcc at herr
    cases hs : Internal.splitFirstEqBytes entry with
    | none => rw [hs] at herr; exact ih accRev herr
    | some kv =>
      rcases kv with ⟨kBytes, vBytes⟩
      rw [hs] at herr
      dsimp only at herr
      cases hk : String.fromUTF8? kBytes with
      | none => rw [hk] at herr; injection herr with he; subst he; rfl
      | some k =>
        rw [hk] at herr
        dsimp only at herr
        cases hv : String.fromUTF8? vBytes with
        | none => rw [hv] at herr; injection herr with he; subst he; rfl
        | some v =>
          rw [hv] at herr
          exact ih ((k, v) :: accRev) herr

private theorem mkApiM_getEnv_never
    (f : EnvVarsErrorKind) (hf1 : f ≠ .invalidKey) (hf2 : f ≠ .invalidEncoding)
    (g : String → BaseIO (Option ByteArray))
    (l : BaseIO (Array ByteArray))
    (key : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsError.kind f
      ((Internal.mkApiM (m := IO) {
        getEnvBytes := fun k => liftM (g k)
        listEnvironBytes := liftM l
      }).getEnv key) w := by
  unfold Core.NeverErrorKindIO
  simp only [Internal.mkApiM]
  by_cases hk : Internal.isValidKey key
  · simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [io_bind_baseIO]
    cases (g key w).val with
    | none => dsimp only; rw [io_pure_eq]; trivial
    | some bs =>
      dsimp only
      cases String.fromUTF8? bs with
      | some _ => dsimp only; rw [io_pure_eq]; trivial
      | none => dsimp only; rw [io_pure_eq]; exact hf2.symm
  · simp only [hk, Bool.not_false, ↓reduceIte]
    rw [io_pure_eq]
    exact hf1.symm

private theorem mkApiM_listEnv_never
    (f : EnvVarsErrorKind) (hf : f ≠ .invalidEncoding)
    (g : String → BaseIO (Option ByteArray))
    (l : BaseIO (Array ByteArray))
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsError.kind f
      ((Internal.mkApiM (m := IO) {
        getEnvBytes := fun k => liftM (g k)
        listEnvironBytes := liftM l
      }).listEnv) w := by
  unfold Core.NeverErrorKindIO
  simp only [Internal.mkApiM]
  rw [io_bind_baseIO]
  cases hd : Internal.decodeEnvironAcc [] (l w).val.toList with
  | ok _ => simp only [Except.map]; rw [io_pure_eq]; trivial
  | error err =>
    simp only [Except.map]
    rw [io_pure_eq]
    intro heq
    exact hf (heq ▸ decodeEnvironAcc_only_invalidEncoding [] (l w).val.toList hd)

private theorem mkApiM_homeDir_never
    (f : EnvVarsErrorKind) (hf1 : f ≠ .notFound) (hf2 : f ≠ .invalidEncoding)
    (g : String → BaseIO (Option ByteArray))
    (l : BaseIO (Array ByteArray))
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsError.kind f
      ((Internal.mkApiM (m := IO) {
        getEnvBytes := fun k => liftM (g k)
        listEnvironBytes := liftM l
      }).homeDir) w := by
  unfold Core.NeverErrorKindIO
  simp only [Internal.mkApiM]
  rw [io_bind_baseIO]
  cases (g "HOME" w).val with
  | none => dsimp only; rw [io_pure_eq]; exact hf1.symm
  | some bs =>
    dsimp only
    cases String.fromUTF8? bs with
    | none => dsimp only; rw [io_pure_eq]; exact hf2.symm
    | some s =>
      by_cases hs : s = ""
      · subst hs; simp [io_pure_eq]; exact hf1.symm
      · simp [io_pure_eq]

private theorem mkApiM_getEnv_never_throws
    (g : String → BaseIO (Option ByteArray))
    (l : BaseIO (Array ByteArray))
    (key : String) (w : Void IO.RealWorld) :
    ∃ res w', (Internal.mkApiM (m := IO) {
      getEnvBytes := fun k => liftM (g k)
      listEnvironBytes := liftM l
    }).getEnv key w = EST.Out.ok res w' := by
  simp only [Internal.mkApiM]
  by_cases hk : Internal.isValidKey key
  · simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [io_bind_baseIO]
    cases (g key w).val with
    | none => exact ⟨_, _, io_pure_eq _ _⟩
    | some bs =>
      dsimp only
      cases String.fromUTF8? bs <;> exact ⟨_, _, io_pure_eq _ _⟩
  · simp only [hk, Bool.not_false, ↓reduceIte]
    exact ⟨_, _, io_pure_eq _ _⟩

private theorem mkApiM_listEnv_never_throws
    (g : String → BaseIO (Option ByteArray))
    (l : BaseIO (Array ByteArray))
    (w : Void IO.RealWorld) :
    ∃ res w', (Internal.mkApiM (m := IO) {
      getEnvBytes := fun k => liftM (g k)
      listEnvironBytes := liftM l
    }).listEnv w = EST.Out.ok res w' := by
  simp only [Internal.mkApiM]
  rw [io_bind_baseIO]
  exact ⟨_, _, io_pure_eq _ _⟩

/-- `defaultApi.getEnv` never throws an uncaught `IO.Error`. -/
theorem defaultApi_getEnv_never_throws (key : String) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.EnvVars.defaultApi.getEnv key w = EST.Out.ok res w' := by
  apply mkApiM_getEnv_never_throws

/-- `defaultApi.listEnv` never throws an uncaught `IO.Error`. -/
theorem defaultApi_listEnv_never_throws (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.EnvVars.defaultApi.listEnv w = EST.Out.ok res w' := by
  apply mkApiM_listEnv_never_throws

/-- Proof that `EnvVars.getEnv` never returns `.notFound`. -/
theorem envvars_getEnv_never_notFound (key : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsError.kind .notFound (EnvVars.getEnv key) w := by
  apply mkApiM_getEnv_never .notFound (by decide) (by decide)

/-- Proof that `EnvVars.getEnv` never returns `.ioError`. -/
theorem envvars_getEnv_never_ioError (key : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsError.kind .ioError (EnvVars.getEnv key) w := by
  apply mkApiM_getEnv_never .ioError (by decide) (by decide)

/-- Proof that `EnvVars.listEnv` never returns `.invalidKey`. -/
theorem envvars_listEnv_never_invalidKey (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsError.kind .invalidKey EnvVars.listEnv w := by
  apply mkApiM_listEnv_never .invalidKey (by decide)

/-- Proof that `EnvVars.listEnv` never returns `.notFound`. -/
theorem envvars_listEnv_never_notFound (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsError.kind .notFound EnvVars.listEnv w := by
  apply mkApiM_listEnv_never .notFound (by decide)

/-- Proof that `EnvVars.listEnv` never returns `.ioError`. -/
theorem envvars_listEnv_never_ioError (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsError.kind .ioError EnvVars.listEnv w := by
  apply mkApiM_listEnv_never .ioError (by decide)

/-- Proof that `EnvVars.homeDir` never returns `.invalidKey`. -/
theorem envvars_homeDir_never_invalidKey (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsError.kind .invalidKey EnvVars.homeDir w := by
  apply mkApiM_homeDir_never .invalidKey (by decide) (by decide)

/-- Proof that `EnvVars.homeDir` never returns `.ioError`. -/
theorem envvars_homeDir_never_ioError (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsError.kind .ioError EnvVars.homeDir w := by
  apply mkApiM_homeDir_never .ioError (by decide) (by decide)

private theorem splitColonAccModel_eq (curRev : List Char) (accRev : List (List Char)) (cs : List Char) :
    Model.splitColonAccModel curRev accRev cs = Internal.splitColonAcc curRev accRev cs := by
  induction cs generalizing curRev accRev with
  | nil => rfl
  | cons c cs ih =>
    simp only [Model.splitColonAccModel, Internal.splitColonAcc]
    split <;> exact ih _ _

private theorem splitSearchPathModel_eq (path : String) :
    Model.splitSearchPathModel path = Internal.splitSearchPath path := by
  simp [Model.splitSearchPathModel, Internal.splitSearchPath, splitColonAccModel_eq]

private theorem hasInvalidKeyCharModel_eq (cs : List Char) :
    Model.hasInvalidKeyCharModel cs = Internal.hasInvalidKeyChar cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [Model.hasInvalidKeyCharModel, Internal.hasInvalidKeyChar, ih]
    cases (c == '=' || c == Char.ofNat 0) <;> rfl

private theorem isValidKey_eq_model (key : String) :
    Internal.isValidKey key = Model.isValidPosixKeyModel key := by
  simp [Internal.isValidKey, Model.isValidPosixKeyModel, hasInvalidKeyCharModel_eq]

private theorem splitFirstEqListModel_eq (rp bl : List UInt8) :
    Model.splitFirstEqListModel rp bl = Internal.splitFirstEqList rp bl := by
  induction bl generalizing rp with
  | nil => rfl
  | cons b bs ih =>
    simp only [Model.splitFirstEqListModel, Internal.splitFirstEqList]
    split
    · rfl
    · exact ih (b :: rp)

private theorem splitFirstEqBytesModel_eq (entry : ByteArray) :
    Model.splitFirstEqBytesModel entry = Internal.splitFirstEqBytes entry :=
  splitFirstEqListModel_eq [] entry.data.toList

private theorem mapRawError_eq_model (err : EnvVarsRawError) :
    LeanSwe.EnvVars.mapRawError err = Model.mapRawErrorModel err := by
  cases err <;> rfl

private theorem decodeEnvironModelAcc_eq (accRev : List (String × String)) (xs : List ByteArray) :
    Model.decodeEnvironModelAcc accRev xs = Internal.decodeEnvironAcc accRev xs := by
  induction xs generalizing accRev with
  | nil => rfl
  | cons entry rest ih =>
    simp only [Model.decodeEnvironModelAcc, Internal.decodeEnvironAcc, splitFirstEqBytesModel_eq]
    cases Internal.splitFirstEqBytes entry with
    | none => exact ih accRev
    | some kv =>
      rcases kv with ⟨kBytes, vBytes⟩
      dsimp only
      cases String.fromUTF8? kBytes with
      | none => rfl
      | some k =>
        cases String.fromUTF8? vBytes with
        | none => rfl
        | some v => exact ih ((k, v) :: accRev)

private theorem stateM_map_run {W α β : Type} (f : α → β) (m : StateM W α) (w : W) :
    (f <$> m).run w = (f (m.run w).1, (m.run w).2) := rfl

private theorem stateM_bind_run {W α β : Type} (m : StateM W α) (k : α → StateM W β) (w : W) :
    (m >>= k).run w = (k (m.run w).1).run (m.run w).2 := rfl

private theorem stateM_pure_run {W α : Type} (a : α) (w : W) :
    (pure a : StateM W α).run w = (a, w) := rfl

private theorem obeysStepFrom_mkApiM :
    Core.ObeysStepFrom id Model.rawStepWf Model.execPosixStep Model.allowedPosixStep
      Model.rawStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj posix hPosix w req _
  cases req with
  | getEnv key =>
    dsimp only [Model.execPkgStep, Internal.mkApiM]
    rw [stateM_map_run, isValidKey_eq_model]
    cases hk : Model.isValidPosixKeyModel key with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, stateM_pure_run, Model.allowedPkgStep,
        Model.getEnvModel, hk]
      trivial
    | true =>
      have hStep := hPosix w (.getEnvBytes key) rfl
      have hProj : proj ((posix.getEnvBytes key).run w).2 = proj w := hStep.1
      have hOut : ((posix.getEnvBytes key).run w).1 = Model.posixGetEnvBytesModel (proj w) key := hStep.2
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hOut]
      cases hm : Model.posixGetEnvBytesModel (proj w) key with
      | none =>
        simp only [stateM_pure_run, Model.allowedPkgStep, Model.getEnvModel, Function.comp, id,
          hk, hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hProj, trivial⟩
      | some bs =>
        cases hUtf : String.fromUTF8? bs with
        | some s =>
          simp only [hUtf, stateM_pure_run, Model.allowedPkgStep, Model.getEnvModel, Function.comp, id,
            hk, hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact ⟨hProj, trivial⟩
        | none =>
          simp only [hUtf, stateM_pure_run, Model.allowedPkgStep, Model.getEnvModel, Function.comp, id,
            hk, hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact ⟨hProj, rfl⟩
  | listEnv =>
    have hStep := hPosix w .listEnvironBytes rfl
    have hProj : proj (posix.listEnvironBytes.run w).2 = proj w := hStep.1
    have hOut : (posix.listEnvironBytes.run w).1 = (proj w).entries := hStep.2
    simp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgStep, Model.listEnvModel,
      stateM_map_run, stateM_bind_run, stateM_pure_run, hOut, decodeEnvironModelAcc_eq]
    exact ⟨hProj, rfl⟩
  | homeDir =>
    have hStep := hPosix w (.getEnvBytes "HOME") rfl
    have hProj : proj ((posix.getEnvBytes "HOME").run w).2 = proj w := hStep.1
    have hOut : ((posix.getEnvBytes "HOME").run w).1 = Model.posixGetEnvBytesModel (proj w) "HOME" := hStep.2
    simp only [Model.execPkgStep, Internal.mkApiM, stateM_map_run, stateM_bind_run, hOut]
    cases hm : Model.posixGetEnvBytesModel (proj w) "HOME" with
    | none =>
      simp only [stateM_pure_run, Model.allowedPkgStep, Model.homeDirModel, Function.comp, id, hm]
      exact ⟨hProj, trivial⟩
    | some bs =>
      cases hUtf : String.fromUTF8? bs with
      | none =>
        simp only [hUtf, stateM_pure_run, Model.allowedPkgStep, Model.homeDirModel, Function.comp, id, hm]
        exact ⟨hProj, rfl⟩
      | some v =>
        by_cases hv : v = ""
        · subst hv
          simp only [hUtf, stateM_pure_run, Model.allowedPkgStep, Model.homeDirModel, Function.comp, id, hm]
          exact ⟨hProj, trivial⟩
        · simp only [hUtf, stateM_pure_run, Model.allowedPkgStep, Model.homeDirModel, Function.comp, id, hm]
          exact ⟨hProj, trivial⟩
  | listEnvironBytes =>
    have hStep := hPosix w .listEnvironBytes rfl
    have hProj : proj (posix.listEnvironBytes.run w).2 = proj w := hStep.1
    have hOut : (posix.listEnvironBytes.run w).1 = (proj w).entries := hStep.2
    simp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgStep, stateM_map_run, hOut]
    exact ⟨hProj, rfl⟩

/-- Full public `Interface` obedience of `LeanSwe.EnvVars` against `LeanSwe.EnvVars.Model`. -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.EnvVars.mapRawError Model.mapRawErrorModel ∧
    Core.ObeysPureEq LeanSwe.EnvVars.splitSearchPath Model.splitSearchPathModel ∧
    Core.ObeysStepFrom id Model.rawStepWf Model.execPosixStep Model.allowedPosixStep
      Model.rawStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep :=
  ⟨mapRawError_eq_model,
   fun path => (splitSearchPathModel_eq path).symm,
   obeysStepFrom_mkApiM⟩

private theorem modelStatePosixOps_obeys :
    Core.ObeysStepId Model.rawStepWf
      (Model.execPosixStep Model.modelStatePosixOps) Model.allowedPosixStep := by
  intro s req _
  cases req <;> exact ⟨rfl, rfl⟩

/-- Concrete non-vacuity witness instantiating `obeys_model` over `Model.modelStatePosixOps`. -/
theorem obeys_model_nonvacuous :
    Core.ObeysStepId Model.rawStepWf
      (Model.execPkgStep (Internal.mkApiM Model.modelStatePosixOps)) Model.allowedPkgStep :=
  obeys_model.2.2 id Model.modelStatePosixOps modelStatePosixOps_obeys

end LeanSwe.EnvVars.Proofs
