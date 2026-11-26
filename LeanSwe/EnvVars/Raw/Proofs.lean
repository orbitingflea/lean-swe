import Core.Assumptions
import Core.Obeys
import LeanSwe.EnvVars.Raw.Types
import LeanSwe.EnvVars.Raw.Model
import LeanSwe.EnvVars.Raw.Model.Refines
import LeanSwe.EnvVars.Raw.Interface
import LeanSwe.EnvVars.Raw.Impl
import LeanSwe.EnvVars.Raw.SpecTests
import LeanSwe.EnvVars.Raw.Proofs.Utf8AndSplit
import LeanSwe.EnvVars.Raw.Proofs.ListAndModel

namespace LeanSwe.EnvVars.Raw.Proofs

open Core
open Core.NondetTest

/-- Proof of `test_envvarsraw_mapRawError_returnsNonEmptyMessage` for `defaultOps`. -/
theorem proof_envvarsraw_mapRawError_returnsNonEmptyMessage :
    AllPass (test_envvarsraw_mapRawError_returnsNonEmptyMessage defaultOps) := by
  intro raw
  simp only [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]
  refine ⟨?_, trivial⟩
  cases raw with
  | invalidEncoding _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | invalidArgument _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | otherError code _ =>
    exact nonEmptyMsg_ne_empty _ _ (append_head_ne_empty "os error " (toString code) (by decide))
  | userError _ => exact nonEmptyMsg_ne_empty _ _ (by decide)

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_mapRawError_returnsNonEmptyMessage`. -/
theorem reach_envvarsraw_mapRawError_returnsNonEmptyMessage :
    CanReach (test_envvarsraw_mapRawError_returnsNonEmptyMessage defaultOps) :=
  ⟨.userError "", proof_envvarsraw_mapRawError_returnsNonEmptyMessage (.userError "")⟩

/-- Proof of `test_envvarsraw_mapRawError_preservesKindAndMetadata` for `defaultOps`. -/
theorem proof_envvarsraw_mapRawError_preservesKindAndMetadata :
    AllPass (test_envvarsraw_mapRawError_preservesKindAndMetadata defaultOps) := by
  intro raw
  cases raw <;> simp [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_mapRawError_preservesKindAndMetadata`. -/
theorem reach_envvarsraw_mapRawError_preservesKindAndMetadata :
    CanReach (test_envvarsraw_mapRawError_preservesKindAndMetadata defaultOps) :=
  ⟨.invalidEncoding (some "PATH") "bad",
    proof_envvarsraw_mapRawError_preservesKindAndMetadata (.invalidEncoding (some "PATH") "bad")⟩

/-- Proof of `test_envvarsraw_mapRawError_consistentAcrossBackends` for `defaultOps` and `Internal.mkRawOps`. -/
theorem proof_envvarsraw_mapRawError_consistentAcrossBackends :
    AllPass (test_envvarsraw_mapRawError_consistentAcrossBackends defaultOps (Internal.mkRawOps (m := Id))) := by
  intro _ _
  simp [defaultOps, Internal.mkRawOps, assert]

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_mapRawError_consistentAcrossBackends`. -/
theorem reach_envvarsraw_mapRawError_consistentAcrossBackends :
    CanReach (test_envvarsraw_mapRawError_consistentAcrossBackends defaultOps (Internal.mkRawOps (m := Id))) :=
  ⟨{ getEnvBytes := fun _ => none, listEnvironBytes := #[] }, .userError "",
    proof_envvarsraw_mapRawError_consistentAcrossBackends
      { getEnvBytes := fun _ => none, listEnvironBytes := #[] } (.userError "")⟩

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

private theorem mkRawOps_getEnv_never
    (f : EnvVarsRawErrorKind) (hf : f ≠ .invalidEncoding)
    (g : String → BaseIO (Option ByteArray))
    (l : BaseIO (Array ByteArray))
    (key : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsRawError.kind f
      ((Internal.mkRawOps (m := IO) {
        getEnvBytes := fun k => liftM (g k)
        listEnvironBytes := liftM l
      }).getEnv key) w := by
  unfold Core.NeverErrorKindIO
  simp only [Internal.mkRawOps]
  by_cases hk : Internal.isValidPosixKey key
  · simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [io_bind_baseIO]
    cases (g key w).val with
    | none => dsimp only; rw [io_pure_eq]; trivial
    | some bs =>
      dsimp only
      cases hutf : String.fromUTF8? bs with
      | some _ => dsimp only; rw [io_pure_eq]; trivial
      | none => dsimp only; rw [io_pure_eq]; simp only [EnvVarsRawError.kind]; exact hf.symm
  · simp only [hk, Bool.not_false, ↓reduceIte]
    rw [io_pure_eq]
    trivial

private theorem mkRawOps_listEnv_never
    (f : EnvVarsRawErrorKind) (hf : f ≠ .invalidEncoding)
    (g : String → BaseIO (Option ByteArray))
    (l : BaseIO (Array ByteArray))
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsRawError.kind f
      ((Internal.mkRawOps (m := IO) {
        getEnvBytes := fun k => liftM (g k)
        listEnvironBytes := liftM l
      }).listEnv) w := by
  unfold Core.NeverErrorKindIO
  simp only [Internal.mkRawOps, decodeEnvironAcc_nil]
  rw [io_bind_baseIO]
  cases hd : decodeEnvironList (l w).val.toList with
  | ok _ => simp only [Except.map]; rw [io_pure_eq]; trivial
  | error err =>
    simp only [Except.map]
    rw [io_pure_eq]
    intro heq
    exact hf (heq ▸ decodeEnvironList_only_invalidEncoding (l w).val.toList hd)

/-- Proof that `Raw.getEnv` never returns `.invalidArgument`. -/
theorem raw_getEnv_never_invalidArgument (key : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsRawError.kind .invalidArgument (Raw.getEnv key) w := by
  apply mkRawOps_getEnv_never .invalidArgument (by decide)

/-- Proof that `Raw.getEnv` never returns `.otherError`. -/
theorem raw_getEnv_never_otherError (key : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsRawError.kind .otherError (Raw.getEnv key) w := by
  apply mkRawOps_getEnv_never .otherError (by decide)

/-- Proof that `Raw.getEnv` never returns `.userError`. -/
theorem raw_getEnv_never_userError (key : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsRawError.kind .userError (Raw.getEnv key) w := by
  apply mkRawOps_getEnv_never .userError (by decide)

/-- Proof that `Raw.listEnv` never returns `.invalidArgument`. -/
theorem raw_listEnv_never_invalidArgument (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsRawError.kind .invalidArgument Raw.listEnv w := by
  apply mkRawOps_listEnv_never .invalidArgument (by decide)

/-- Proof that `Raw.listEnv` never returns `.otherError`. -/
theorem raw_listEnv_never_otherError (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsRawError.kind .otherError Raw.listEnv w := by
  apply mkRawOps_listEnv_never .otherError (by decide)

/-- Proof that `Raw.listEnv` never returns `.userError`. -/
theorem raw_listEnv_never_userError (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsRawError.kind .userError Raw.listEnv w := by
  apply mkRawOps_listEnv_never .userError (by decide)

private theorem mapRawError_obeys :
    Core.ObeysPureEq mapRawError Model.mapRawErrorModel := by
  intro err
  cases err <;> rfl

private theorem stateM_map_run {W α β : Type} (f : α → β) (m : StateM W α) (w : W) :
    (f <$> m).run w = (f (m.run w).1, (m.run w).2) := rfl

private theorem stateM_bind_run {W α β : Type} (m : StateM W α) (k : α → StateM W β) (w : W) :
    (m >>= k).run w = (k (m.run w).1).run (m.run w).2 := rfl

private theorem stateM_pure_run {W α : Type} (a : α) (w : W) :
    (pure a : StateM W α).run w = (a, w) := rfl

private theorem mkRawBundle_obeys :
    Core.ObeysStepFrom id Model.rawStepWf
      Model.execPosixStep Model.allowedPosixStep Model.rawStepWf
      Internal.mkRawBundle Model.execPkgStep Model.allowedPkgStep := by
  intro W proj posix hPosix w req _
  cases req with
  | getEnv key =>
    by_cases hk : Internal.isValidPosixKey key = true
    · have hStep := hPosix w (.getEnvBytes key) rfl
      have hProj : proj ((posix.getEnvBytes key).run w).2 = proj w := hStep.1
      have hOut : ((posix.getEnvBytes key).run w).1 = Model.posixGetEnvBytesModel (proj w) key :=
        hStep.2
      have hkMod : Model.isValidPosixKeyModel key = true := by
        rw [isValidPosixKeyModel_eq]
        exact hk
      simp only [Model.posixGetEnvBytesModel, hkMod, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte] at hOut
      simp only [Model.execPkgStep, Internal.mkRawOps, Model.allowedPkgStep,
        Model.rawGetEnvModel, Model.posixGetEnvBytesModel, Function.comp, id,
        hk, hkMod, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        stateM_map_run, stateM_bind_run, hOut]
      cases Model.findFirstKeyValue (proj w).entries.toList key.toUTF8 with
      | none =>
        simp only [stateM_pure_run]
        exact ⟨hProj, trivial⟩
      | some bs =>
        cases hUtf : String.fromUTF8? bs
        · simp only [hUtf, stateM_pure_run]
          exact ⟨hProj, trivial⟩
        · simp only [hUtf, stateM_pure_run]
          exact ⟨hProj, trivial⟩
    · have hkF : Internal.isValidPosixKey key = false := Bool.eq_false_iff.mpr hk
      have hkModF : Model.isValidPosixKeyModel key = false := by
        rw [isValidPosixKeyModel_eq]
        exact hkF
      simp only [Model.execPkgStep, Internal.mkRawOps, Model.allowedPkgStep,
        Model.rawGetEnvModel, Model.posixGetEnvBytesModel, Function.comp, id,
        hkF, hkModF, Bool.not_false, ↓reduceIte, stateM_map_run, stateM_pure_run]
      trivial
  | listEnv =>
    have hStep := hPosix w .listEnvironBytes rfl
    have hProj : proj (posix.listEnvironBytes.run w).2 = proj w := hStep.1
    have hOut : (posix.listEnvironBytes.run w).1 = (proj w).entries := hStep.2
    simp only [Model.execPkgStep, Internal.mkRawOps, Model.allowedPkgStep,
      Model.rawListEnvModel, Function.comp, id,
      stateM_map_run, stateM_bind_run, stateM_pure_run, hOut, decodeEnvironModelAcc_eq]
    exact ⟨hProj, trivial⟩
  | listEnvironBytes =>
    have hStep := hPosix w .listEnvironBytes rfl
    have hProj : proj (posix.listEnvironBytes.run w).2 = proj w := hStep.1
    have hOut : (posix.listEnvironBytes.run w).1 = (proj w).entries := hStep.2
    simp only [Model.execPkgStep, Model.allowedPkgStep,
      Function.comp, id, stateM_map_run, hOut]
    exact ⟨hProj, trivial⟩

/-- Canonical `Core.Obeys*` specification theorem for `LeanSwe.EnvVars.Raw`. -/
theorem obeys_model :
    Core.ObeysPureEq mapRawError Model.mapRawErrorModel ∧
    Core.ObeysStepFrom id Model.rawStepWf
      Model.execPosixStep Model.allowedPosixStep Model.rawStepWf
      Internal.mkRawBundle Model.execPkgStep Model.allowedPkgStep :=
  ⟨mapRawError_obeys, mkRawBundle_obeys⟩

private theorem modelStatePosixOps_obeys :
    Core.ObeysStepId Model.rawStepWf
      (Model.execPosixStep Model.modelStatePosixOps) Model.allowedPosixStep := by
  intro s req _
  cases req <;> exact ⟨rfl, rfl⟩

/-- Concrete non-vacuity witness instantiating `obeys_model` over `Model.modelStatePosixOps`. -/
theorem obeys_model_nonvacuous :
    Core.ObeysStepId Model.rawStepWf
      (Model.execPkgStep (Internal.mkRawBundle Model.modelStatePosixOps)) Model.allowedPkgStep :=
  obeys_model.2 id Model.modelStatePosixOps modelStatePosixOps_obeys

end LeanSwe.EnvVars.Raw.Proofs
