import Core.Obeys
import LeanSwe.PostFork.Types
import LeanSwe.PostFork.Impl
import LeanSwe.PostFork.Interface
import LeanSweProofs.PostFork.Model
import LeanSweProofs.PostFork.Model.Refines

/-!
# PostFork Kernel Proof Suite

Proves pure equivalence between `LeanSwe.PostFork.Impl.Internal` validation/decoding helpers
and `LeanSwe.PostFork.Model`, together with canonical `Core.ObeysStepFrom` capability refinement
`obeys_model` and its non-vacuity witness `obeys_model_nonvacuous`.
-/

namespace LeanSwe.PostFork.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork
open LeanSwe.PostFork.Impl
open LeanSwe.PostFork.Model

private theorem stateM_map_run {W α β : Type} (f : α → β) (m : StateM W α) (w : W) :
    (f <$> m).run w = (f (m.run w).1, (m.run w).2) := rfl

private theorem stateM_bind_run {W α β : Type} (m : StateM W α) (k : α → StateM W β) (w : W) :
    (m >>= k).run w = (k (m.run w).1).run (m.run w).2 := rfl

private theorem stateM_pure_run {W α : Type} (a : α) (w : W) :
    (pure a : StateM W α).run w = (a, w) := rfl

private theorem fdRefIsNonneg_eq {fd : Type} (r : FdRef fd) :
    Internal.fdRefIsNonnegImpl r = FdRef.isNonneg r := by
  cases r <;> rfl

private theorem fdRefIsRawStdioSlot_eq {fd : Type} (r : FdRef fd) :
    Internal.fdRefIsRawStdioSlotImpl r = FdRef.isRawStdioSlot r := by
  cases r <;> rfl

private theorem fdRefSameRaw_eq {fd : Type} (a b : FdRef fd) :
    Internal.fdRefSameRawImpl a b = FdRef.sameRaw a b := by
  cases a <;> cases b <;> rfl

private theorem argTokenIsValid_eq {fd : Type} (tok : ArgToken fd) :
    Internal.argTokenIsValidImpl tok = ArgToken.isValid tok := by
  cases tok
  rfl

private theorem keepFds_eq {fd : Type} (pol : FdPolicy fd) :
    Internal.keepFdsImpl pol = FdPolicy.keepFds pol := by
  cases pol <;> rfl

/-- `Internal.validateSpecImpl` equals `Model.validateSpec` identically on every `ChildSpecM`. -/
theorem validateSpecImpl_eq_model {fd : Type} (spec : ChildSpecM fd) :
    Internal.validateSpecImpl spec = Model.validateSpec spec := by
  unfold Internal.validateSpecImpl Model.validateSpec
  have hArg : (Internal.argTokenIsValidImpl : ArgToken fd → Bool) = ArgToken.isValid :=
    funext argTokenIsValid_eq
  have hNonneg : (Internal.fdRefIsNonnegImpl : FdRef fd → Bool) = FdRef.isNonneg :=
    funext fdRefIsNonneg_eq
  have hSlot : (Internal.fdRefIsRawStdioSlotImpl : FdRef fd → Bool) = FdRef.isRawStdioSlot :=
    funext fdRefIsRawStdioSlot_eq
  have hSame : (Internal.fdRefSameRawImpl : FdRef fd → FdRef fd → Bool) = FdRef.sameRaw :=
    funext fun a => funext fun b => fdRefSameRaw_eq a b
  have hEnv : Internal.isValidEnvBindingImpl = Model.isValidEnvBinding := rfl
  have hRawEnv : Internal.isValidRawEnvEntryImpl = Model.isValidRawEnvEntry := rfl
  have hNul : Internal.hasEmbeddedNulStrImpl = Model.hasEmbeddedNulStr := rfl
  rw [hArg, hNonneg, hSlot, hSame, hEnv, hRawEnv, hNul, keepFds_eq]
  rfl

/-- `Internal.decodeRawSpawnErrImpl` equals `Model.decodeRawSpawnErr` on every `RawSpawnErr`. -/
theorem decodeRawSpawnErrImpl_eq_model (e : RawSpawnErr) :
    Internal.decodeRawSpawnErrImpl e = Model.decodeRawSpawnErr e := by
  cases e <;> rfl

private theorem normalizeErrnoImpl_valid (e : Errno) :
    Model.validHostErrnoProp (Internal.normalizeErrnoImpl e) := by
  unfold Internal.normalizeErrnoImpl Model.validHostErrnoProp
  split
  · rename_i h
    exact ⟨of_decide_eq_true ((Bool.and_eq_true _ _).mp h).1,
           of_decide_eq_true ((Bool.and_eq_true _ _).mp h).2⟩
  · exact ⟨by decide, by decide⟩

private theorem decodeRawSpawnErrImpl_valid {e : RawSpawnErr} (he : Model.validRawSpawnErrProp e) :
    Model.validRuntimeErrProp (Internal.decodeRawSpawnErrImpl e) := by
  cases e with
  | sys code =>
    left
    dsimp only [Internal.decodeRawSpawnErrImpl]
    refine ⟨rfl, rfl, rfl, Internal.normalizeErrnoImpl code, rfl, normalizeErrnoImpl_valid code⟩
  | child wst tag code =>
    right
    rcases he with ⟨hWst, _⟩
    dsimp only [Internal.decodeRawSpawnErrImpl]
    refine ⟨rfl, rfl, _, wst, rfl, rfl, rfl, hWst, ?_⟩
    cases Internal.failureStageOfTagImpl? tag with
    | none => simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]; exact ⟨by decide, by decide⟩
    | some _ => exact normalizeErrnoImpl_valid code

/-- Canonical `Core.ObeysStepFrom` capability refinement for `LeanSwe.PostFork`,
covering `Impl.Internal.mkHostOpsM` and the public `spawn` operation over `Model.HostStepState`. -/
theorem obeys_model :
    Core.ObeysStepFrom id Model.rawStepWf Model.execRawStep Model.allowedRawStep
      Model.rawStepWf Impl.Internal.mkHostOpsM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj raw hRaw w req hWf
  cases req with
  | spawn spec =>
    by_cases hv : Internal.validateSpecImpl spec = true
    · have hvM : Model.validateSpec spec = true := by rw [← validateSpecImpl_eq_model]; exact hv
      let t := Internal.stdioTriple spec.stdio
      let rReq : Model.RawStepReq :=
        .spawnRaw (Internal.flagsOfSpecImpl spec) t.1 t.2.1 t.2.2 spec.cwd spec.path
          (spec.argv.map Internal.argTokenTextImpl)
          (Internal.formatEnvEntriesBytesImpl spec.rawEnv spec.env)
      have hStep := hRaw w rReq hWf
      dsimp only [Model.execRawStep, Model.allowedRawStep, Function.comp, id, rReq] at hStep
      rw [stateM_map_run] at hStep
      dsimp only [Model.execPkgStep, Internal.mkHostOpsM, Internal.mkHostOps, Model.allowedPkgStep,
        Function.comp, id]
      rw [stateM_map_run]
      simp only [hv, hvM, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run]
      cases hCall : (raw.spawnRaw (Internal.flagsOfSpecImpl spec) t.1 t.2.1 t.2.2 spec.cwd spec.path
          (spec.argv.map Internal.argTokenTextImpl)
          (Internal.formatEnvEntriesBytesImpl spec.rawEnv spec.env)).run w with
      | mk out w' =>
        rw [hCall] at hStep
        rcases hStep with ⟨hWf0, hWf1, hPost⟩
        cases out with
        | error rawErr =>
          rw [stateM_pure_run]
          exact ⟨hWf0, hWf1, decodeRawSpawnErrImpl_valid hPost⟩
        | ok pid =>
          rw [stateM_pure_run]
          refine ⟨hWf0, hWf1, hPost.1, hPost.2.1, ?_⟩
          cases spec.processGroup <;> rfl
    · have hvF : Internal.validateSpecImpl spec = false := Bool.eq_false_iff.mpr hv
      have hvMF : Model.validateSpec spec = false := by rw [← validateSpecImpl_eq_model]; exact hvF
      dsimp only [Model.execPkgStep, Internal.mkHostOpsM, Internal.mkHostOps, Model.allowedPkgStep,
        Function.comp, id]
      rw [stateM_map_run]
      simp only [hvF, hvMF, Bool.not_false, ↓reduceIte, stateM_pure_run]
      exact ⟨hWf, hWf, trivial, rfl, rfl, rfl, rfl⟩

private theorem modelRawOps_obeys_allowedRawStep :
    Core.ObeysStep id Model.rawStepWf (Model.execRawStep Model.modelRawOps) Model.allowedRawStep := by
  intro s req hWf
  cases req with
  | spawnRaw _ _ _ _ _ _ _ _ =>
    have hH : s.healthyHost = true := ((Bool.and_eq_true _ _).mp hWf).1
    have hWf' : Model.rawStepWf { s with lastPid := 100 } = true := by
      simp [Model.rawStepWf, hH, Model.maxLinuxPid]
    exact ⟨hWf, hWf', by decide, by decide, rfl⟩

/-- Non-vacuity witness showing both `Model.rawStepWf` and the raw `RawSpawnOpsM`
contract in `obeys_model` are inhabited. -/
theorem obeys_model_nonvacuous :
    (∃ s : Model.HostStepState, Model.rawStepWf s = true) ∧
    (∃ raw : Model.RawHostOpsM (StateM Model.HostStepState),
      Core.ObeysStep id Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep) :=
  ⟨⟨{}, rfl⟩, ⟨Model.modelRawOps, modelRawOps_obeys_allowedRawStep⟩⟩

end LeanSwe.PostFork.Proofs
