import Core.Assumptions
import Core.Obeys
import LeanSwe.EnvVars.Model
import LeanSwe.EnvVars.Interface
import LeanSwe.EnvVars.Raw.Model.Assumptions

namespace LeanSwe.EnvVars.Proofs

open Core

private theorem hasInvalidKeyChar_iff (cs : List Char) :
    Internal.hasInvalidKeyChar cs = true ↔ '=' ∈ cs ∨ Char.ofNat 0 ∈ cs := by
  induction cs with
  | nil => simp [Internal.hasInvalidKeyChar]
  | cons c rest ih =>
    simp only [Internal.hasInvalidKeyChar, Bool.or_eq_true, beq_iff_eq, List.mem_cons, ih]
    constructor
    · intro h
      rcases h with (h1 | h2) | h3 | h4
      · exact Or.inl (Or.inl h1.symm)
      · exact Or.inr (Or.inl h2.symm)
      · exact Or.inl (Or.inr h3)
      · exact Or.inr (Or.inr h4)
    · intro h
      rcases h with (h1 | h2) | (h3 | h4)
      · exact Or.inl (Or.inl h1.symm)
      · exact Or.inr (Or.inl h2)
      · exact Or.inl (Or.inr h3.symm)
      · exact Or.inr (Or.inr h4)

private theorem isValidKey_true_iff (key : String) :
    Internal.isValidKey key = true ↔ key ≠ "" ∧ '=' ∉ key.toList ∧ Char.ofNat 0 ∉ key.toList := by
  unfold Internal.isValidKey
  rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true', List.isEmpty_eq_false_iff]
  have hmem : Internal.hasInvalidKeyChar key.toList = false ↔
      '=' ∉ key.toList ∧ Char.ofNat 0 ∉ key.toList := by
    constructor
    · intro hf
      refine ⟨?_, ?_⟩
      · intro heq
        have ht := (hasInvalidKeyChar_iff key.toList).mpr (Or.inl heq)
        rw [hf] at ht
        cases ht
      · intro hnul
        have ht := (hasInvalidKeyChar_iff key.toList).mpr (Or.inr hnul)
        rw [hf] at ht
        cases ht
    · intro ⟨h1, h2⟩
      cases h : Internal.hasInvalidKeyChar key.toList with
      | false => rfl
      | true =>
        rcases (hasInvalidKeyChar_iff key.toList).mp h with heq | hnul
        · exact absurd heq h1
        · exact absurd hnul h2
  have hne : key.toList ≠ [] ↔ key ≠ "" := by
    constructor
    · intro h heq
      subst heq
      exact h rfl
    · intro h hl
      apply h
      rw [← String.ofList_toList (s := key), hl]
  rw [hmem, hne]

/-- Upper-layer consumer theorem for `Raw.assume_envvarsraw_listEnv_consistentWithGetEnv`:
    whenever a `RawEnvVarsOpsM Id` backend satisfies the formal listing/lookup consistency assumption,
    `Internal.mkApiM raw` preserves key well-formedness on `listEnv` and agrees with `listEnv` on valid `getEnv` keys. -/
theorem envvars_listEnv_consistent_with_getEnv
    (raw : RawEnvVarsOpsM Id)
    (hcons : AllPass (Raw.assume_envvarsraw_listEnv_consistentWithGetEnv raw))
    (pairs : Array (String × String))
    (hlist : (Internal.mkApiM raw).listEnv = .ok pairs)
    (k : String)
    (hk : k ≠ "" ∧ '=' ∉ k.toList ∧ Char.ofNat 0 ∉ k.toList) :
    (pairs.toList.all (fun p => !p.1.isEmpty && !('=' ∈ p.1.toList) && !(Char.ofNat 0 ∈ p.1.toList)) = true) ∧
    ((Internal.mkApiM raw).getEnv k = .ok ((pairs.toList.find? (fun p => p.1 == k)).map Prod.snd)) := by
  have hrawList : raw.listEnv = .ok pairs := by
    simp only [Internal.mkApiM, bind] at hlist
    cases hrl : raw.listEnv with
    | error err => rw [hrl] at hlist; simp [pure] at hlist
    | ok xs => rw [hrl] at hlist; simp [pure] at hlist; injection hlist with hEq; subst hEq; rfl
  rcases hcons pairs k hrawList hk with ⟨⟨hall, hget⟩, _⟩
  have hvalid : Internal.isValidKey k = true := (isValidKey_true_iff k).mpr hk
  refine ⟨hall, ?_⟩
  simp only [Internal.mkApiM, hvalid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, pure]
  rw [hget]

private theorem io_bind_ok {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld)
    {a : α} {w' : Void IO.RealWorld} (h : act w = EST.Out.ok a w') :
    (act >>= k) w = k a w' := by
  change EST.bind act k w = k a w'
  simp [EST.bind, h]

private theorem io_pure_eq {α : Type} (a : α) (w : Void IO.RealWorld) :
    (pure a : IO α) w = EST.Out.ok a w := rfl

private theorem raw_getEnv_res (key : String) (w : Void IO.RealWorld) :
    (∃ a w', Raw.defaultOps.getEnv key w = EST.Out.ok (Except.ok a) w') ∨
    (∃ key? detail w', Raw.defaultOps.getEnv key w = EST.Out.ok (Except.error (.invalidEncoding key? detail)) w') :=
  Raw.defaultOps_getEnv_res key w

private theorem raw_listEnv_res (w : Void IO.RealWorld) :
    (∃ a w', Raw.defaultOps.listEnv w = EST.Out.ok (Except.ok a) w') ∨
    (∃ key? detail w', Raw.defaultOps.listEnv w = EST.Out.ok (Except.error (.invalidEncoding key? detail)) w') :=
  Raw.defaultOps_listEnv_res w

private theorem mapRawError_invalidEncoding_kind (key? : Option String) (detail : String) :
    (Raw.defaultOps.mapRawError (.invalidEncoding key? detail)).kind = .invalidEncoding :=
  Raw.defaultOps_mapRawError_invalidEncoding_kind key? detail

private theorem envvars_getEnv_never_of (f : Raw.EnvVarsErrorKind)
    (hf1 : f ≠ .invalidKey) (hf2 : f ≠ .invalidEncoding)
    (key : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.EnvVarsError.kind f (EnvVars.getEnv key) w := by
  unfold Core.NeverErrorKindIO EnvVars.getEnv EnvVars.defaultApi Internal.mkApiM
  dsimp only
  by_cases hk : Internal.isValidKey key
  · simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rcases raw_getEnv_res key w with ⟨a, w', hok⟩ | ⟨k?, d, w', herr⟩
    · rw [io_bind_ok _ _ w hok]; dsimp only; rw [io_pure_eq]; trivial
    · rw [io_bind_ok _ _ w herr]; dsimp only; rw [io_pure_eq]
      intro heq
      exact hf2 (heq ▸ mapRawError_invalidEncoding_kind k? d)
  · simp only [hk, Bool.not_false, ↓reduceIte]
    rw [io_pure_eq]
    exact hf1.symm

private theorem envvars_listEnv_never_of (f : Raw.EnvVarsErrorKind)
    (hf : f ≠ .invalidEncoding) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.EnvVarsError.kind f EnvVars.listEnv w := by
  unfold Core.NeverErrorKindIO EnvVars.listEnv EnvVars.defaultApi Internal.mkApiM
  dsimp only
  rcases raw_listEnv_res w with ⟨a, w', hok⟩ | ⟨k?, d, w', herr⟩
  · rw [io_bind_ok _ _ w hok]; dsimp only; rw [io_pure_eq]; trivial
  · rw [io_bind_ok _ _ w herr]; dsimp only; rw [io_pure_eq]
    intro heq
    exact hf (heq ▸ mapRawError_invalidEncoding_kind k? d)

private theorem envvars_homeDir_never_of (f : Raw.EnvVarsErrorKind)
    (hf1 : f ≠ .notFound) (hf2 : f ≠ .invalidEncoding) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.EnvVarsError.kind f EnvVars.homeDir w := by
  unfold Core.NeverErrorKindIO EnvVars.homeDir EnvVars.defaultApi Internal.mkApiM
  dsimp only
  rcases raw_getEnv_res "HOME" w with ⟨a, w', hok⟩ | ⟨k?, d, w', herr⟩
  · rw [io_bind_ok _ _ w hok]
    cases a with
    | none => dsimp only; rw [io_pure_eq]; exact hf1.symm
    | some s =>
      by_cases hs : s = ""
      · subst hs; simp [io_pure_eq]; exact hf1.symm
      · simp [io_pure_eq]
  · rw [io_bind_ok _ _ w herr]; dsimp only; rw [io_pure_eq]
    intro heq
    exact hf2 (heq ▸ mapRawError_invalidEncoding_kind k? d)

/-- Proof that `EnvVars.getEnv` never returns `.notFound`. -/
theorem envvars_getEnv_never_notFound (key : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.EnvVarsError.kind .notFound (EnvVars.getEnv key) w :=
  envvars_getEnv_never_of .notFound (by decide) (by decide) key w

/-- Proof that `EnvVars.getEnv` never returns `.ioError`. -/
theorem envvars_getEnv_never_ioError (key : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.EnvVarsError.kind .ioError (EnvVars.getEnv key) w :=
  envvars_getEnv_never_of .ioError (by decide) (by decide) key w

/-- Proof that `EnvVars.listEnv` never returns `.invalidKey`. -/
theorem envvars_listEnv_never_invalidKey (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.EnvVarsError.kind .invalidKey EnvVars.listEnv w :=
  envvars_listEnv_never_of .invalidKey (by decide) w

/-- Proof that `EnvVars.listEnv` never returns `.notFound`. -/
theorem envvars_listEnv_never_notFound (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.EnvVarsError.kind .notFound EnvVars.listEnv w :=
  envvars_listEnv_never_of .notFound (by decide) w

/-- Proof that `EnvVars.listEnv` never returns `.ioError`. -/
theorem envvars_listEnv_never_ioError (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.EnvVarsError.kind .ioError EnvVars.listEnv w :=
  envvars_listEnv_never_of .ioError (by decide) w

/-- Proof that `EnvVars.homeDir` never returns `.invalidKey`. -/
theorem envvars_homeDir_never_invalidKey (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.EnvVarsError.kind .invalidKey EnvVars.homeDir w :=
  envvars_homeDir_never_of .invalidKey (by decide) (by decide) w

/-- Proof that `EnvVars.homeDir` never returns `.ioError`. -/
theorem envvars_homeDir_never_ioError (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.EnvVarsError.kind .ioError EnvVars.homeDir w :=
  envvars_homeDir_never_of .ioError (by decide) (by decide) w

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
    Raw.Model.hasInvalidKeyCharModel cs = Internal.hasInvalidKeyChar cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [Raw.Model.hasInvalidKeyCharModel, Internal.hasInvalidKeyChar, ih]
    cases (c == '=' || c == Char.ofNat 0) <;> rfl

private theorem isEmpty_iff_toList_isEmpty (s : String) :
    s.isEmpty = s.toList.isEmpty := by
  cases h : s.toList with
  | nil =>
    have hs : s = "" := by rw [← String.ofList_toList (s := s), h]
    subst hs
    rfl
  | cons c cs =>
    have hne : s ≠ "" := fun hs => by subst hs; cases h
    cases he : s.isEmpty with
    | false => rfl
    | true => exact absurd (String.isEmpty_iff.mp he) hne

private theorem isValidKey_eq_model (key : String) :
    Internal.isValidKey key = Raw.Model.isValidPosixKeyModel key := by
  simp [Internal.isValidKey, Raw.Model.isValidPosixKeyModel, isEmpty_iff_toList_isEmpty,
    hasInvalidKeyCharModel_eq]

private theorem mapRawError_eq_model (err : EnvVarsRawError) :
    LeanSwe.EnvVars.mapRawError err = Model.mapRawErrorModel err := by
  cases err <;> rfl

private theorem obeysStepFrom_mkApiM :
    Core.ObeysStepFrom id Model.rawStepWf Model.execRawStep Model.allowedRawStep
      Model.rawStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj raw hRaw w req _
  have hMap : ∀ e, raw.mapRawError e = Raw.Model.mapRawErrorModel e := fun e => by
    have h := hRaw w (.mapRawError e) rfl
    exact h.2
  cases req with
  | getEnv key =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Functor.map, StateT.map, Bind.bind, StateT.bind,
      Pure.pure, StateT.pure, StateT.run, Function.comp]
    rw [isValidKey_eq_model]
    cases hk : Raw.Model.isValidPosixKeyModel key with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, StateT.pure, Pure.pure, Model.allowedPkgStep,
        Model.getEnvModel, id]
      rw [hk]
      simp
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.bind]
      have hStep := hRaw w (.getEnv key) rfl
      dsimp only [Model.execRawStep, Functor.map, StateT.map, Bind.bind, StateT.bind,
        Pure.pure, StateT.pure, StateT.run, Model.allowedRawStep] at hStep
      cases hg : raw.getEnv key w with
      | mk res w' =>
        simp only [hg] at hStep ⊢
        rcases hStep with ⟨hw', hres⟩
        subst hres
        cases hm : Raw.Model.rawGetEnvModel (proj w) key with
        | error err =>
          simp [Bind.bind, StateT.pure, Pure.pure, Model.allowedPkgStep, Model.getEnvModel,
            Except.mapError, hk, hm, hMap, hw']
        | ok val =>
          simp [Bind.bind, StateT.pure, Pure.pure, Model.allowedPkgStep, Model.getEnvModel,
            Except.mapError, hk, hm, hw']
  | listEnv =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Functor.map, StateT.map, Bind.bind, StateT.bind,
      Pure.pure, StateT.pure, StateT.run, Function.comp]
    have hStep := hRaw w .listEnv rfl
    dsimp only [Model.execRawStep, Functor.map, StateT.map, Bind.bind, StateT.bind,
      Pure.pure, StateT.pure, StateT.run, Model.allowedRawStep] at hStep
    cases hl : raw.listEnv w with
    | mk res w' =>
      simp only [hl] at hStep ⊢
      rcases hStep with ⟨hw', hres⟩
      subst hres
      cases hm : Raw.Model.rawListEnvModel (proj w) with
      | error err =>
        simp only [StateT.pure, Pure.pure, Model.allowedPkgStep, Model.listEnvModel, Except.mapError, id]
        rw [hm, hMap, hw']
        exact ⟨rfl, rfl⟩
      | ok entries =>
        simp only [StateT.pure, Pure.pure, Model.allowedPkgStep, Model.listEnvModel, Except.mapError, id]
        rw [hm, hw']
        exact ⟨rfl, rfl⟩
  | homeDir =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Functor.map, StateT.map, Bind.bind, StateT.bind,
      Pure.pure, StateT.pure, StateT.run, Function.comp]
    have hStep := hRaw w (.getEnv "HOME") rfl
    dsimp only [Model.execRawStep, Functor.map, StateT.map, Bind.bind, StateT.bind,
      Pure.pure, StateT.pure, StateT.run, Model.allowedRawStep] at hStep
    cases hg : raw.getEnv "HOME" w with
    | mk res w' =>
      simp only [hg] at hStep ⊢
      rcases hStep with ⟨hw', hres⟩
      subst hres
      cases hm : Raw.Model.rawGetEnvModel (proj w) "HOME" with
      | error err =>
        simp only [StateT.pure, Pure.pure, Model.allowedPkgStep, Model.homeDirModel, id]
        rw [hm, hMap, hw']
        exact ⟨rfl, rfl⟩
      | ok v? =>
        cases v? with
        | none =>
          simp only [StateT.pure, Pure.pure, Model.allowedPkgStep, Model.homeDirModel, id]
          rw [hm, hw']
          exact ⟨rfl, rfl⟩
        | some v =>
          by_cases hv : v = ""
          · subst hv
            simp [StateT.pure, Pure.pure, Model.allowedPkgStep, Model.homeDirModel, hm, hw']
          · simp [StateT.pure, Pure.pure, Model.allowedPkgStep, Model.homeDirModel, hm, hw']

/-- Full public `Interface` obedience of `LeanSwe.EnvVars` against `LeanSwe.EnvVars.Model`. -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.EnvVars.mapRawError Model.mapRawErrorModel ∧
    Core.ObeysPureEq LeanSwe.EnvVars.splitSearchPath Model.splitSearchPathModel ∧
    Core.ObeysStepFrom id Model.rawStepWf Model.execRawStep Model.allowedRawStep
      Model.rawStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep :=
  ⟨mapRawError_eq_model,
   fun path => (splitSearchPathModel_eq path).symm,
   obeysStepFrom_mkApiM⟩

end LeanSwe.EnvVars.Proofs
