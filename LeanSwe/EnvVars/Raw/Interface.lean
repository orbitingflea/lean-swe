import LeanSwe.EnvVars.Raw.Types
import LeanSwe.EnvVars.Raw.Impl

namespace LeanSwe.EnvVars.Raw

@[extern "leanswe_envvars_getenv"]
private opaque rawGetEnvBytes (key : @& String) : BaseIO (Option ByteArray)

@[extern "leanswe_envvars_environ"]
private opaque rawListEnvironBytes : BaseIO (Array ByteArray)

private def posixRawOps : PosixRawOps :=
  { getEnvBytes := fun key => rawGetEnvBytes key
    listEnvironBytes := rawListEnvironBytes }

/-- Full OS environment primitive bundle including raw `listEnvironBytes`, backed by `c/envvars_shim.c`. -/
abbrev defaultOpsBase : RawEnvVarsBundle :=
  Internal.mkRawBundle posixRawOps

/-- Default minimal OS environment primitives backed by `c/envvars_shim.c` (`getenv(3)` and `environ(7)`). -/
def defaultOps : RawEnvVarsOps :=
  defaultOpsBase.toRawEnvVarsOpsM

/-- Convert a raw OS error record into a normalized `EnvVarsError` with non-empty message. -/
@[inline] def mapRawError (err : EnvVarsRawError) : EnvVarsError :=
  defaultOps.mapRawError err

/-- Look up a single environment variable via `getenv(3)` and Lean UTF-8 decoding without upper-layer `.invalidKey` errors. -/
@[inline] def getEnv (key : String) : IO (Except EnvVarsRawError (Option String)) :=
  defaultOps.getEnv key

/-- List all `(key, value)` environment entries from `environ(7)` in order via Lean `'='` splitting and UTF-8 decoding. -/
@[inline] def listEnv : IO (Except EnvVarsRawError (Array (String × String))) :=
  defaultOps.listEnv

/-- Snapshot raw NUL-free byte entries directly from `environ(7)` in order without UTF-8 decoding. -/
@[inline] def listEnvironBytes : IO (Array ByteArray) :=
  defaultOpsBase.listEnvironBytes

private theorem baseIO_liftM_ok {α : Type} (act : BaseIO α) (w : Void IO.RealWorld) :
    ∃ a w', (liftM act : IO α) w = EST.Out.ok a w' := by
  simp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, BaseIO.toEIO]
  cases act w with
  | mk a s => exact ⟨a, s, rfl⟩

private theorem io_bind_match {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld) :
    (act >>= k) w =
      match act w with
      | EST.Out.ok a w' => k a w'
      | EST.Out.error ex w' => EST.Out.error ex w' := by
  change EST.bind act k w = _
  unfold EST.bind
  cases act w <;> rfl

private theorem decodeEnvironAcc_err_invalidEncoding
    (accRev : List (String × String)) (entries : List ByteArray) (err : EnvVarsRawError)
    (h : Internal.decodeEnvironAcc accRev entries = .error err) :
    ∃ key? detail, err = .invalidEncoding key? detail := by
  induction entries generalizing accRev with
  | nil => simp [Internal.decodeEnvironAcc] at h
  | cons entry rest ih =>
    unfold Internal.decodeEnvironAcc at h
    cases hs : Internal.splitFirstEqBytes entry with
    | none =>
      rw [hs] at h
      exact ih accRev h
    | some kv =>
      rcases kv with ⟨kBytes, vBytes⟩
      rw [hs] at h
      dsimp only at h
      cases hk : String.fromUTF8? kBytes with
      | none =>
        rw [hk] at h
        injection h with he
        exact ⟨none, _, he.symm⟩
      | some k =>
        rw [hk] at h
        dsimp only at h
        cases hv : String.fromUTF8? vBytes with
        | none =>
          rw [hv] at h
          injection h with he
          exact ⟨some k, _, he.symm⟩
        | some v =>
          rw [hv] at h
          exact ih ((k, v) :: accRev) h

/-- `defaultOps.getEnv` never throws an uncaught `IO.Error` and only reports `.invalidEncoding` on failure. -/
theorem defaultOps_getEnv_res (key : String) (w : Void IO.RealWorld) :
    (∃ a w', defaultOps.getEnv key w = EST.Out.ok (Except.ok a) w') ∨
    (∃ key? detail w', defaultOps.getEnv key w = EST.Out.ok (Except.error (.invalidEncoding key? detail)) w') := by
  unfold defaultOps defaultOpsBase Internal.mkRawBundle Internal.mkRawOps posixRawOps
  dsimp only
  by_cases hpk : Internal.isValidPosixKey key
  · simp only [hpk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [io_bind_match]
    rcases baseIO_liftM_ok (rawGetEnvBytes key) w with ⟨mb, w1, hG⟩
    rw [hG]
    cases mb with
    | none => exact Or.inl ⟨none, w1, rfl⟩
    | some bs =>
      dsimp only
      cases String.fromUTF8? bs with
      | some s => exact Or.inl ⟨some s, w1, rfl⟩
      | none => exact Or.inr ⟨some key, _, w1, rfl⟩
  · simp only [hpk, Bool.not_false, ↓reduceIte]
    exact Or.inl ⟨none, w, rfl⟩

/-- `defaultOps.listEnv` never throws an uncaught `IO.Error` and only reports `.invalidEncoding` on failure. -/
theorem defaultOps_listEnv_res (w : Void IO.RealWorld) :
    (∃ a w', defaultOps.listEnv w = EST.Out.ok (Except.ok a) w') ∨
    (∃ key? detail w', defaultOps.listEnv w = EST.Out.ok (Except.error (.invalidEncoding key? detail)) w') := by
  unfold defaultOps defaultOpsBase Internal.mkRawBundle Internal.mkRawOps posixRawOps
  dsimp only
  rw [io_bind_match]
  rcases baseIO_liftM_ok rawListEnvironBytes w with ⟨entries, w1, hL⟩
  rw [hL]
  dsimp only
  cases hd : Internal.decodeEnvironAcc [] entries.toList with
  | ok xs =>
    simp only [Except.map]
    exact Or.inl ⟨xs.toArray, w1, rfl⟩
  | error err =>
    rcases decodeEnvironAcc_err_invalidEncoding [] entries.toList err hd with ⟨k?, d, rfl⟩
    simp only [Except.map]
    exact Or.inr ⟨k?, d, w1, rfl⟩

/-- `defaultOps.mapRawError (.invalidEncoding key? detail)` always has `.kind = .invalidEncoding`. -/
theorem defaultOps_mapRawError_invalidEncoding_kind (key? : Option String) (detail : String) :
    (defaultOps.mapRawError (.invalidEncoding key? detail)).kind = .invalidEncoding :=
  rfl

/-- `defaultOps.getEnv` never throws an uncaught `IO.Error`. -/
theorem defaultOps_getEnv_never_throws (key : String) (w : Void IO.RealWorld) :
    ∃ res w', defaultOps.getEnv key w = EST.Out.ok res w' := by
  rcases defaultOps_getEnv_res key w with ⟨a, w', h⟩ | ⟨k?, d, w', h⟩
  · exact ⟨.ok a, w', h⟩
  · exact ⟨.error (.invalidEncoding k? d), w', h⟩

/-- `defaultOps.listEnv` never throws an uncaught `IO.Error`. -/
theorem defaultOps_listEnv_never_throws (w : Void IO.RealWorld) :
    ∃ res w', defaultOps.listEnv w = EST.Out.ok res w' := by
  rcases defaultOps_listEnv_res w with ⟨a, w', h⟩ | ⟨k?, d, w', h⟩
  · exact ⟨.ok a, w', h⟩
  · exact ⟨.error (.invalidEncoding k? d), w', h⟩

end LeanSwe.EnvVars.Raw
