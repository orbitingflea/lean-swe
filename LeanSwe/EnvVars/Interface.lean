import LeanSwe.EnvVars.Types
import LeanSwe.EnvVars.Impl

namespace LeanSwe.EnvVars

@[extern "leanswe_envvars_getenv"]
private opaque rawGetEnvBytes (key : @& String) : BaseIO (Option ByteArray)

@[extern "leanswe_envvars_environ"]
private opaque rawListEnvironBytes : BaseIO (Array ByteArray)

private def posixRawOps : PosixRawOps :=
  { getEnvBytes := fun key => rawGetEnvBytes key
    listEnvironBytes := rawListEnvironBytes }

/-- Default `EnvVarsApi` backed directly by `c/envvars_shim.c` (`getenv(3)` and `environ(7)`). -/
def defaultApi : EnvVarsApi :=
  Internal.mkApiM posixRawOps

/-- Convert a raw OS error record into a normalized `EnvVarsError` with non-empty message. -/
@[inline] def mapRawError (err : EnvVarsRawError) : EnvVarsError :=
  defaultApi.mapRawError err

/-- Validate `key` and look up its value in the process environment. -/
@[inline] def getEnv (key : String) : IO (Except EnvVarsError (Option String)) :=
  defaultApi.getEnv key

/-- Return all `(key, value)` entries from the process environment. -/
@[inline] def listEnv : IO (Except EnvVarsError (Array (String × String))) :=
  defaultApi.listEnv

/-- Return the non-empty `HOME` directory string, or `.notFound` if unset or empty. -/
@[inline] def homeDir : IO (Except EnvVarsError String) :=
  defaultApi.homeDir

/-- Snapshot raw NUL-free byte entries directly from `environ(7)` in order without UTF-8 decoding. -/
@[inline] def listEnvironBytes : IO (Array ByteArray) :=
  defaultApi.listEnvironBytes

/-- Split a POSIX `:`-delimited search path, dropping empty segments (`""` yields `#[]`). -/
@[inline] def splitSearchPath (path : String) : Array String :=
  defaultApi.splitSearchPath path

private theorem io_bind_match {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld) :
    (act >>= k) w =
      match act w with
      | EST.Out.ok a w' => k a w'
      | EST.Out.error ex w' => EST.Out.error ex w' := by
  change EST.bind act k w = _
  unfold EST.bind
  cases act w <;> rfl

/-- `defaultApi.getEnv` never throws an uncaught `IO.Error`. -/
theorem defaultApi_getEnv_never_throws (key : String) (w : Void IO.RealWorld) :
    ∃ res w', defaultApi.getEnv key w = EST.Out.ok res w' := by
  unfold defaultApi Internal.mkApiM posixRawOps
  dsimp only
  by_cases hk : Internal.isValidKey key
  · simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [io_bind_match]
    have hLift : ∃ a w', (liftM (rawGetEnvBytes key) : IO (Option ByteArray)) w = EST.Out.ok a w' := by
      simp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, BaseIO.toEIO]
      cases rawGetEnvBytes key w with
      | mk a s => exact ⟨a, s, rfl⟩
    rcases hLift with ⟨mb, w1, hr⟩
    rw [hr]
    cases mb with
    | none => exact ⟨.ok none, w1, rfl⟩
    | some bs =>
      dsimp only
      cases String.fromUTF8? bs with
      | some s => exact ⟨.ok (some s), w1, rfl⟩
      | none => exact ⟨_, w1, rfl⟩
  · simp only [hk, Bool.not_false, ↓reduceIte]
    exact ⟨_, w, rfl⟩

/-- `defaultApi.listEnv` never throws an uncaught `IO.Error`. -/
theorem defaultApi_listEnv_never_throws (w : Void IO.RealWorld) :
    ∃ res w', defaultApi.listEnv w = EST.Out.ok res w' := by
  unfold defaultApi Internal.mkApiM posixRawOps
  dsimp only
  rw [io_bind_match]
  have hLift : ∃ a w', (liftM rawListEnvironBytes : IO (Array ByteArray)) w = EST.Out.ok a w' := by
    simp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, BaseIO.toEIO]
    cases rawListEnvironBytes w with
    | mk a s => exact ⟨a, s, rfl⟩
  rcases hLift with ⟨entries, w1, hr⟩
  rw [hr]
  exact ⟨_, w1, rfl⟩

end LeanSwe.EnvVars
