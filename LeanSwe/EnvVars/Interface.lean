import LeanSwe.EnvVars.Types
import LeanSwe.EnvVars.Impl
import LeanSwe.EnvVars.Raw.Interface

namespace LeanSwe.EnvVars

/-- Default `EnvVarsApi` backed by `LeanSwe.EnvVars.Raw.defaultOps`. -/
def defaultApi : EnvVarsApi :=
  Internal.mkApiM Raw.defaultOps

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
  unfold defaultApi Internal.mkApiM
  dsimp only
  by_cases hk : Internal.isValidKey key
  · simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [io_bind_match]
    rcases Raw.defaultOps_getEnv_never_throws key w with ⟨r, w1, hr⟩
    rw [hr]
    cases r with
    | error err => exact ⟨.error (Raw.defaultOps.mapRawError err), w1, rfl⟩
    | ok val => exact ⟨.ok val, w1, rfl⟩
  · simp only [hk, Bool.not_false, ↓reduceIte]
    exact ⟨_, w, rfl⟩

/-- `defaultApi.listEnv` never throws an uncaught `IO.Error`. -/
theorem defaultApi_listEnv_never_throws (w : Void IO.RealWorld) :
    ∃ res w', defaultApi.listEnv w = EST.Out.ok res w' := by
  unfold defaultApi Internal.mkApiM
  dsimp only
  rw [io_bind_match]
  rcases Raw.defaultOps_listEnv_never_throws w with ⟨r, w1, hr⟩
  rw [hr]
  cases r with
  | error err => exact ⟨.error (Raw.defaultOps.mapRawError err), w1, rfl⟩
  | ok entries => exact ⟨.ok entries, w1, rfl⟩

end LeanSwe.EnvVars
