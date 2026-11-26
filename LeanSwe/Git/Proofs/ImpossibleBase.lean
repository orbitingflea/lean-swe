import Core.Assumptions
import LeanSwe.EnvVars.Interface
import LeanSwe.Process.Interface
import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open Core
open LeanSwe.Git

/-- Unfold `IO` pure on a world token. -/
theorem io_pure_eq {α : Type} (a : α) (w : Void IO.RealWorld) :
    (pure a : IO α) w = EST.Out.ok a w := rfl

/-- Unfold `IO` bind on a world token. -/
theorem io_bind_eq {α β : Type} (x : IO α) (f : α → IO β) (w : Void IO.RealWorld) :
    (x >>= f) w =
      match x w with
      | EST.Out.ok a w' => f a w'
      | EST.Out.error e w' => EST.Out.error e w' := by
  change EST.bind x f w = _
  unfold EST.bind
  cases x w <;> rfl

/-- Simplify `IO` bind when the first action succeeds with `EST.Out.ok`. -/
theorem io_bind_ok {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld)
    {a : α} {w' : Void IO.RealWorld} (h : act w = EST.Out.ok a w') :
    (act >>= k) w = k a w' := by
  change EST.bind act k w = k a w'
  simp [EST.bind, h]

private theorem baseIO_liftM_never_throws {α : Type} (act : BaseIO α) (w : Void IO.RealWorld) :
    ∃ a w', (liftM act : IO α) w = EST.Out.ok a w' := by
  simp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, BaseIO.toEIO]
  cases act w with
  | mk a s => exact ⟨a, s, rfl⟩

private theorem mkRawOps_envvars_listEnv_never_throws
    (g : String → BaseIO (Option ByteArray)) (l : BaseIO (Array ByteArray))
    (w : Void IO.RealWorld) :
    ∃ res w',
      (LeanSwe.EnvVars.Internal.mkApiM
        (LeanSwe.EnvVars.Raw.Internal.mkRawOps (m := IO) {
          getEnvBytes := fun k => liftM (g k)
          listEnvironBytes := liftM l
        })).listEnv w = EST.Out.ok res w' := by
  dsimp only [LeanSwe.EnvVars.Internal.mkApiM, LeanSwe.EnvVars.Raw.Internal.mkRawOps]
  rw [io_bind_eq, io_bind_eq]
  rcases baseIO_liftM_never_throws l w with ⟨entries, w1, hL⟩
  rw [hL]
  dsimp only
  rw [io_pure_eq]
  cases LeanSwe.EnvVars.Raw.Internal.decodeEnvironAcc [] entries.toList with
  | ok xs => exact ⟨.ok xs.toArray, w1, rfl⟩
  | error e => exact ⟨.error (LeanSwe.EnvVars.Raw.Internal.mapRawError e), w1, rfl⟩

/-- `LeanSwe.EnvVars.defaultApi.listEnv` never throws an uncaught `IO.Error`. -/
theorem envvars_listEnv_never_throws (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.EnvVars.defaultApi.listEnv w = EST.Out.ok res w' := by
  apply mkRawOps_envvars_listEnv_never_throws

private theorem ioConc_tryCatch_ok {α : Type} (act : IO α) (w : Void IO.RealWorld) :
    ∃ r w', Core.ioConcOps.tryCatchMsg act w = EST.Out.ok r w' := by
  have heq : Core.ioConcOps.tryCatchMsg act w =
      EST.tryCatch (EST.bind act (fun a => EST.pure (.ok a)))
        (fun err => EST.pure (.error (toString err))) w := rfl
  rw [heq]; unfold EST.tryCatch EST.bind EST.pure
  cases act w <;> exact ⟨_, _, rfl⟩

private theorem ioCell_get_ok {S : Type} (r : IO.Ref S) (w : Void IO.RealWorld) :
    ∃ s w', (Core.ioStateCell r).get w = EST.Out.ok s w' := by
  change ∃ s w', (r.get : BaseIO S).toEIO w = EST.Out.ok s w'
  unfold BaseIO.toEIO
  cases (r.get : BaseIO S) w with | mk a s => exact ⟨a, s, rfl⟩

private theorem ioCell_mod_ok {S α : Type} (r : IO.Ref S) (f : S → α × S) (w : Void IO.RealWorld) :
    ∃ a w', (Core.ioStateCell r).modifyGet f w = EST.Out.ok a w' := by
  change ∃ a w', (r.modifyGet f : BaseIO α).toEIO w = EST.Out.ok a w'
  unfold BaseIO.toEIO
  cases (r.modifyGet f : BaseIO α) w with | mk a s => exact ⟨a, s, rfl⟩

/-- `LeanSwe.Process.defaultApi.run` never throws an uncaught `IO.Error`. -/
theorem process_run_never_throws (req : LeanSwe.Process.ExecRequest)
    (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Process.defaultApi.run req w = EST.Out.ok res w' := by
  have spawn_ok : ∀ (sys : LeanSwe.Process.Internal.ProcessSysCapsM IO)
      (r : IO.Ref (LeanSwe.Process.Internal.ProcCellS Core.ioConcOps.Ref Core.ioConcOps.TaskHandle))
      (ef : Nat) (rq : LeanSwe.Process.ExecRequest) (w0 : Void IO.RealWorld),
      ∃ res w', LeanSwe.Process.SysBridge.spawnConc sys Core.ioConcOps
        (@Core.ioStateCell (LeanSwe.Process.Internal.ProcCellS Core.ioConcOps.Ref Core.ioConcOps.TaskHandle) r)
        ef rq w0 = EST.Out.ok res w' := by
    intro sys r ef rq w0; unfold LeanSwe.Process.SysBridge.spawnConc
    rcases ioConc_tryCatch_ok _ w0 with ⟨tr, w1, h1⟩; rw [io_bind_ok _ _ _ h1]
    cases tr with
    | error _ => exact ⟨_, w1, rfl⟩
    | ok os => cases os with
      | error _ => exact ⟨_, w1, rfl⟩
      | ok _ => dsimp only; rcases ioCell_mod_ok r _ w1 with ⟨_, w2, h2⟩; rw [io_bind_ok _ _ _ h2]; exact ⟨_, w2, rfl⟩
  have await_ok : ∀ (sys : LeanSwe.Process.Internal.ProcessSysCapsM IO)
      (r : IO.Ref (LeanSwe.Process.Internal.ProcCellS Core.ioConcOps.Ref Core.ioConcOps.TaskHandle))
      (ef iof : Nat) (h : LeanSwe.Process.ProcessHandle) (stdin : ByteArray) (to? max? : Option Nat) (w0 : Void IO.RealWorld),
      ∃ res w', LeanSwe.Process.SysBridge.awaitOutputConc sys Core.ioConcOps
        (@Core.ioStateCell (LeanSwe.Process.Internal.ProcCellS Core.ioConcOps.Ref Core.ioConcOps.TaskHandle) r)
        ef iof h stdin to? max? w0 = EST.Out.ok res w' := by
    intro sys r ef iof h stdin to? max? w0; unfold LeanSwe.Process.SysBridge.awaitOutputConc
    rcases ioCell_mod_ok r _ w0 with ⟨tk, w1, h1⟩; rw [io_bind_ok _ _ _ h1]
    cases tk with
    | none => exact ⟨_, w1, rfl⟩
    | some tup =>
      rcases tup with ⟨_, _, _, _⟩; dsimp only
      rcases ioConc_tryCatch_ok _ w1 with ⟨tr, w2, h2⟩; rw [io_bind_ok _ _ _ h2]
      cases tr with
      | error _ => exact ⟨_, w2, rfl⟩
      | ok os => cases os with
        | error _ => exact ⟨_, w2, rfl⟩
        | ok p =>
          rcases p with ⟨_, _⟩; dsimp only
          rcases ioCell_mod_ok r _ w2 with ⟨okF, w3, h3⟩; rw [io_bind_ok _ _ _ h3]; cases okF <;> exact ⟨_, w3, rfl⟩
  have kill_ok : ∀ (sys : LeanSwe.Process.Internal.ProcessSysCapsM IO)
      (r : IO.Ref (LeanSwe.Process.Internal.ProcCellS Core.ioConcOps.Ref Core.ioConcOps.TaskHandle))
      (ef : Nat) (h : LeanSwe.Process.ProcessHandle) (w0 : Void IO.RealWorld),
      ∃ res w', LeanSwe.Process.SysBridge.killProcessGroupConc sys Core.ioConcOps
        (@Core.ioStateCell (LeanSwe.Process.Internal.ProcCellS Core.ioConcOps.Ref Core.ioConcOps.TaskHandle) r)
        ef h w0 = EST.Out.ok res w' := by
    intro sys r ef h w0; unfold LeanSwe.Process.SysBridge.killProcessGroupConc
    rcases ioCell_get_ok r w0 with ⟨st, w1, h1⟩; rw [io_bind_ok _ _ _ h1]
    cases (LeanSwe.Process.SysBridge.findSlotPure h.handleId st.slots).map (·.pgid) with
    | none => exact ⟨_, w1, rfl⟩
    | some _ => dsimp only; rcases ioConc_tryCatch_ok _ w1 with ⟨tr, w2, h2⟩; rw [io_bind_ok _ _ _ h2]; cases tr <;> exact ⟨_, w2, rfl⟩
  have reap_ok : ∀ (sys : LeanSwe.Process.Internal.ProcessSysCapsM IO)
      (r : IO.Ref (LeanSwe.Process.Internal.ProcCellS Core.ioConcOps.Ref Core.ioConcOps.TaskHandle))
      (ef : Nat) (h : LeanSwe.Process.ProcessHandle) (w0 : Void IO.RealWorld),
      ∃ res w', LeanSwe.Process.SysBridge.reapConc sys Core.ioConcOps
        (@Core.ioStateCell (LeanSwe.Process.Internal.ProcCellS Core.ioConcOps.Ref Core.ioConcOps.TaskHandle) r)
        ef h w0 = EST.Out.ok res w' := by
    intro sys r ef h w0; unfold LeanSwe.Process.SysBridge.reapConc
    rcases ioCell_mod_ok r _ w0 with ⟨det, w1, h1⟩; rw [io_bind_ok _ _ _ h1]
    cases det with
    | none => exact ⟨_, w1, rfl⟩
    | some _ => dsimp only; rcases ioConc_tryCatch_ok _ w1 with ⟨tr, w2, h2⟩; rw [io_bind_ok _ _ _ h2]; cases tr <;> exact ⟨_, w2, rfl⟩
  unfold LeanSwe.Process.defaultApi LeanSwe.Process.Internal.mkFullApiM
    LeanSwe.Process.Internal.run LeanSwe.Process.SysBridge.mkFullRawOpsM
  dsimp only
  cases LeanSwe.Process.Internal.validateRequest req with
  | error e => exact ⟨Except.error e, w, rfl⟩
  | ok vreq =>
    dsimp only
    rcases spawn_ok _ _ _ vreq w with ⟨rSpawn, w1, hSpawn⟩; rw [io_bind_ok _ _ _ hSpawn]
    cases rSpawn with
    | error _ => exact ⟨_, w1, rfl⟩
    | ok h =>
      dsimp only
      rcases await_ok _ _ _ _ h vreq.stdin vreq.timeoutMs vreq.maxOutputBytes w1 with ⟨rAwait, w2, hAwait⟩
      rw [io_bind_ok _ _ _ hAwait]
      rcases rAwait with _ | outcome
      · dsimp only
        rcases kill_ok _ _ _ h w2 with ⟨_, w3, hKill⟩; rw [io_bind_ok _ _ _ hKill]
        rcases reap_ok _ _ _ h w3 with ⟨_, w4, hReap⟩; rw [io_bind_ok _ _ _ hReap]
        exact ⟨_, w4, rfl⟩
      · cases outcome with
        | exited _ =>
          dsimp only
          rcases reap_ok _ _ _ h w2 with ⟨rReap, w3, hReap⟩; rw [io_bind_ok _ _ _ hReap]
          cases rReap <;> exact ⟨_, w3, rfl⟩
        | signaled _ _ _ | timedOut _ _ | outputLimitExceeded _ _ =>
          dsimp only
          rcases kill_ok _ _ _ h w2 with ⟨_, w3, hKill⟩; rw [io_bind_ok _ _ _ hKill]
          rcases reap_ok _ _ _ h w3 with ⟨_, w4, hReap⟩; rw [io_bind_ok _ _ _ hReap]
          exact ⟨_, w4, rfl⟩

/-- `Git.defaultOps.listEnv` never throws and maps all errors to `.commandFailed`. -/
theorem defaultOps_listEnv_res (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.defaultOps.listEnv w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind = .commandFailed := by
  dsimp only [LeanSwe.Git.defaultOps, LeanSwe.Git.Impl.mkRawOpsM]
  rcases envvars_listEnv_never_throws w with ⟨res, w', hw⟩
  rw [io_bind_ok _ _ _ hw]
  cases res with
  | ok env => exact ⟨.ok env, w', rfl, fun _ h => by cases h⟩
  | error e => exact ⟨.error (LeanSwe.Git.Impl.mapEnvVarsErrorImpl e), w', rfl, fun _ h => by cases h; rfl⟩

/-- `Impl.mapProcessErrorImpl` produces only `.timeout`, `.invalidInput`, or `.commandFailed`. -/
theorem mapProcessErrorImpl_kinds (cmd : String) (e : LeanSwe.Process.ProcessError) :
    (LeanSwe.Git.Impl.mapProcessErrorImpl cmd e).kind = .timeout ∨
    (LeanSwe.Git.Impl.mapProcessErrorImpl cmd e).kind = .invalidInput ∨
    (LeanSwe.Git.Impl.mapProcessErrorImpl cmd e).kind = .commandFailed := by
  dsimp only [LeanSwe.Git.Impl.mapProcessErrorImpl]
  cases e.kind <;> simp

/-- `Git.defaultOps.execGit` never throws and restricts errors to `.timeout`, `.invalidInput`, or `.commandFailed`. -/
theorem defaultOps_execGit_res (envOverrides : Array (String × Option String))
    (req : GitRawRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.defaultOps.execGit envOverrides req w = EST.Out.ok res w' ∧
      ∀ e, res = .error e →
        e.kind = .timeout ∨ e.kind = .invalidInput ∨ e.kind = .commandFailed := by
  dsimp only [LeanSwe.Git.defaultOps, LeanSwe.Git.Impl.mkRawOpsM]
  rcases process_run_never_throws
      { program := "git", args := req.args, cwd := req.cwd, env := envOverrides,
        stdin := req.stdin, timeoutMs := req.timeoutMs, maxOutputBytes := req.maxOutputBytes } w with ⟨res, w', hw⟩
  rw [io_bind_ok _ _ _ hw]
  cases res with
  | ok out => exact ⟨_, w', rfl, fun _ h => by cases h⟩
  | error e =>
    refine ⟨_, w', rfl, fun _ h => ?_⟩
    cases h
    exact mapProcessErrorImpl_kinds (req.args[0]?.getD "git") e

/-- `Impl.runGitRaw Git.defaultOps` never throws and bounds error kinds cleanly. -/
theorem runGitRaw_res (req : GitRawRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.Impl.runGitRaw LeanSwe.Git.defaultOps req w = EST.Out.ok res w' ∧
      ∀ e, res = .error e →
        (e.kind = .invalidPath ∧ ∃ p, req.cwd = some p ∧ LeanSwe.Git.Model.isValidPathArg p = false) ∨
        e.kind = .invalidInput ∨
        e.kind = .timeout ∨
        e.kind = .commandFailed := by
  unfold LeanSwe.Git.Impl.runGitRaw
  cases hcwd : LeanSwe.Git.Impl.validateCwd? req.cwd with
  | error e =>
    dsimp only
    refine ⟨_, w, rfl, fun _ he => ?_⟩
    cases he
    cases hreq : req.cwd with
    | none => simp [LeanSwe.Git.Impl.validateCwd?, hreq] at hcwd
    | some p =>
      simp only [LeanSwe.Git.Impl.validateCwd?, hreq] at hcwd
      split at hcwd
      · cases hcwd
      · cases hcwd
        rename_i hinv
        have hinvF : LeanSwe.Git.Model.isValidPathArg p = false := Bool.eq_false_iff.mpr hinv
        exact Or.inl ⟨rfl, p, rfl, hinvF⟩
  | ok _ =>
    dsimp only
    cases henv : LeanSwe.Git.Impl.validateExtraEnv req.extraEnv with
    | error e =>
      dsimp only
      refine ⟨_, w, rfl, fun _ he => ?_⟩
      cases he
      unfold LeanSwe.Git.Impl.validateExtraEnv at henv
      split at henv
      · cases henv
      · cases henv; exact Or.inr (Or.inl rfl)
    | ok _ =>
      dsimp only
      split
      · refine ⟨_, w, rfl, fun _ he => ?_⟩
        cases he; exact Or.inr (Or.inl rfl)
      · rcases defaultOps_listEnv_res w with ⟨renv, w1, hw1, hkenv⟩
        rw [io_bind_ok _ _ _ hw1]
        cases renv with
        | error e =>
          refine ⟨_, w1, rfl, fun _ he => ?_⟩
          cases he
          exact Or.inr (Or.inr (Or.inr (hkenv e rfl)))
        | ok inherited =>
          rcases defaultOps_execGit_res (LeanSwe.Git.Model.cleanGitEnv inherited req.extraEnv) req w1 with
            ⟨re, w2, hw2, hke⟩
          exact ⟨re, w2, hw2, fun e he => by
            rcases hke e he with h | h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inr h))⟩

/-- `Impl.classifyError` never produces `.invalidPath` or `.parseError`. -/
theorem classifyError_kinds (cmd : String) (out : GitRawOutput) :
    (LeanSwe.Git.Impl.classifyError cmd out).kind ≠ .invalidPath ∧
    (LeanSwe.Git.Impl.classifyError cmd out).kind ≠ .parseError := by
  dsimp only [LeanSwe.Git.Impl.classifyError]
  by_cases hBlank : (LeanSwe.Git.Impl.trimAsciiWhitespace (LeanSwe.Git.Impl.decodeUtf8Lossy out.stderr)).isEmpty = true
  · simp only [hBlank, ↓reduceIte]
    repeat' (split; try exact ⟨by decide, by decide⟩)
    exact ⟨by decide, by decide⟩
  · simp only [hBlank, Bool.false_eq_true, ↓reduceIte]
    repeat' (split; try exact ⟨by decide, by decide⟩)
    exact ⟨by decide, by decide⟩

/-- `Impl.runGitChecked Git.defaultOps` never throws and never produces `.parseError` (nor `.invalidPath` on valid `cwd`). -/
theorem runGitChecked_res (cmd : String) (req : GitRawRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultOps cmd req w = EST.Out.ok res w' ∧
      ∀ e, res = .error e →
        (req.cwd.elim True (fun p => LeanSwe.Git.Model.isValidPathArg p = true) → e.kind ≠ .invalidPath) ∧
        e.kind ≠ .parseError := by
  unfold LeanSwe.Git.Impl.runGitChecked
  rcases runGitRaw_res req w with ⟨r, w1, hw1, hkr⟩
  rw [io_bind_ok _ _ _ hw1]
  cases r with
  | error e =>
    dsimp only
    refine ⟨_, w1, rfl, fun _ he => ?_⟩
    cases he
    rcases hkr e rfl with ⟨h1, p, hp, hinv⟩ | h | h | h
    · refine ⟨fun hvalid => ?_, by rw [h1]; decide⟩
      simp [hp, hinv] at hvalid
    · exact ⟨fun _ => by rw [h]; decide, by rw [h]; decide⟩
    · exact ⟨fun _ => by rw [h]; decide, by rw [h]; decide⟩
    · exact ⟨fun _ => by rw [h]; decide, by rw [h]; decide⟩
  | ok out =>
    dsimp only
    split
    · exact ⟨_, w1, rfl, fun _ h => by cases h⟩
    · refine ⟨_, w1, rfl, fun e he => ?_⟩
      rw [← Except.error.inj he]
      have hk := classifyError_kinds cmd out
      exact ⟨fun _ => hk.1, hk.2⟩

/-- Binding unit continuation after `runGitChecked` never throws or returns `.parseError`. -/
theorem bind_runGitChecked_never_parseError (cmd : String) (req : GitRawRequest)
    (w : Void IO.RealWorld) :
    ∃ res w',
      (LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultOps cmd req >>= fun r =>
        match r with
        | Except.error e => pure (Except.error e)
        | Except.ok _ => pure (Except.ok ())) w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind ≠ .parseError := by
  rcases runGitChecked_res cmd req w with ⟨r, w1, hw1, hkr⟩
  rw [io_bind_ok _ _ _ hw1]
  cases r with
  | error e => exact ⟨_, w1, rfl, fun _ he => by cases he; exact (hkr e rfl).2⟩
  | ok _ => exact ⟨_, w1, rfl, fun _ h => by cases h⟩

/-- Binding unit continuation after `runGitChecked` with `cwd = none` never throws or returns `.invalidPath`/`.parseError`. -/
theorem bind_runGitChecked_no_cwd (cmd : String) (req : GitRawRequest)
    (hcwd : req.cwd = none) (w : Void IO.RealWorld) :
    ∃ res w',
      (LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultOps cmd req >>= fun r =>
        match r with
        | Except.error e => pure (Except.error e)
        | Except.ok _ => pure (Except.ok ())) w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind ≠ .invalidPath ∧ e.kind ≠ .parseError := by
  rcases runGitChecked_res cmd req w with ⟨r, w1, hw1, hkr⟩
  rw [io_bind_ok _ _ _ hw1]
  cases r with
  | error e =>
    refine ⟨_, w1, rfl, fun _ he => ?_⟩
    cases he
    exact ⟨(hkr e rfl).1 (by simp [hcwd]), (hkr e rfl).2⟩
  | ok _ => exact ⟨_, w1, rfl, fun _ h => by cases h⟩

/-- Lift a non-throwing `EST.Out.ok` characterization into `Core.NeverErrorKindIO`. -/
theorem neverErrorKindIO_of_ok {α : Type} (kind : GitErrorKind)
    (act : IO (Except GitError α)) (w : Void IO.RealWorld)
    (h : ∃ res w', act w = EST.Out.ok res w' ∧ ∀ e, res = .error e → e.kind ≠ kind) :
    Core.NeverErrorKindIO GitError.kind kind act w := by
  rcases h with ⟨res, w', hw, hk⟩
  unfold Core.NeverErrorKindIO
  rw [hw]
  cases res with
  | ok _ => trivial
  | error e => exact hk e rfl

/-- `Model.validateFsPathArg` produces only `.invalidPath` or `.invalidInput`. -/
theorem validateFsPathArg_kinds (p : String) (e : GitError)
    (h : LeanSwe.Git.Model.validateFsPathArg p = .error e) :
    e.kind = .invalidPath ∨ e.kind = .invalidInput := by
  unfold LeanSwe.Git.Model.validateFsPathArg at h
  split at h
  · cases h; exact Or.inl rfl
  · split at h
    · cases h; exact Or.inr rfl
    · cases h

/-- `Impl.validateRepoPath` never produces `.notARepo` or `.parseError`. -/
theorem validateRepoPath_never (repoPath : String) (e : GitError)
    (h : LeanSwe.Git.Impl.validateRepoPath repoPath = .error e) :
    e.kind ≠ .notARepo ∧ e.kind ≠ .parseError := by
  rcases validateFsPathArg_kinds repoPath e h with hk | hk <;> rw [hk] <;> exact ⟨by decide, by decide⟩

/-- `Model.validateCloneEndpoint` produces only `.invalidInput`. -/
theorem validateCloneEndpoint_kind (p : String) (e : GitError)
    (h : LeanSwe.Git.Model.validateCloneEndpoint p = .error e) :
    e.kind = .invalidInput := by
  unfold LeanSwe.Git.Model.validateCloneEndpoint at h
  split at h
  · cases h; rfl
  · cases h

end LeanSwe.Git.Proofs
