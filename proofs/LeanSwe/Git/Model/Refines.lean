import LeanSwe.EnvVars.Types
import LeanSwe.EnvVars.Model
import LeanSwe.Process.Types
import LeanSwe.Process.Model
import LeanSwe.Git.Types
import LeanSwe.Git.Types.Internal
import LeanSwe.Git.Model

/-!
Pure capability-refinement specification for `LeanSwe.Git` over `LeanSwe.EnvVars.Model`
and `LeanSwe.Process.Model`, covering `GitHostCapsM`, `GitHostState`, `execCapsStep`,
`allowedHostCapsStep`, and all 26 operations of `GitApiM` (`execPkgStep`, `allowedPkgStep`).
-/

namespace LeanSwe.Git.Model

open LeanSwe.EnvVars
open LeanSwe.Process
open LeanSwe.Git

/-- Pure model of `LeanSwe.Git.mapEnvVarsError`. -/
def mapEnvVarsErrorModel (e : EnvVarsError) : GitError :=
  let msg := if e.message.isEmpty then "failed to read inherited environment variables" else e.message
  { kind := .commandFailed, message := msg }

/-- Pure model of `LeanSwe.Git.mapProcessError`. -/
def mapProcessErrorModel (cmd : String) (e : ProcessError) : GitError :=
  let kind :=
    match e.kind with
    | .timedOut => .timeout
    | .invalidInput => .invalidInput
    | _ => .commandFailed
  let msg := if e.message.isEmpty then s!"git {cmd} invocation failed" else e.message
  { kind := kind
    command := some cmd
    exitCode := e.exitCode
    stderr := e.stderr.map (fun b => (String.fromUTF8? b).getD "")
    message := msg }

/-- Pure capability container bundling `EnvVarsApiM m` and `ProcessApiM m` for `LeanSwe.Git`. -/
abbrev GitHostCapsM := LeanSwe.Git.Internal.GitHostCapsM

/-- Combined abstract host state pairing `EnvVars.Raw.Model.EnvironState` with `Process.Model.ProcessModelState`. -/
structure GitHostState where
  /-- Ambient process environment snapshot model. -/
  env : LeanSwe.EnvVars.Raw.Model.EnvironState := {}
  /-- Active child-process handle lifecycle state. -/
  proc : LeanSwe.Process.Model.ProcessModelState := {}
  deriving Inhabited

/-- Well-formedness guard on `GitHostState` delegating to `Process.Model.processStateWf`. -/
def hostStepWf (s : GitHostState) : Bool :=
  LeanSwe.Process.Model.processStateWf s.proc

/-- Single-step lower-layer capability request sum over `GitHostCapsM`. -/
inductive HostCapsReq where
  /-- Environment query request dispatched to `caps.env`. -/
  | env (req : LeanSwe.EnvVars.Model.PkgStepReq)
  /-- Process operation request dispatched to `caps.proc`. -/
  | proc (req : LeanSwe.Process.Model.PkgStepReq)

/-- Single-step lower-layer capability output sum over `GitHostCapsM`. -/
inductive HostCapsOut where
  /-- Environment query output returned by `caps.env`. -/
  | env (out : LeanSwe.EnvVars.Model.PkgStepOut)
  /-- Process operation output returned by `caps.proc`. -/
  | proc (out : LeanSwe.Process.Model.PkgStepOut)

/-- Execute one `HostCapsReq` against an arbitrary `GitHostCapsM (StateM W)`. -/
def execCapsStep {W : Type} (caps : GitHostCapsM (StateM W)) : HostCapsReq → StateM W HostCapsOut
  | .env req => .env <$> LeanSwe.EnvVars.Model.execPkgStep caps.env req
  | .proc req => .proc <$> LeanSwe.Process.Model.execPkgStep caps.proc req

/-- Allowed lower-layer single-step relation composing `EnvVars.Model.allowedPkgStep` and `Process.Model.allowedPkgStep`. -/
def allowedHostCapsStep (s : GitHostState) (req : HostCapsReq) (out : HostCapsOut)
    (s' : GitHostState) : Prop :=
  hostStepWf s = true ∧
  hostStepWf s' = true ∧
  match req, out with
  | .env er, .env eo =>
    s'.proc = s.proc ∧ LeanSwe.EnvVars.Model.allowedPkgStep s.env er eo s'.env
  | .proc pr, .proc po =>
    s'.env = s.env ∧ LeanSwe.Process.Model.allowedPkgStep s.proc pr po s'.proc
  | _, _ => False

/-- Single-step request sum covering all 26 operations of `GitApiM`. -/
inductive PkgStepReq where
  /-- `api.isRepo repoPath`. -/
  | isRepo (repoPath : String)
  /-- `api.repoRoot repoPath`. -/
  | repoRoot (repoPath : String)
  /-- `api.commonDir repoPath`. -/
  | commonDir (repoPath : String)
  /-- `api.headCommit? repoPath`. -/
  | headCommit? (repoPath : String)
  /-- `api.headBranch? repoPath`. -/
  | headBranch? (repoPath : String)
  /-- `api.headState repoPath`. -/
  | headState (repoPath : String)
  /-- `api.revParseCommit repoPath rev`. -/
  | revParseCommit (repoPath rev : String)
  /-- `api.isAncestor repoPath ancestor descendant`. -/
  | isAncestor (repoPath : String) (ancestor descendant : CommitId)
  /-- `api.mergeBase? repoPath a b`. -/
  | mergeBase? (repoPath : String) (a b : CommitId)
  /-- `api.status repoPath`. -/
  | status (repoPath : String)
  /-- `api.diffNameStatus repoPath revA revB? paths`. -/
  | diffNameStatus (repoPath revA : String) (revB? : Option String) (paths : Array String)
  /-- `api.listWorktrees repoPath`. -/
  | listWorktrees (repoPath : String)
  /-- `api.showFile? repoPath rev relPath`. -/
  | showFile? (repoPath rev relPath : String)
  /-- `api.init path bare initialBranch?`. -/
  | init (path : String) (bare : Bool) (initialBranch? : Option RefName)
  /-- `api.clone source target opts`. -/
  | clone (source target : String) (opts : CloneOptions)
  /-- `api.add repoPath paths all`. -/
  | add (repoPath : String) (paths : Array String) (all : Bool)
  /-- `api.commit repoPath opts`. -/
  | commit (repoPath : String) (opts : CommitOptions)
  /-- `api.createBranch repoPath branch startPoint? force`. -/
  | createBranch (repoPath : String) (branch : RefName) (startPoint? : Option String) (force : Bool)
  /-- `api.deleteBranch repoPath branch force`. -/
  | deleteBranch (repoPath : String) (branch : RefName) (force : Bool)
  /-- `api.checkout repoPath target force`. -/
  | checkout (repoPath : String) (target : CheckoutTarget) (force : Bool)
  /-- `api.switch repoPath branch create startPoint? force`. -/
  | switch (repoPath : String) (branch : RefName) (create : Bool) (startPoint? : Option String) (force : Bool)
  /-- `api.reset repoPath mode rev`. -/
  | reset (repoPath : String) (mode : ResetMode) (rev : String)
  /-- `api.fetch repoPath remote refspec? prune`. -/
  | fetch (repoPath remote : String) (refspec? : Option String) (prune : Bool)
  /-- `api.worktreeAdd repoPath opts`. -/
  | worktreeAdd (repoPath : String) (opts : WorktreeAddOptions)
  /-- `api.worktreeRemove repoPath wtPath force`. -/
  | worktreeRemove (repoPath wtPath : String) (force : Bool)
  /-- `api.withWorktree repoPath opts (fun _ => pure actionRes)`. -/
  | withWorktree (repoPath : String) (opts : WorktreeAddOptions) (actionRes : Except GitError Nat)
  deriving Inhabited

/-- Single-step output sum for all 26 operations of `GitApiM`. -/
inductive PkgStepOut where
  /-- Boolean outcome (`isRepo`, `isAncestor`). -/
  | bool (res : Except GitError Bool)
  /-- String outcome (`repoRoot`, `commonDir`). -/
  | str (res : Except GitError String)
  /-- Optional commit ID outcome (`headCommit?`, `mergeBase?`). -/
  | optCommit (res : Except GitError (Option CommitId))
  /-- Optional ref name outcome (`headBranch?`). -/
  | optRef (res : Except GitError (Option RefName))
  /-- Combined `HEAD` state outcome (`headState`). -/
  | headState (res : Except GitError HeadState)
  /-- Commit ID outcome (`revParseCommit`, `commit`). -/
  | commit (res : Except GitError CommitId)
  /-- Porcelain status entries outcome (`status`). -/
  | status (res : Except GitError (Array StatusEntry))
  /-- Diff entries outcome (`diffNameStatus`). -/
  | diff (res : Except GitError (Array DiffEntry))
  /-- Worktree list outcome (`listWorktrees`). -/
  | worktrees (res : Except GitError (Array WorktreeInfo))
  /-- Optional blob bytes outcome (`showFile?`). -/
  | optBytes (res : Except GitError (Option ByteArray))
  /-- Unit outcome for mutation operations. -/
  | unit (res : Except GitError Unit)
  /-- Bracketed `withWorktree` action outcome at `Nat`. -/
  | withWt (res : Except GitError Nat)
  deriving Inhabited

/-- Execute one `PkgStepReq` against an arbitrary `GitApiM (StateM W)`. -/
def execPkgStep {W : Type} (api : GitApiM (StateM W)) : PkgStepReq → StateM W PkgStepOut
  | .isRepo p => .bool <$> api.isRepo p
  | .repoRoot p => .str <$> api.repoRoot p
  | .commonDir p => .str <$> api.commonDir p
  | .headCommit? p => .optCommit <$> api.headCommit? p
  | .headBranch? p => .optRef <$> api.headBranch? p
  | .headState p => .headState <$> api.headState p
  | .revParseCommit p rev => .commit <$> api.revParseCommit p rev
  | .isAncestor p a d => .bool <$> api.isAncestor p a d
  | .mergeBase? p a b => .optCommit <$> api.mergeBase? p a b
  | .status p => .status <$> api.status p
  | .diffNameStatus p rA rB? ps => .diff <$> api.diffNameStatus p rA rB? ps
  | .listWorktrees p => .worktrees <$> api.listWorktrees p
  | .showFile? p rev rel => .optBytes <$> api.showFile? p rev rel
  | .init p bare b? => .unit <$> api.init p bare b?
  | .clone src dst opts => .unit <$> api.clone src dst opts
  | .add p ps all => .unit <$> api.add p ps all
  | .commit p opts => .commit <$> api.commit p opts
  | .createBranch p b sp? f => .unit <$> api.createBranch p b sp? f
  | .deleteBranch p b f => .unit <$> api.deleteBranch p b f
  | .checkout p t f => .unit <$> api.checkout p t f
  | .switch p b c sp? f => .unit <$> api.switch p b c sp? f
  | .reset p m rev => .unit <$> api.reset p m rev
  | .fetch p rem ref? pr => .unit <$> api.fetch p rem ref? pr
  | .worktreeAdd p opts => .unit <$> api.worktreeAdd p opts
  | .worktreeRemove p wt f => .unit <$> api.worktreeRemove p wt f
  | .withWorktree p opts actRes => .withWt <$> api.withWorktree p opts (fun _ => pure actRes)

/-- Handle- and environment-conserving `GitHostState` transition across zero or more `git` subprocess calls. -/
def allowedHostTransition (s s' : GitHostState) : Prop :=
  hostStepWf s = true ∧
  hostStepWf s' = true ∧
  s'.env = s.env ∧
  s'.proc.activeHandles = s.proc.activeHandles ∧
  s.proc.nextHandleId ≤ s'.proc.nextHandleId

/-- Well-formedness and forbidden-kind exclusion on a `GitError`. -/
def allowedGitErr (forbidden : List GitErrorKind) (e : GitError) : Prop :=
  e.message ≠ "" ∧ ∀ k ∈ forbidden, e.kind ≠ k

/-- Structural validity check on `HeadState` values returned by `headState`. -/
def isValidHeadState : HeadState → Bool
  | .attached b c? => isValidRefNameStr b.raw && c?.all (fun c => isValidCommitIdStr c.hex)
  | .detached c => isValidCommitIdStr c.hex

/-- Structural validity check on `WorktreeInfo` values returned by `listWorktrees`. -/
def isValidWorktreeInfo (w : WorktreeInfo) : Bool :=
  !w.path.isEmpty &&
  w.head?.all (fun c => isValidCommitIdStr c.hex) &&
  w.branch?.all (fun b => isValidRefNameStr b.raw)

/-- Pure pre-validation check for `revParseCommit`. -/
def preValidateRevParseCommit (repoPath rev : String) : Except GitErrorKind Unit := do
  (validateFsPathArg repoPath).mapError (·.kind)
  if !isValidRevSpec rev then .error .invalidInput else .ok ()

/-- Pure pre-validation check for `isAncestor` and `mergeBase?`. -/
def preValidateCommitPair (repoPath : String) (a b : CommitId) : Except GitErrorKind Unit := do
  (validateFsPathArg repoPath).mapError (·.kind)
  if !isValidCommitIdStr a.hex || !isValidCommitIdStr b.hex then .error .invalidRef else .ok ()

/-- Pure pre-validation check for `diffNameStatus`. -/
def preValidateDiffNameStatus (repoPath revA : String) (revB? : Option String) (paths : Array String) :
    Except GitErrorKind Unit := do
  (validateFsPathArg repoPath).mapError (·.kind)
  if !isValidStrictRevSpec revA then .error .invalidInput
  match revB? with
  | none => pure ()
  | some rb => if !isValidStrictRevSpec rb then .error .invalidInput
  if !paths.all isValidPathArg then .error .invalidPath else .ok ()

/-- Pure pre-validation check for `showFile?`. -/
def preValidateShowFile (repoPath rev relPath : String) : Except GitErrorKind Unit := do
  (validateFsPathArg repoPath).mapError (·.kind)
  if !isValidStrictRevSpec rev then .error .invalidInput
  (validateRelRepoPath relPath).mapError (·.kind)

/-- Pure pre-validation check for `init`. -/
def preValidateInit (path : String) (initialBranch? : Option RefName) : Except GitErrorKind Unit := do
  (validateFsPathArg path).mapError (·.kind)
  match initialBranch? with
  | none => .ok ()
  | some b => if isValidRefNameStr b.raw then .ok () else .error .invalidRef

/-- Pure pre-validation check for `clone`. -/
def preValidateClone (source target : String) (opts : CloneOptions) : Except GitErrorKind Unit := do
  (validateCloneEndpoint source).mapError (·.kind)
  (validateCloneEndpoint target).mapError (·.kind)
  if opts.depth? == some 0 then .error .invalidInput
  match opts.branch? with
  | none => .ok ()
  | some b => if isValidRefNameStr b then .ok () else .error .invalidRef

/-- Pure pre-validation check for `add`. -/
def preValidateAdd (repoPath : String) (paths : Array String) (all : Bool) : Except GitErrorKind Unit := do
  (validateFsPathArg repoPath).mapError (·.kind)
  if !all && paths.isEmpty then .error .invalidInput
  if !paths.all isValidPathArg then .error .invalidPath else .ok ()

/-- Pure pre-validation check for `commit`. -/
def preValidateCommit (repoPath : String) (opts : CommitOptions) : Except GitErrorKind Unit := do
  (validateFsPathArg repoPath).mapError (·.kind)
  (validateCommitOptions opts).mapError (·.kind)

/-- Pure pre-validation check for `createBranch`. -/
def preValidateCreateBranch (repoPath : String) (branch : RefName) (startPoint? : Option String) :
    Except GitErrorKind Unit := do
  (validateFsPathArg repoPath).mapError (·.kind)
  if !isValidRefNameStr branch.raw then .error .invalidRef
  match startPoint? with
  | none => .ok ()
  | some sp => if isValidStrictRevSpec sp then .ok () else .error .invalidInput

/-- Pure pre-validation check for `deleteBranch`. -/
def preValidateDeleteBranch (repoPath : String) (branch : RefName) : Except GitErrorKind Unit := do
  (validateFsPathArg repoPath).mapError (·.kind)
  if !isValidRefNameStr branch.raw then .error .invalidRef else .ok ()

/-- Pure pre-validation check for `checkout`. -/
def preValidateCheckout (repoPath : String) (target : CheckoutTarget) : Except GitErrorKind Unit := do
  (validateFsPathArg repoPath).mapError (·.kind)
  match target with
  | .branch b => if isValidRefNameStr b.raw then .ok () else .error .invalidRef
  | .commit cid => if isValidCommitIdStr cid.hex then .ok () else .error .invalidRef
  | .ref spec => if isValidStrictRevSpec spec then .ok () else .error .invalidInput

/-- Pure pre-validation check for `switch`. -/
def preValidateSwitch (repoPath : String) (branch : RefName) (create : Bool)
    (startPoint? : Option String) : Except GitErrorKind Unit := do
  (validateFsPathArg repoPath).mapError (·.kind)
  if !isValidRefNameStr branch.raw then .error .invalidRef
  if !create && startPoint?.isSome then .error .invalidInput
  match startPoint? with
  | none => .ok ()
  | some sp => if isValidStrictRevSpec sp then .ok () else .error .invalidInput

/-- Pure pre-validation check for `reset`. -/
def preValidateReset (repoPath rev : String) : Except GitErrorKind Unit := do
  (validateFsPathArg repoPath).mapError (·.kind)
  if !isValidStrictRevSpec rev then .error .invalidInput else .ok ()

/-- Pure pre-validation check for `fetch`. -/
def preValidateFetch (repoPath remote : String) (refspec? : Option String) : Except GitErrorKind Unit := do
  (validateFsPathArg repoPath).mapError (·.kind)
  if !isValidRemoteOrRefspec remote then .error .invalidInput
  match refspec? with
  | none => .ok ()
  | some r => if isValidRemoteOrRefspec r then .ok () else .error .invalidInput

/-- Pure pre-validation check for `worktreeAdd` and `withWorktree`. -/
def preValidateWorktreeAdd (repoPath : String) (opts : WorktreeAddOptions) : Except GitErrorKind Unit := do
  (validateFsPathArg repoPath).mapError (·.kind)
  (validateFsPathArg opts.path).mapError (·.kind)
  if opts.detach && opts.newBranch?.isSome then .error .invalidInput
  match opts.newBranch? with
  | none => pure ()
  | some b => if !isValidRefNameStr b.raw then .error .invalidRef
  match opts.target? with
  | none => .ok ()
  | some t => if isValidStrictRevSpec t then .ok () else .error .invalidInput

/-- Pure pre-validation check for `worktreeRemove`. -/
def preValidateWorktreeRemove (repoPath wtPath : String) : Except GitErrorKind Unit := do
  (validateFsPathArg repoPath).mapError (·.kind)
  (validateFsPathArg wtPath).mapError (·.kind)

/-- Guarded outcome predicate: rejected pre-validations fail without mutating state; accepted inputs satisfy `allowedHostTransition`, `okPred`, and `allowedGitErr forbidden`. -/
def allowedGuardedStep {α : Type} (s s' : GitHostState) (pre : Except GitErrorKind Unit)
    (forbidden : List GitErrorKind) (okPred : α → Prop) (res : Except GitError α) : Prop :=
  match pre with
  | .error k =>
    s' = s ∧
    hostStepWf s = true ∧
    match res with
    | .error e => e.kind = k ∧ e.message ≠ ""
    | .ok _ => False
  | .ok () =>
    allowedHostTransition s s' ∧
    match res with
    | .ok v => okPred v
    | .error e => allowedGitErr forbidden e

/-- Relational single-step contract for all 26 `GitApiM` operations over `GitHostState`. -/
def allowedPkgStep (s : GitHostState) (req : PkgStepReq) (out : PkgStepOut)
    (s' : GitHostState) : Prop :=
  match req, out with
  | .isRepo p, .bool res =>
    allowedGuardedStep s s' ((validateFsPathArg p).mapError (·.kind)) [.notARepo, .parseError]
      (fun _ => True) res
  | .repoRoot p, .str res =>
    allowedGuardedStep s s' ((validateFsPathArg p).mapError (·.kind)) [] (fun _ => True) res
  | .commonDir p, .str res =>
    allowedGuardedStep s s' ((validateFsPathArg p).mapError (·.kind)) [] (fun _ => True) res
  | .headCommit? p, .optCommit res =>
    allowedGuardedStep s s' ((validateFsPathArg p).mapError (·.kind)) []
      (fun c? => c?.all (fun c => isValidCommitIdStr c.hex) = true) res
  | .headBranch? p, .optRef res =>
    allowedGuardedStep s s' ((validateFsPathArg p).mapError (·.kind)) []
      (fun b? => b?.all (fun b => isValidRefNameStr b.raw) = true) res
  | .headState p, .headState res =>
    allowedGuardedStep s s' ((validateFsPathArg p).mapError (·.kind)) []
      (fun hs => isValidHeadState hs = true) res
  | .revParseCommit p rev, .commit res =>
    allowedGuardedStep s s' (preValidateRevParseCommit p rev) []
      (fun cid => isValidCommitIdStr cid.hex = true) res
  | .isAncestor p a d, .bool res =>
    allowedGuardedStep s s' (preValidateCommitPair p a d) [.parseError] (fun _ => True) res
  | .mergeBase? p a b, .optCommit res =>
    allowedGuardedStep s s' (preValidateCommitPair p a b) []
      (fun c? => c?.all (fun c => isValidCommitIdStr c.hex) = true) res
  | .status p, .status res =>
    allowedGuardedStep s s' ((validateFsPathArg p).mapError (·.kind)) []
      (fun entries => entries.all (fun e => !e.path.isEmpty) = true) res
  | .diffNameStatus p rA rB? ps, .diff res =>
    allowedGuardedStep s s' (preValidateDiffNameStatus p rA rB? ps) [] (fun _ => True) res
  | .listWorktrees p, .worktrees res =>
    allowedGuardedStep s s' ((validateFsPathArg p).mapError (·.kind)) []
      (fun wts => wts.all isValidWorktreeInfo = true) res
  | .showFile? p rev rel, .optBytes res =>
    allowedGuardedStep s s' (preValidateShowFile p rev rel) [] (fun _ => True) res
  | .init p _ b?, .unit res =>
    allowedGuardedStep s s' (preValidateInit p b?) [.parseError] (fun _ => True) res
  | .clone src dst opts, .unit res =>
    allowedGuardedStep s s' (preValidateClone src dst opts) [.invalidPath, .parseError] (fun _ => True) res
  | .add p ps all, .unit res =>
    allowedGuardedStep s s' (preValidateAdd p ps all) [.parseError] (fun _ => True) res
  | .commit p opts, .commit res =>
    allowedGuardedStep s s' (preValidateCommit p opts) []
      (fun cid => isValidCommitIdStr cid.hex = true) res
  | .createBranch p b sp? _, .unit res =>
    allowedGuardedStep s s' (preValidateCreateBranch p b sp?) [.parseError] (fun _ => True) res
  | .deleteBranch p b _, .unit res =>
    allowedGuardedStep s s' (preValidateDeleteBranch p b) [.parseError] (fun _ => True) res
  | .checkout p t _, .unit res =>
    allowedGuardedStep s s' (preValidateCheckout p t) [.parseError] (fun _ => True) res
  | .switch p b c sp? _, .unit res =>
    allowedGuardedStep s s' (preValidateSwitch p b c sp?) [.parseError] (fun _ => True) res
  | .reset p _ rev, .unit res =>
    allowedGuardedStep s s' (preValidateReset p rev) [.parseError] (fun _ => True) res
  | .fetch p rem ref? _, .unit res =>
    allowedGuardedStep s s' (preValidateFetch p rem ref?) [.parseError] (fun _ => True) res
  | .worktreeAdd p opts, .unit res =>
    allowedGuardedStep s s' (preValidateWorktreeAdd p opts) [.parseError] (fun _ => True) res
  | .worktreeRemove p wt _, .unit res =>
    allowedGuardedStep s s' (preValidateWorktreeRemove p wt) [.parseError] (fun _ => True) res
  | .withWorktree p opts actRes, .withWt res =>
    match preValidateWorktreeAdd p opts with
    | .error k =>
      s' = s ∧
      hostStepWf s = true ∧
      match res with
      | .error e => e.kind = k ∧ e.message ≠ ""
      | .ok _ => False
    | .ok () =>
      allowedHostTransition s s' ∧
      match actRes with
      | .ok a =>
        res = .ok a ∨ ∃ e, res = .error e ∧ allowedGitErr [.parseError] e
      | .error ae =>
        res = .error ae ∨ ∃ e, res = .error e ∧ allowedGitErr [.parseError] e
  | _, _ => False

end LeanSwe.Git.Model
