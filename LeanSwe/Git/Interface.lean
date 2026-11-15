import LeanSwe.Process.Types
import LeanSwe.Process.Interface
import LeanSwe.EnvVars.Types
import LeanSwe.EnvVars.Interface
import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Impl

namespace LeanSwe.Git

open LeanSwe.Process
open LeanSwe.EnvVars

/-- Map an `EnvVarsError` produced by `EnvVars.listEnv` to a normalized `GitError`. -/
def mapEnvVarsError (e : EnvVarsError) : GitError :=
  let msg := if e.message.isEmpty then "failed to read inherited environment variables" else e.message
  { kind := .commandFailed, message := msg }

/-- Map a `ProcessError` produced by `Process.run` to a normalized `GitError`. -/
def mapProcessError (cmd : String) (e : ProcessError) : GitError :=
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

/-- Default `IO` implementation of `RawGitOps` wired to `EnvVars.listEnv` and `Process.run`. -/
def defaultRawOps : RawGitOps :=
  { listEnv := do
      match ← EnvVars.listEnv with
      | .ok env => return .ok env
      | .error e => return .error (mapEnvVarsError e)
    execGit := fun envOverrides req => do
      let cmd := req.args[0]?.getD "git"
      let execReq : ExecRequest :=
        { program := "git"
          args := req.args
          cwd := req.cwd
          env := envOverrides
          inheritEnv := true
          stdin := req.stdin
          timeoutMs := req.timeoutMs
          maxOutputBytes := req.maxOutputBytes }
      match ← Process.run execReq with
      | .ok res =>
        return .ok { exitCode := res.exitCode, stdout := res.stdout, stderr := res.stderr }
      | .error e =>
        return .error (mapProcessError cmd e) }

/-- Default `IO` Git API bundle built from `Impl.mkApiM defaultRawOps`. -/
def defaultApi : GitApi := Impl.mkApiM defaultRawOps

/-- Return `true` iff `repoPath` is inside a Git repository. -/
def isRepo (repoPath : String) : IO (Except GitError Bool) :=
  defaultApi.isRepo repoPath

/-- Return the absolute working-tree top-level directory (`notARepo` for bare repositories). -/
def repoRoot (repoPath : String) : IO (Except GitError String) :=
  defaultApi.repoRoot repoPath

/-- Return the absolute shared `.git` directory across all worktrees. -/
def commonDir (repoPath : String) : IO (Except GitError String) :=
  defaultApi.commonDir repoPath

/-- Return the `HEAD` commit ID, or `none` when `HEAD` is on an unborn branch. -/
def headCommit? (repoPath : String) : IO (Except GitError (Option CommitId)) :=
  defaultApi.headCommit? repoPath

/-- Return the attached branch name of `HEAD`, or `none` when detached. -/
def headBranch? (repoPath : String) : IO (Except GitError (Option RefName)) :=
  defaultApi.headBranch? repoPath

/-- Return the combined `HeadState` of `HEAD`. -/
def headState (repoPath : String) : IO (Except GitError HeadState) :=
  defaultApi.headState repoPath

/-- Resolve a revision specification to a validated `CommitId`. -/
def revParseCommit (repoPath rev : String) : IO (Except GitError CommitId) :=
  defaultApi.revParseCommit repoPath rev

/-- Return `true` iff `ancestor` is an ancestor of `descendant`. -/
def isAncestor (repoPath : String) (ancestor descendant : CommitId) : IO (Except GitError Bool) :=
  defaultApi.isAncestor repoPath ancestor descendant

/-- Return a merge base commit of `a` and `b`, or `none` if histories are disjoint. -/
def mergeBase? (repoPath : String) (a b : CommitId) : IO (Except GitError (Option CommitId)) :=
  defaultApi.mergeBase? repoPath a b

/-- Return working-tree and index status entries via `git status --porcelain=v1 -z`. -/
def status (repoPath : String) : IO (Except GitError (Array StatusEntry)) :=
  defaultApi.status repoPath

/-- Return file change summaries between `revA` and optional `revB?` (or working tree). -/
def diffNameStatus (repoPath revA : String) (revB? : Option String := none)
    (paths : Array String := #[]) : IO (Except GitError (Array DiffEntry)) :=
  defaultApi.diffNameStatus repoPath revA revB? paths

/-- List main and linked worktrees via `git worktree list --porcelain -z`. -/
def listWorktrees (repoPath : String) : IO (Except GitError (Array WorktreeInfo)) :=
  defaultApi.listWorktrees repoPath

/-- Read blob bytes for `relPath` at `rev`, returning `none` if absent or a directory tree. -/
def showFile? (repoPath rev relPath : String) : IO (Except GitError (Option ByteArray)) :=
  defaultApi.showFile? repoPath rev relPath

/-- Initialize a new Git repository at `path`. -/
def init (path : String) (bare : Bool := false) (initialBranch? : Option RefName := none) :
    IO (Except GitError Unit) :=
  defaultApi.init path bare initialBranch?

/-- Clone a repository non-interactively from `source` to `target`. -/
def clone (source target : String) (opts : CloneOptions := {}) : IO (Except GitError Unit) :=
  defaultApi.clone source target opts

/-- Stage explicit `paths` or all changes (`all = true`). -/
def add (repoPath : String) (paths : Array String := #[]) (all : Bool := false) :
    IO (Except GitError Unit) :=
  defaultApi.add repoPath paths all

/-- Create a commit with `CommitOptions` and return the resulting `CommitId`. -/
def commit (repoPath : String) (opts : CommitOptions) : IO (Except GitError CommitId) :=
  defaultApi.commit repoPath opts

/-- Create (or reset when `force = true`) a local branch. -/
def createBranch (repoPath : String) (branch : RefName) (startPoint? : Option String := none)
    (force : Bool := false) : IO (Except GitError Unit) :=
  defaultApi.createBranch repoPath branch startPoint? force

/-- Delete a local branch. -/
def deleteBranch (repoPath : String) (branch : RefName) (force : Bool := false) :
    IO (Except GitError Unit) :=
  defaultApi.deleteBranch repoPath branch force

/-- Check out a branch, commit, or validated revision. -/
def checkout (repoPath : String) (target : CheckoutTarget) (force : Bool := false) :
    IO (Except GitError Unit) :=
  defaultApi.checkout repoPath target force

/-- Switch to an existing or newly created branch. -/
def switch (repoPath : String) (branch : RefName) (create : Bool := false)
    (startPoint? : Option String := none) (force : Bool := false) : IO (Except GitError Unit) :=
  defaultApi.switch repoPath branch create startPoint? force

/-- Reset `HEAD` (and optionally index/working tree) to `rev`. -/
def reset (repoPath : String) (mode : ResetMode) (rev : String) : IO (Except GitError Unit) :=
  defaultApi.reset repoPath mode rev

/-- Fetch updates non-interactively from `remote` and optional `refspec?`. -/
def fetch (repoPath remote : String) (refspec? : Option String := none) (prune : Bool := false) :
    IO (Except GitError Unit) :=
  defaultApi.fetch repoPath remote refspec? prune

/-- Add a new linked worktree. -/
def worktreeAdd (repoPath : String) (opts : WorktreeAddOptions) : IO (Except GitError Unit) :=
  defaultApi.worktreeAdd repoPath opts

/-- Remove an existing linked worktree. -/
def worktreeRemove (repoPath wtPath : String) (force : Bool := false) : IO (Except GitError Unit) :=
  defaultApi.worktreeRemove repoPath wtPath force

/-- Execute `action` inside a bracketed linked worktree, guaranteeing removal on completion. -/
def withWorktree {α : Type} (repoPath : String) (opts : WorktreeAddOptions)
    (action : String → IO (Except GitError α)) : IO (Except GitError α) :=
  defaultApi.withWorktree repoPath opts action

end LeanSwe.Git
