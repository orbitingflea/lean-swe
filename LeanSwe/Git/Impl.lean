import LeanSwe.EnvVars.Types
import LeanSwe.Process.Types
import LeanSwe.Git.Types
import LeanSwe.Git.Types.Internal
import LeanSwe.Git.Impl.Helpers
import LeanSwe.Git.Impl.QueryOps
import LeanSwe.Git.Impl.MutOps

namespace LeanSwe.Git.Impl

open LeanSwe.EnvVars
open LeanSwe.Process
open LeanSwe.Git
open LeanSwe.Git.Internal (GitHostCapsM)

/-- Map an `EnvVarsError` produced by `EnvVarsApiM.listEnv` to a normalized `GitError`. -/
abbrev mapEnvVarsErrorImpl (e : EnvVarsError) : GitError :=
  let msg := if e.message.isEmpty then "failed to read inherited environment variables" else e.message
  { kind := .commandFailed, message := msg }

/-- Map a `ProcessError` produced by `ProcessApiM.run` to a normalized `GitError`. -/
abbrev mapProcessErrorImpl (cmd : String) (e : ProcessError) : GitError :=
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

/-- Build `RawGitOpsM m` from injected `EnvVarsApiM m` and `ProcessApiM m` host capabilities. -/
def mkRawOpsM {m : Type → Type} [Monad m] (caps : GitHostCapsM m) : RawGitOpsM m :=
  { listEnv := do
      match ← caps.env.listEnv with
      | .ok env => return .ok env
      | .error e => return .error (mapEnvVarsErrorImpl e)
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
      match ← caps.proc.run execReq with
      | .ok res =>
        return .ok { exitCode := res.exitCode, stdout := res.stdout, stderr := res.stderr }
      | .error e =>
        return .error (mapProcessErrorImpl cmd e) }

/-- Construct the effect-polymorphic `GitApiM m` implementation backed by `RawGitOpsM m`. -/
def mkApiM {m : Type → Type} [Monad m] [MonadFinally m] (ops : RawGitOpsM m) : GitApiM m :=
  { isRepo := isRepoImpl ops
    repoRoot := repoRootImpl ops
    commonDir := commonDirImpl ops
    headCommit? := headCommitImpl ops
    headBranch? := headBranchImpl ops
    headState := headStateImpl ops
    revParseCommit := revParseCommitImpl ops
    isAncestor := isAncestorImpl ops
    mergeBase? := mergeBaseImpl ops
    status := statusImpl ops
    diffNameStatus := diffNameStatusImpl ops
    listWorktrees := listWorktreesImpl ops
    showFile? := showFileImpl ops
    init := initImpl ops
    clone := cloneImpl ops
    add := addImpl ops
    commit := commitImpl ops
    createBranch := createBranchImpl ops
    deleteBranch := deleteBranchImpl ops
    checkout := checkoutImpl ops
    switch := switchImpl ops
    reset := resetImpl ops
    fetch := fetchImpl ops
    worktreeAdd := worktreeAddImpl ops
    worktreeRemove := worktreeRemoveImpl ops
    withWorktree := fun repoPath opts action => withWorktreeImpl ops repoPath opts action }

/-- Construct `GitApiM m` directly from `GitHostCapsM m` (`EnvVarsApiM m` + `ProcessApiM m`). -/
def mkApiFromCapsM {m : Type → Type} [Monad m] [MonadFinally m] (caps : GitHostCapsM m) :
    GitApiM m :=
  mkApiM (mkRawOpsM caps)

end LeanSwe.Git.Impl
