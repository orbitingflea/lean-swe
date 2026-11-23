namespace LeanSwe.Git

/-- Format a `ByteArray` as a Lean `List UInt8` representation for `Repr` instances. -/
def reprByteArray (bs : ByteArray) : Std.Format :=
  repr bs.toList

/-- Validated Git commit object identifier (40-char SHA-1 or 64-char SHA-256 lowercase hex). -/
structure CommitId where
  /-- Lowercase hexadecimal commit object hash. -/
  hex : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Validated Git reference or branch name. -/
structure RefName where
  /-- Raw reference or branch name string. -/
  raw : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- State of `HEAD` in a Git repository or worktree. -/
inductive HeadState where
  /-- Attached to a branch; `commit? = none` denotes an unborn branch prior to the initial commit. -/
  | attached (branch : RefName) (commit? : Option CommitId)
  /-- Detached `HEAD` pointing directly at a commit. -/
  | detached (commit : CommitId)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- File status classification from `git status --porcelain=v1 -z`. -/
inductive StatusKind where
  /-- Modified file (`M`). -/
  | modified
  /-- Added file (`A`). -/
  | added
  /-- Deleted file (`D`). -/
  | deleted
  /-- Renamed file (`R`). -/
  | renamed
  /-- Copied file (`C`). -/
  | copied
  /-- Type-changed entry (`T`). -/
  | typeChanged
  /-- Untracked entry (`?`). -/
  | untracked
  /-- Ignored entry (`!`). -/
  | ignored
  /-- Unmerged conflict entry (`U`). -/
  | unmerged
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Single status entry parsed from `git status --porcelain=v1 -z`. -/
structure StatusEntry where
  /-- Index (staged) status code, or `none` when unchanged in the index. -/
  indexStatus : Option StatusKind
  /-- Working-tree (unstaged) status code, or `none` when unchanged in the worktree. -/
  worktreeStatus : Option StatusKind
  /-- Current or destination path relative to the repository root. -/
  path : String
  /-- Original source path for `renamed` or `copied` entries. -/
  origPath : Option String := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- File diff classification from `git diff --name-status -z`. -/
inductive DiffKind where
  /-- Added file (`A`). -/
  | added
  /-- Modified file (`M`). -/
  | modified
  /-- Deleted file (`D`). -/
  | deleted
  /-- Renamed file (`R<score>`). -/
  | renamed (score : Nat)
  /-- Copied file (`C<score>`). -/
  | copied (score : Nat)
  /-- Type-changed entry (`T`). -/
  | typeChanged
  /-- Unmerged entry (`U`). -/
  | unmerged
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Single diff entry parsed from `git diff --name-status -z`. -/
structure DiffEntry where
  /-- Change kind and optional similarity score. -/
  kind : DiffKind
  /-- Current or destination path. -/
  path : String
  /-- Original source path for `renamed` or `copied` entries. -/
  origPath : Option String := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Worktree metadata parsed from `git worktree list --porcelain -z`. -/
structure WorktreeInfo where
  /-- Absolute path of the worktree root. -/
  path : String
  /-- Checked-out commit ID, or `none` for an unborn branch or bare worktree without `HEAD`. -/
  head? : Option CommitId
  /-- Attached local branch name (`refs/heads/` stripped), or `none` when detached or bare. -/
  branch? : Option RefName
  /-- Whether the worktree entry represents a bare repository. -/
  isBare : Bool := false
  /-- Whether the worktree is in detached `HEAD` state. -/
  isDetached : Bool := false
  /-- Whether the worktree is locked. -/
  isLocked : Bool := false
  /-- Optional lock reason string. -/
  lockReason : Option String := none
  /-- Whether the worktree is prunable. -/
  isPrunable : Bool := false
  /-- Optional prunable reason string. -/
  pruneReason : Option String := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Reset mode for `git reset`. -/
inductive ResetMode where
  /-- Move `HEAD`/branch only (`--soft`). -/
  | soft
  /-- Move `HEAD`/branch and reset index (`--mixed`). -/
  | mixed
  /-- Move `HEAD`/branch and reset index and working tree (`--hard`). -/
  | hard
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Target specification for `git checkout`. -/
inductive CheckoutTarget where
  /-- Check out a validated branch reference. -/
  | branch (name : RefName)
  /-- Check out a specific commit ID (detached `HEAD`). -/
  | commit (id : CommitId)
  /-- Check out an arbitrary validated revision specification. -/
  | ref (spec : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Options for creating a commit via `git commit`. -/
structure CommitOptions where
  /-- Non-empty commit message without NUL bytes. -/
  message : String
  /-- Allow creating a commit with no staged changes (`--allow-empty`). -/
  allowEmpty : Bool := false
  /-- Optional author and committer name passed via `GIT_AUTHOR_NAME` / `GIT_COMMITTER_NAME`. -/
  authorName : Option String := none
  /-- Optional author and committer email passed via `GIT_AUTHOR_EMAIL` / `GIT_COMMITTER_EMAIL`. -/
  authorEmail : Option String := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Options for non-interactive `git clone`. -/
structure CloneOptions where
  /-- Create a bare clone (`--bare`). -/
  bare : Bool := false
  /-- Optional branch name to check out (`--branch`). -/
  branch? : Option String := none
  /-- Optional shallow history depth (`--depth`, must be positive if set). -/
  depth? : Option Nat := none
  /-- Clone only a single branch (`--single-branch`). -/
  singleBranch : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Options for `git worktree add`. -/
structure WorktreeAddOptions where
  /-- Target directory path for the new worktree. -/
  path : String
  /-- Optional existing branch, commit, or revision to check out. -/
  target? : Option String := none
  /-- Optional new branch name to create (`-b`). -/
  newBranch? : Option RefName := none
  /-- Detach `HEAD` in the new worktree (`--detach`). -/
  detach : Bool := false
  /-- Force worktree creation (`--force`). -/
  force : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Closed classification of errors produced by `LeanSwe.Git`. -/
inductive GitErrorKind where
  /-- Target path is not a Git repository or lacks a working tree when required. -/
  | notARepo
  /-- Invalid or unknown revision, commit, or reference name. -/
  | invalidRef
  /-- Invalid file or repository path argument. -/
  | invalidPath
  /-- Invalid operation arguments or incompatible options. -/
  | invalidInput
  /-- Operation refused because the worktree has uncommitted or unmerged changes. -/
  | dirtyWorktree
  /-- Commit requested with empty staging area and `allowEmpty = false`. -/
  | nothingToCommit
  /-- Target branch is currently checked out in a worktree. -/
  | branchInUse
  /-- Target branch, tag, or path already exists. -/
  | alreadyExists
  /-- Requested path, file, or branch does not exist. -/
  | notFound
  /-- Operation encountered merge or index conflicts. -/
  | conflict
  /-- Underlying `git` subprocess exceeded its timeout. -/
  | timeout
  /-- Underlying `git` invocation failed or could not be executed. -/
  | commandFailed
  /-- Failed to decode or parse `git` porcelain output. -/
  | parseError
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Normalized error returned by `LeanSwe.Git` operations. -/
structure GitError where
  /-- Machine-checkable error category. -/
  kind : GitErrorKind
  /-- Git subcommand or program label associated with the failure. -/
  command : Option String := none
  /-- Child process exit code when available. -/
  exitCode : Option Int := none
  /-- Captured stderr text when available. -/
  stderr : Option String := none
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Raw `git` CLI request passed across the `RawGitOpsM` trust boundary. -/
structure GitRawRequest where
  /-- Optional working directory (`chdir`) for the invocation. -/
  cwd : Option String := none
  /-- Explicit `git` argument vector. -/
  args : Array String
  /-- Standard input bytes sent to `git`. -/
  stdin : ByteArray := ByteArray.empty
  /-- Optional timeout in milliseconds. -/
  timeoutMs : Option Nat := some 30000
  /-- Optional maximum captured output bytes across stdout and stderr. -/
  maxOutputBytes : Option Nat := some 16777216
  /-- Caller-supplied extra environment entries prior to `cleanGitEnv` filtering. -/
  extraEnv : Array (String × Option String) := #[]
  deriving BEq, DecidableEq

instance : Repr GitRawRequest where
  reprPrec r _ :=
    Std.Format.bracket "{" (
      Std.Format.joinSep [
        "cwd := " ++ repr r.cwd,
        "args := " ++ repr r.args,
        "stdin := " ++ reprByteArray r.stdin,
        "timeoutMs := " ++ repr r.timeoutMs,
        "maxOutputBytes := " ++ repr r.maxOutputBytes,
        "extraEnv := " ++ repr r.extraEnv
      ] (", " ++ Std.Format.line)
    ) "}"

/-- Raw output captured from a completed `git` subprocess. -/
structure GitRawOutput where
  /-- Process exit status code. -/
  exitCode : Int
  /-- Captured standard output bytes. -/
  stdout : ByteArray
  /-- Captured standard error bytes. -/
  stderr : ByteArray
  deriving BEq, DecidableEq

instance : Repr GitRawOutput where
  reprPrec r _ :=
    Std.Format.bracket "{" (
      Std.Format.joinSep [
        "exitCode := " ++ repr r.exitCode,
        "stdout := " ++ reprByteArray r.stdout,
        "stderr := " ++ reprByteArray r.stderr
      ] (", " ++ Std.Format.line)
    ) "}"

/-- Minimal raw OS/process boundary for running `git`, parameterized over `m`. -/
structure RawGitOpsM (m : Type → Type) where
  /-- List inherited environment `(key, value)` pairs for `GIT_*` sanitization. -/
  listEnv : m (Except GitError (Array (String × String)))
  /-- Execute `git` with sanitized environment overrides and explicit request parameters. -/
  execGit : Array (String × Option String) → GitRawRequest → m (Except GitError GitRawOutput)

/-- Concrete `IO` raw boundary type for `LeanSwe.Git`. -/
abbrev RawGitOps := RawGitOpsM IO

/-- Public non-interactive Git API record parameterized over effect monad `m`. -/
structure GitApiM (m : Type → Type) where
  /-- Return `true` if `repoPath` is inside a bare or non-bare Git repository, `false` otherwise. -/
  isRepo : String → m (Except GitError Bool)
  /-- Return the absolute working-tree top-level directory (`notARepo` on bare repos). -/
  repoRoot : String → m (Except GitError String)
  /-- Return the absolute shared common `.git` directory across all worktrees. -/
  commonDir : String → m (Except GitError String)
  /-- Return the commit ID of `HEAD`, or `none` when `HEAD` is on an unborn branch. -/
  headCommit? : String → m (Except GitError (Option CommitId))
  /-- Return the attached branch name of `HEAD`, or `none` when `HEAD` is detached. -/
  headBranch? : String → m (Except GitError (Option RefName))
  /-- Return the combined attached/detached `HeadState` of `HEAD`. -/
  headState : String → m (Except GitError HeadState)
  /-- Resolve a revision string to a validated `CommitId`. -/
  revParseCommit : String → String → m (Except GitError CommitId)
  /-- Return `true` iff `ancestor` is an ancestor of `descendant`. -/
  isAncestor : String → CommitId → CommitId → m (Except GitError Bool)
  /-- Return a minimal common ancestor commit of two commits, or `none` if histories are disjoint. -/
  mergeBase? : String → CommitId → CommitId → m (Except GitError (Option CommitId))
  /-- Return working-tree and index status entries via `git status --porcelain=v1 -z`. -/
  status : String → m (Except GitError (Array StatusEntry))
  /-- Return file change summaries between `revA` and `revB?` (or working tree when `none`). Path arguments are matched literally via `GIT_LITERAL_PATHSPECS=1`: wildcards (`*`, `?`, `[`, `\`) and leading `:` magic prefixes are NOT expanded; directories (e.g. `.` and `src/`) still diff all contents inside them. -/
  diffNameStatus : String → String → Option String → Array String → m (Except GitError (Array DiffEntry))
  /-- List main and linked worktrees via `git worktree list --porcelain -z`. -/
  listWorktrees : String → m (Except GitError (Array WorktreeInfo))
  /-- Read blob bytes for `relPath` at `rev`, returning `none` if absent or a directory tree. -/
  showFile? : String → String → String → m (Except GitError (Option ByteArray))
  /-- Initialize a new Git repository at `path`. -/
  init : String → Bool → Option RefName → m (Except GitError Unit)
  /-- Clone a repository non-interactively from `source` to `target`. -/
  clone : String → String → CloneOptions → m (Except GitError Unit)
  /-- Stage explicit paths or all changes in the repository. Path arguments are matched literally via `GIT_LITERAL_PATHSPECS=1`: wildcards (`*`, `?`, `[`, `\`) and leading `:` magic prefixes are NOT expanded; directories (e.g. `.` and `src/`) still stage all contents inside them. -/
  add : String → Array String → Bool → m (Except GitError Unit)
  /-- Create a commit with `CommitOptions` and return the resulting `CommitId`. -/
  commit : String → CommitOptions → m (Except GitError CommitId)
  /-- Create (or reset when `force = true`) a branch at optional `startPoint?`. -/
  createBranch : String → RefName → Option String → Bool → m (Except GitError Unit)
  /-- Delete a local branch. -/
  deleteBranch : String → RefName → Bool → m (Except GitError Unit)
  /-- Check out a branch, commit, or validated revision. -/
  checkout : String → CheckoutTarget → Bool → m (Except GitError Unit)
  /-- Switch to an existing or newly created branch. -/
  switch : String → RefName → Bool → Option String → Bool → m (Except GitError Unit)
  /-- Reset `HEAD` (and optionally index/worktree) to `rev`. -/
  reset : String → ResetMode → String → m (Except GitError Unit)
  /-- Fetch updates non-interactively from `remote` and optional `refspec?`. -/
  fetch : String → String → Option String → Bool → m (Except GitError Unit)
  /-- Add a new linked worktree. -/
  worktreeAdd : String → WorktreeAddOptions → m (Except GitError Unit)
  /-- Remove an existing linked worktree. -/
  worktreeRemove : String → String → Bool → m (Except GitError Unit)
  /-- Bracketed temporary worktree execution guaranteeing cleanup via `[MonadFinally m]`. -/
  withWorktree : {α : Type} → String → WorktreeAddOptions → (String → m (Except GitError α)) → m (Except GitError α)

/-- Concrete `IO` API bundle for `LeanSwe.Git`. -/
abbrev GitApi := GitApiM IO

end LeanSwe.Git
