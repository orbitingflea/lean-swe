import LeanSwe.Git.Types
import LeanSwe.Git.Impl.Helpers
import LeanSwe.Git.Impl.QueryOps

namespace LeanSwe.Git.Impl

open LeanSwe.Git

/-- Initialize a new repository at `path`. -/
def initImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (path : String) (bare : Bool) (initialBranch? : Option RefName) : m (Except GitError Unit) := do
  match validateRepoPath path with
  | .error e => return .error e
  | .ok () =>
    let branchArgs : Except GitError (Array String) :=
      match initialBranch? with
      | none => .ok #[]
      | some b =>
        if isValidRefNameStrImpl b.raw then .ok #["-b", b.raw]
        else .error { kind := .invalidRef, message := s!"invalid initial branch name: '{b.raw}'" }
    match branchArgs with
    | .error e => return .error e
    | .ok bArgs =>
      let args := #["init"] ++ (if bare then #["--bare"] else #[]) ++ bArgs ++ #["--", path]
      match ← runGitChecked ops "init" { cwd := none, args := args } with
      | .error e => return .error e
      | .ok _ => return .ok ()

/-- Clone a repository non-interactively from `source` to `target`. -/
def cloneImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (source target : String) (opts : CloneOptions) : m (Except GitError Unit) := do
  match validateCloneEndpointImpl source, validateCloneEndpointImpl target with
  | .error e, _ => return .error e
  | _, .error e => return .error e
  | .ok (), .ok () =>
    match opts.depth? with
    | some 0 => return .error { kind := .invalidInput, message := "clone depth must be positive" }
    | _ => pure ()
    let branchArgs : Except GitError (Array String) :=
      match opts.branch? with
      | none => .ok #[]
      | some b =>
        if isValidRefNameStrImpl b then .ok #["--branch", b]
        else .error { kind := .invalidRef, message := s!"invalid clone branch: '{b}'" }
    match branchArgs with
    | .error e => return .error e
    | .ok bArgs =>
      let depthArgs := match opts.depth? with | none => #[] | some d => #["--depth", toString d]
      let args :=
        #["clone"] ++ (if opts.bare then #["--bare"] else #[]) ++
        (if opts.singleBranch then #["--single-branch"] else #[]) ++
        depthArgs ++ bArgs ++ #["--", source, target]
      match ← runGitChecked ops "clone" { cwd := none, args := args } with
      | .error e => return .error e
      | .ok _ => return .ok ()

/-- Stage explicit paths or all changes (`all = true`). -/
def addImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath : String) (paths : Array String) (all : Bool) : m (Except GitError Unit) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    if !all && paths.isEmpty then
      return .error { kind := .invalidInput, message := "add requires non-empty paths or all = true" }
    if !paths.all isValidPathArgImpl then
      return .error { kind := .invalidPath, message := "invalid path passed to git add" }
    let args :=
      if all then
        if paths.isEmpty then #["add", "--all"] else #["add", "--all", "--"] ++ paths
      else
        #["add", "--"] ++ paths
    match ← runGitChecked ops "add" { cwd := some repoPath, args := args } with
    | .error e => return .error e
    | .ok _ => return .ok ()

/-- Create a commit with validated message and optional author/committer overrides. -/
def commitImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath : String) (opts : CommitOptions) : m (Except GitError CommitId) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    match validateCommitOptionsImpl opts with
    | .error e => return .error e
    | .ok () =>
      let nEnv := match opts.authorName with
        | none => #[]
        | some n => #[("GIT_AUTHOR_NAME", some n), ("GIT_COMMITTER_NAME", some n)]
      let eEnv := match opts.authorEmail with
        | none => #[]
        | some em => #[("GIT_AUTHOR_EMAIL", some em), ("GIT_COMMITTER_EMAIL", some em)]
      let args := #["commit", "--no-gpg-sign", "-m", opts.message] ++
        (if opts.allowEmpty then #["--allow-empty"] else #[])
      match ← runGitChecked ops "commit"
          { cwd := some repoPath, args := args, extraEnv := nEnv ++ eEnv } with
      | .error e => return .error e
      | .ok _ => revParseCommitImpl ops repoPath "HEAD"

/-- Create (or reset with `force = true`) a local branch. -/
def createBranchImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath : String) (branch : RefName) (startPoint? : Option String) (force : Bool) :
    m (Except GitError Unit) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    if !isValidRefNameStrImpl branch.raw then
      return .error { kind := .invalidRef, message := s!"invalid branch name: '{branch.raw}'" }
    let spArgs : Except GitError (Array String) :=
      match startPoint? with
      | none => .ok #[]
      | some sp =>
        if isValidStrictRevSpecImpl sp then
          .ok #[sp]
        else
          .error { kind := .invalidInput, message := s!"invalid startPoint: '{sp}'" }
    match spArgs with
    | .error e => return .error e
    | .ok sArgs =>
      let args := #["branch"] ++ (if force then #["-f"] else #[]) ++ #["--", branch.raw] ++ sArgs
      match ← runGitChecked ops "branch" { cwd := some repoPath, args := args } with
      | .error e => return .error e
      | .ok _ => return .ok ()

/-- Delete a local branch safely (`-d`) or forcefully (`-D`). -/
def deleteBranchImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath : String) (branch : RefName) (force : Bool) : m (Except GitError Unit) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    if !isValidRefNameStrImpl branch.raw then
      return .error { kind := .invalidRef, message := s!"invalid branch name: '{branch.raw}'" }
    let args := #["branch", if force then "-D" else "-d", "--", branch.raw]
    match ← runGitChecked ops "branch" { cwd := some repoPath, args := args } with
    | .error e => return .error e
    | .ok _ => return .ok ()

/-- Check out a branch, commit (`--detach`), or validated revision target. -/
def checkoutImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath : String) (target : CheckoutTarget) (force : Bool) : m (Except GitError Unit) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    let targetArgs : Except GitError (Array String) :=
      match target with
      | .branch b =>
        if isValidRefNameStrImpl b.raw then
          .ok #[b.raw, "--"]
        else
          .error { kind := .invalidRef, message := s!"invalid branch name: '{b.raw}'" }
      | .commit cid =>
        if isValidCommitIdStrImpl cid.hex then
          .ok #["--detach", cid.hex, "--"]
        else
          .error { kind := .invalidRef, message := s!"invalid commit ID: '{cid.hex}'" }
      | .ref spec =>
        if isValidStrictRevSpecImpl spec then
          .ok #[spec, "--"]
        else
          .error { kind := .invalidInput, message := s!"invalid revision: '{spec}'" }
    match targetArgs with
    | .error e => return .error e
    | .ok tArgs =>
      let args := #["checkout"] ++ (if force then #["--force"] else #[]) ++ tArgs
      match ← runGitChecked ops "checkout" { cwd := some repoPath, args := args } with
      | .error e => return .error e
      | .ok _ => return .ok ()

/-- Switch to an existing branch or create and switch (`create = true`). -/
def switchImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath : String) (branch : RefName) (create : Bool) (startPoint? : Option String)
    (force : Bool) : m (Except GitError Unit) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    if !isValidRefNameStrImpl branch.raw then
      return .error { kind := .invalidRef, message := s!"invalid branch name: '{branch.raw}'" }
    if !create && startPoint?.isSome then
      return .error { kind := .invalidInput, message := "switch startPoint requires create = true" }
    let spArgs : Except GitError (Array String) :=
      match startPoint? with
      | none => .ok #[]
      | some sp =>
        if isValidStrictRevSpecImpl sp then
          .ok #[sp]
        else
          .error { kind := .invalidInput, message := s!"invalid startPoint: '{sp}'" }
    match spArgs with
    | .error e => return .error e
    | .ok sArgs =>
      let args :=
        #["switch"] ++
        (if force then #["--force"] else #[]) ++
        (if create then #[if force then "-C" else "-c", branch.raw] else #[branch.raw]) ++
        sArgs
      match ← runGitChecked ops "switch" { cwd := some repoPath, args := args } with
      | .error e => return .error e
      | .ok _ => return .ok ()

/-- Reset `HEAD` (and optionally index/working tree) to `rev`. -/
def resetImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath : String) (mode : ResetMode) (rev : String) : m (Except GitError Unit) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    if !isValidStrictRevSpecImpl rev then
      return .error { kind := .invalidInput, message := s!"invalid revision: '{rev}'" }
    let modeFlag :=
      match mode with
      | .soft => "--soft"
      | .mixed => "--mixed"
      | .hard => "--hard"
    let args := #["reset", modeFlag, rev, "--"]
    match ← runGitChecked ops "reset" { cwd := some repoPath, args := args } with
    | .error e => return .error e
    | .ok _ => return .ok ()

/-- Fetch non-interactively from `remote` with optional `refspec?` and `prune`. -/
def fetchImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath remote : String) (refspec? : Option String) (prune : Bool) :
    m (Except GitError Unit) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    if !isValidRemoteOrRefspecImpl remote then
      return .error { kind := .invalidInput, message := s!"invalid remote name: '{remote}'" }
    let refArgs : Except GitError (Array String) :=
      match refspec? with
      | none => .ok #[]
      | some r =>
        if isValidRemoteOrRefspecImpl r then
          .ok #[r]
        else
          .error { kind := .invalidInput, message := s!"invalid refspec: '{r}'" }
    match refArgs with
    | .error e => return .error e
    | .ok rArgs =>
      let args := #["fetch"] ++ (if prune then #["--prune"] else #[]) ++ #[remote] ++ rArgs
      match ← runGitChecked ops "fetch" { cwd := some repoPath, args := args } with
      | .error e => return .error e
      | .ok _ => return .ok ()

/-- Create a linked worktree via `git worktree add`. -/
def worktreeAddImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath : String) (opts : WorktreeAddOptions) : m (Except GitError Unit) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    match validateRepoPath opts.path with
    | .error e => return .error e
    | .ok () =>
      if opts.detach && opts.newBranch?.isSome then
        return .error { kind := .invalidInput, message := "worktreeAdd cannot combine detach and newBranch" }
      let branchArgs : Except GitError (Array String) :=
        match opts.newBranch? with
        | none => .ok #[]
        | some b =>
          if isValidRefNameStrImpl b.raw then .ok #["-b", b.raw]
          else .error { kind := .invalidRef, message := s!"invalid branch name: '{b.raw}'" }
      match branchArgs with
      | .error e => return .error e
      | .ok bArgs =>
        let targetArgs : Except GitError (Array String) :=
          match opts.target? with
          | none => .ok #[]
          | some t =>
            if isValidStrictRevSpecImpl t then .ok #[t]
            else .error { kind := .invalidInput, message := s!"invalid worktree target: '{t}'" }
        match targetArgs with
        | .error e => return .error e
        | .ok tArgs =>
          let args := #["worktree", "add"] ++ (if opts.force then #["--force"] else #[]) ++
            (if opts.detach then #["--detach"] else #[]) ++ bArgs ++ #["--", opts.path] ++ tArgs
          match ← runGitChecked ops "worktree" { cwd := some repoPath, args := args } with
          | .error e => return .error e
          | .ok _ => return .ok ()

/-- Remove a linked worktree via `git worktree remove`. -/
def worktreeRemoveImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath wtPath : String) (force : Bool) : m (Except GitError Unit) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    match validateRepoPath wtPath with
    | .error e => return .error e
    | .ok () =>
      let args := #["worktree", "remove"] ++ (if force then #["--force"] else #[]) ++ #["--", wtPath]
      match ← runGitChecked ops "worktree" { cwd := some repoPath, args := args } with
      | .error e => return .error e
      | .ok _ => return .ok ()

/-- Bracketed temporary worktree helper guaranteeing `worktreeRemove` cleanup via `MonadFinally`. -/
def withWorktreeImpl {m : Type → Type} [Monad m] [MonadFinally m] (ops : RawGitOpsM m)
    {α : Type} (repoPath : String) (opts : WorktreeAddOptions)
    (action : String → m (Except GitError α)) : m (Except GitError α) := do
  match ← worktreeAddImpl ops repoPath opts with
  | .error e => return .error e
  | .ok () =>
    let (actRes, cleanRes) ← MonadFinally.tryFinally' (action opts.path) fun _ =>
      worktreeRemoveImpl ops repoPath opts.path opts.force
    match actRes, cleanRes with
    | .ok a, .ok () => return .ok a
    | .ok _, .error ce => return .error ce
    | .error ae, _ => return .error ae

end LeanSwe.Git.Impl
