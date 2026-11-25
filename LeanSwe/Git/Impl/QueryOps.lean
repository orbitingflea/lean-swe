import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Impl.Helpers

namespace LeanSwe.Git.Impl

open LeanSwe.Git
open LeanSwe.Git.Model

/-- Probe whether `repoPath` is inside a Git repository (`notARepo` maps to `false`). -/
def isRepoImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m) (repoPath : String) :
    m (Except GitError Bool) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    match ← runGitRaw ops { cwd := some repoPath, args := #["rev-parse", "--git-dir"] } with
    | .error e => return .error e
    | .ok out =>
      if out.exitCode == 0 then
        return .ok true
      else
        let err := classifyError "rev-parse" out
        if err.kind == .notARepo then
          return .ok false
        else
          return .error err

/-- Resolve the absolute working-tree top-level directory (`notARepo` for bare repos). -/
def repoRootImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m) (repoPath : String) :
    m (Except GitError String) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    match ← runGitChecked ops "rev-parse"
        { cwd := some repoPath, args := #["rev-parse", "--path-format=absolute", "--show-toplevel"] } with
    | .error e => return .error e
    | .ok out =>
      match decodeUtf8Checked out.stdout with
      | .error e => return .error e
      | .ok s => return .ok (stripSingleTrailingLf s)

/-- Resolve the absolute shared `.git` common directory across all worktrees. -/
def commonDirImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m) (repoPath : String) :
    m (Except GitError String) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    match ← runGitChecked ops "rev-parse"
        { cwd := some repoPath, args := #["rev-parse", "--path-format=absolute", "--git-common-dir"] } with
    | .error e => return .error e
    | .ok out =>
      match decodeUtf8Checked out.stdout with
      | .error e => return .error e
      | .ok s => return .ok (stripSingleTrailingLf s)

/-- Resolve `HEAD` commit ID, returning `none` when the repository is on an unborn branch. -/
def headCommitImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m) (repoPath : String) :
    m (Except GitError (Option CommitId)) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    match ← runGitRaw ops
        { cwd := some repoPath, args := #["rev-parse", "-q", "--verify", "HEAD^{commit}"] } with
    | .error e => return .error e
    | .ok out =>
      if out.exitCode == 0 then
        match decodeUtf8Checked out.stdout with
        | .error e => return .error e
        | .ok s =>
          match mkCommitId (trimTrailingNewlines s) with
          | .error e => return .error e
          | .ok cid => return .ok (some cid)
      else
        let err := classifyError "rev-parse" out
        if err.kind == .notARepo then
          return .error err
        else if out.exitCode == 1 && trimAsciiWhitespace (decodeUtf8Lossy out.stderr) == "" then
          match ← runGitChecked ops "rev-parse"
              { cwd := some repoPath, args := #["rev-parse", "--git-dir"] } with
          | .error re => return .error re
          | .ok _ => return .ok none
        else
          return .error err

/-- Resolve the currently attached branch name of `HEAD`, or `none` when detached. -/
def headBranchImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m) (repoPath : String) :
    m (Except GitError (Option RefName)) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    match ← runGitRaw ops
        { cwd := some repoPath, args := #["symbolic-ref", "--quiet", "HEAD"] } with
    | .error e => return .error e
    | .ok out =>
      if out.exitCode == 0 then
        match decodeUtf8Checked out.stdout with
        | .error e => return .error e
        | .ok s =>
          let raw := trimTrailingNewlines s
          let stripped := if raw.startsWith "refs/heads/" then String.ofList (raw.toList.drop 11) else raw
          match mkRefName stripped with
          | .error e => return .error e
          | .ok ref => return .ok (some ref)
      else
        let err := classifyError "symbolic-ref" out
        if err.kind == .notARepo then
          return .error err
        else if out.exitCode == 1 && trimAsciiWhitespace (decodeUtf8Lossy out.stderr) == "" then
          match ← runGitChecked ops "rev-parse"
              { cwd := some repoPath, args := #["rev-parse", "--git-dir"] } with
          | .error re => return .error re
          | .ok _ => return .ok none
        else
          return .error err

/-- Compute combined `HeadState` from `headBranch?` and `headCommit?`. -/
def headStateImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m) (repoPath : String) :
    m (Except GitError HeadState) := do
  match ← headBranchImpl ops repoPath with
  | .error e => return .error e
  | .ok (some b) =>
    match ← headCommitImpl ops repoPath with
    | .error e => return .error e
    | .ok c? => return .ok (.attached b c?)
  | .ok none =>
    match ← headCommitImpl ops repoPath with
    | .error e => return .error e
    | .ok (some c) => return .ok (.detached c)
    | .ok none => return .error { kind := .invalidRef, message := "detached HEAD has no commit" }

/-- Resolve a validated revision specification to a `CommitId`. -/
def revParseCommitImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath rev : String) : m (Except GitError CommitId) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    if !isValidRevSpec rev then
      return .error { kind := .invalidInput, message := s!"invalid revision specification: '{rev}'" }
    match ← runGitRaw ops
        { cwd := some repoPath, args := #["rev-parse", "-q", "--verify", rev ++ "^{commit}"] } with
    | .error e => return .error e
    | .ok out =>
      if out.exitCode == 0 then
        match decodeUtf8Checked out.stdout with
        | .error e => return .error e
        | .ok s => return mkCommitId (trimTrailingNewlines s)
      else
        let err := classifyError "rev-parse" out
        if err.kind == .notARepo then
          return .error err
        else if err.kind == .commandFailed &&
            !hasFatalOrErrorChars (sanitizeLowerForClassify (decodeUtf8Lossy out.stderr)) then
          return .error
            { kind := .invalidRef
              command := some "rev-parse"
              exitCode := some out.exitCode
              message := s!"unknown or unborn revision: '{rev}'" }
        else
          return .error err

/-- Return `true` iff `ancestor` is an ancestor of `descendant`. -/
def isAncestorImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath : String) (ancestor descendant : CommitId) : m (Except GitError Bool) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    if !isValidCommitIdStr ancestor.hex || !isValidCommitIdStr descendant.hex then
      return .error { kind := .invalidRef, message := "invalid commit ID argument" }
    match ← runGitRaw ops
        { cwd := some repoPath, args := #["merge-base", "--is-ancestor", ancestor.hex, descendant.hex] } with
    | .error e => return .error e
    | .ok out =>
      if out.exitCode == 0 then
        return .ok true
      else if out.exitCode == 1 && (classifyError "merge-base" out).kind == .commandFailed &&
          !hasFatalOrErrorChars (sanitizeLowerForClassify (decodeUtf8Lossy out.stderr)) then
        return .ok false
      else
        return .error (classifyError "merge-base" out)

/-- Compute a merge base of two commits, returning `none` if their histories are disjoint. -/
def mergeBaseImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath : String) (a b : CommitId) : m (Except GitError (Option CommitId)) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    if !isValidCommitIdStr a.hex || !isValidCommitIdStr b.hex then
      return .error { kind := .invalidRef, message := "invalid commit ID argument" }
    match ← runGitRaw ops
        { cwd := some repoPath, args := #["merge-base", a.hex, b.hex] } with
    | .error e => return .error e
    | .ok out =>
      if out.exitCode == 0 then
        match decodeUtf8Checked out.stdout with
        | .error e => return .error e
        | .ok s =>
          match mkCommitId (trimTrailingNewlines s) with
          | .error e => return .error e
          | .ok cid => return .ok (some cid)
      else if out.exitCode == 1 && (classifyError "merge-base" out).kind == .commandFailed &&
          !hasFatalOrErrorChars (sanitizeLowerForClassify (decodeUtf8Lossy out.stderr)) then
        return .ok none
      else
        return .error (classifyError "merge-base" out)

/-- Query `git status --porcelain=v1 --untracked-files=normal -z` and parse all entries. -/
def statusImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m) (repoPath : String) :
    m (Except GitError (Array StatusEntry)) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    match ← runGitChecked ops "status"
        { cwd := some repoPath, args := #["status", "--porcelain=v1", "--untracked-files=normal", "-z"] } with
    | .error e => return .error e
    | .ok out => return parsePorcelainStatusZ out.stdout

/-- Query `git diff --name-status -z` between `revA` and optional `revB?`. -/
def diffNameStatusImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath revA : String) (revB? : Option String) (paths : Array String) :
    m (Except GitError (Array DiffEntry)) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    if !isValidStrictRevSpec revA then
      return .error { kind := .invalidInput, message := s!"invalid revision: '{revA}'" }
    let revBArgs : Except GitError (Array String) :=
      match revB? with
      | none => .ok #[]
      | some rb =>
        if isValidStrictRevSpec rb then
          .ok #[rb]
        else
          .error { kind := .invalidInput, message := s!"invalid revision: '{rb}'" }
    match revBArgs with
    | .error e => return .error e
    | .ok rbArgs =>
      if !paths.all isValidPathArg then
        return .error { kind := .invalidPath, message := "invalid diff path argument" }
      let args := #["diff", "--name-status", "-z", revA] ++ rbArgs ++ #["--"] ++ paths
      match ← runGitChecked ops "diff" { cwd := some repoPath, args := args } with
      | .error e => return .error e
      | .ok out => return parseDiffNameStatusZ out.stdout

/-- Query `git worktree list --porcelain -z` and parse all worktree stanzas. -/
def listWorktreesImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m) (repoPath : String) :
    m (Except GitError (Array WorktreeInfo)) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    match ← runGitChecked ops "worktree"
        { cwd := some repoPath, args := #["worktree", "list", "--porcelain", "-z"] } with
    | .error e => return .error e
    | .ok out => return parseWorktreeListPorcelain out.stdout

/-- Read blob bytes at `rev:relPath`, returning `none` when absent or when the object is a tree/commit. -/
def showFileImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath rev relPath : String) : m (Except GitError (Option ByteArray)) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    if !isValidStrictRevSpec rev then
      return .error { kind := .invalidInput, message := s!"invalid revision: '{rev}'" }
    match validateRelRepoPath relPath with
    | .error e => return .error e
    | .ok () =>
      match ← revParseCommitImpl ops repoPath rev with
      | .error e => return .error e
      | .ok cid =>
        let spec := s!"{cid.hex}:{relPath}"
        match ← runGitRaw ops { cwd := some repoPath, args := #["cat-file", "-t", spec] } with
        | .error e => return .error e
        | .ok typeOut =>
          if typeOut.exitCode != 0 then
            let errText := decodeUtf8Lossy typeOut.stderr
            if errText.startsWith s!"fatal: path '{relPath}' " then
              return .ok none
            let err := classifyError "cat-file" typeOut
            if err.kind == .notARepo then
              return .error err
            else
              return .ok none
          else
            match decodeUtf8Checked typeOut.stdout with
            | .error e => return .error e
            | .ok objType =>
              if trimAsciiWhitespace objType != "blob" then
                return .ok none
              else
                match ← runGitChecked ops "cat-file"
                    { cwd := some repoPath, args := #["cat-file", "blob", spec] } with
                | .error e => return .error e
                | .ok blobOut => return .ok (some blobOut.stdout)

end LeanSwe.Git.Impl
