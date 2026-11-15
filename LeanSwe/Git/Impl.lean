import LeanSwe.Git.Types
import LeanSwe.Git.Model

namespace LeanSwe.Git.Impl

open LeanSwe.Git
open LeanSwe.Git.Model

/-- Convert a single ASCII uppercase character to lowercase. -/
def asciiLowerChar (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- Convert ASCII uppercase letters in `s` to lowercase. -/
def asciiLower (s : String) : String :=
  String.ofList (s.toList.map asciiLowerChar)

/-- Return `true` iff `needle` appears in `haystack` under ASCII case-insensitive matching. -/
def containsSubstrCI (needle haystack : String) : Bool :=
  hasSubstrChars (asciiLower needle).toList (asciiLower haystack).toList

/-- Decode `ByteArray` as UTF-8, substituting an empty string if invalid. -/
def decodeUtf8Lossy (bytes : ByteArray) : String :=
  (String.fromUTF8? bytes).getD ""

/-- Decode `ByteArray` as UTF-8, failing with `.parseError` if invalid. -/
def decodeUtf8Checked (bytes : ByteArray) : Except GitError String :=
  match String.fromUTF8? bytes with
  | some s => .ok s
  | none => .error { kind := .parseError, message := "invalid UTF-8 in git output" }

/-- Strip trailing ASCII CR and LF characters from `s`. -/
def trimTrailingNewlines (s : String) : String :=
  let rev := s.toList.reverse.dropWhile (fun c => c == '\n' || c == '\r')
  String.ofList rev.reverse

/-- Strip leading and trailing ASCII whitespace from `s`. -/
def trimAsciiWhitespace (s : String) : String :=
  let dropL := s.toList.dropWhile isAsciiWhitespace
  String.ofList (dropL.reverse.dropWhile isAsciiWhitespace).reverse

/-- Ensure `msg` is non-empty, falling back to `fallback` when empty. -/
def ensureNonEmptyMsg (fallback msg : String) : String :=
  let t := trimAsciiWhitespace msg
  if t.isEmpty then fallback else t

/-- Validate all caller-supplied environment entries via `isValidEnvKey` and `isValidEnvVal?`. -/
def validateExtraEnv (extra : Array (String × Option String)) : Except GitError Unit :=
  if extra.all (fun kv => isValidEnvKey kv.1 && isValidEnvVal? kv.2) then
    .ok ()
  else
    .error { kind := .invalidInput, message := "invalid environment key or value" }

/-- Validate `cwd` if present via `isValidPathArg`. -/
def validateCwd? : Option String → Except GitError Unit
  | none => .ok ()
  | some p =>
    if isValidPathArg p then
      .ok ()
    else
      .error { kind := .invalidPath, message := "invalid working directory path" }

/-- Classify a non-zero `git` subprocess result using both `stderr` and `stdout`. -/
def classifyError (cmd : String) (out : GitRawOutput) : GitError :=
  let errText := decodeUtf8Lossy out.stderr
  let outText := decodeUtf8Lossy out.stdout
  let combined := errText ++ "\n" ++ outText
  let kind :=
    if containsSubstrCI "not a git repository" combined ||
       containsSubstrCI "must be run in a work tree" combined then
      .notARepo
    else if containsSubstrCI "nothing to commit" combined ||
            containsSubstrCI "no changes added to commit" combined ||
            containsSubstrCI "nothing added to commit" combined then
      .nothingToCommit
    else if containsSubstrCI "is already used by worktree" combined ||
            containsSubstrCI "is already checked out" combined ||
            (containsSubstrCI "cannot delete branch" combined &&
              containsSubstrCI "used by worktree" combined) then
      .branchInUse
    else if containsSubstrCI "would be overwritten by" combined ||
            containsSubstrCI "local changes" combined ||
            containsSubstrCI "uncommitted changes" combined ||
            containsSubstrCI "contains modified or untracked files" combined then
      .dirtyWorktree
    else if containsSubstrCI "conflict" combined ||
            containsSubstrCI "unmerged" combined ||
            containsSubstrCI "needs merge" combined then
      .conflict
    else if containsSubstrCI "already exists" combined then
      .alreadyExists
    else if containsSubstrCI "unknown revision" combined ||
            containsSubstrCI "ambiguous argument" combined ||
            containsSubstrCI "not a valid object name" combined ||
            containsSubstrCI "not a valid commit name" combined ||
            containsSubstrCI "needed a single revision" combined ||
            containsSubstrCI "not a valid branch point" combined ||
            containsSubstrCI "could not parse object" combined ||
            containsSubstrCI "bad revision" combined ||
            containsSubstrCI "invalid reference" combined ||
            containsSubstrCI "unable to read tree" combined ||
            containsSubstrCI "reference is not a tree" combined ||
            containsSubstrCI "does not have any commits yet" combined ||
            containsSubstrCI "not a valid branch name" combined then
      .invalidRef
    else if (containsSubstrCI "pathspec" combined && containsSubstrCI "did not match" combined) ||
            containsSubstrCI "does not exist" combined ||
            containsSubstrCI "not a valid worktree" combined ||
            containsSubstrCI "no such file or directory" combined ||
            (containsSubstrCI "branch" combined && containsSubstrCI "not found" combined) then
      .notFound
    else
      .commandFailed
  let fallback := s!"git {cmd} failed with exit code {out.exitCode}"
  let primary :=
    let trimmedErr := trimAsciiWhitespace errText
    if trimmedErr.isEmpty then trimAsciiWhitespace outText else trimmedErr
  { kind := kind
    command := some cmd
    exitCode := some out.exitCode
    stderr := if errText.isEmpty then none else some errText
    message := ensureNonEmptyMsg fallback primary }

/-- Execute a raw `git` invocation with `GIT_*` sanitization and pre-execution path/env validation. -/
def runGitRaw {m : Type → Type} [Monad m] (ops : RawGitOpsM m) (req : GitRawRequest) :
    m (Except GitError GitRawOutput) := do
  match validateCwd? req.cwd with
  | .error e => return .error e
  | .ok () =>
    match validateExtraEnv req.extraEnv with
    | .error e => return .error e
    | .ok () =>
      if !req.args.all (fun a => !hasNulChar a.toList) then
        return .error { kind := .invalidInput, message := "git argument contains NUL byte" }
      match ← ops.listEnv with
      | .error e => return .error e
      | .ok inherited =>
        let envOverrides := cleanGitEnv inherited req.extraEnv
        ops.execGit envOverrides req

/-- Execute a raw `git` command and classify non-zero exits via `classifyError`. -/
def runGitChecked {m : Type → Type} [Monad m] (ops : RawGitOpsM m) (cmd : String)
    (req : GitRawRequest) : m (Except GitError GitRawOutput) := do
  match ← runGitRaw ops req with
  | .error e => return .error e
  | .ok out =>
    if out.exitCode == 0 then
      return .ok out
    else
      return .error (classifyError cmd out)

/-- Validate a repository directory path argument. -/
def validateRepoPath (repoPath : String) : Except GitError Unit :=
  if isValidPathArg repoPath then
    .ok ()
  else
    .error { kind := .invalidPath, message := "invalid repository path" }

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
      | .ok s => return .ok (trimTrailingNewlines s)

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
      | .ok s => return .ok (trimTrailingNewlines s)

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
        { cwd := some repoPath, args := #["symbolic-ref", "--quiet", "--short", "HEAD"] } with
    | .error e => return .error e
    | .ok out =>
      if out.exitCode == 0 then
        match decodeUtf8Checked out.stdout with
        | .error e => return .error e
        | .ok s =>
          match mkRefName (trimTrailingNewlines s) with
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
        else if err.kind == .commandFailed && trimAsciiWhitespace (decodeUtf8Lossy out.stderr) == "" then
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
      else if out.exitCode == 1 && trimAsciiWhitespace (decodeUtf8Lossy out.stderr) == "" then
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
      else if out.exitCode == 1 && trimAsciiWhitespace (decodeUtf8Lossy out.stderr) == "" then
        return .ok none
      else
        return .error (classifyError "merge-base" out)

/-- Query `git status --porcelain=v1 -z` and parse all entries. -/
def statusImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m) (repoPath : String) :
    m (Except GitError (Array StatusEntry)) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    match ← runGitChecked ops "status"
        { cwd := some repoPath, args := #["status", "--porcelain=v1", "-z"] } with
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
    if !isValidRelRepoPath relPath then
      return .error { kind := .invalidPath, message := s!"invalid repository relative path: '{relPath}'" }
    match ← revParseCommitImpl ops repoPath rev with
    | .error e => return .error e
    | .ok cid =>
      let spec := s!"{cid.hex}:{relPath}"
      match ← runGitRaw ops { cwd := some repoPath, args := #["cat-file", "-t", spec] } with
      | .error e => return .error e
      | .ok typeOut =>
        if typeOut.exitCode != 0 then
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

/-- Initialize a new repository at `path`. -/
def initImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (path : String) (bare : Bool) (initialBranch? : Option RefName) : m (Except GitError Unit) := do
  if !isValidPathArg path then
    return .error { kind := .invalidPath, message := "invalid repository init path" }
  let branchArgs : Except GitError (Array String) :=
    match initialBranch? with
    | none => .ok #[]
    | some b =>
      if isValidRefNameStr b.raw then
        .ok #["-b", b.raw]
      else
        .error { kind := .invalidRef, message := s!"invalid initial branch name: '{b.raw}'" }
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
  if !isValidPathArg source || !isValidPathArg target || source.toList.head? == some '-' then
    return .error { kind := .invalidInput, message := "invalid clone source or target" }
  match opts.depth? with
  | some 0 => return .error { kind := .invalidInput, message := "clone depth must be positive" }
  | _ => pure ()
  let branchArgs : Except GitError (Array String) :=
    match opts.branch? with
    | none => .ok #[]
    | some b =>
      if isValidRefNameStr b then
        .ok #["--branch", b]
      else
        .error { kind := .invalidRef, message := s!"invalid clone branch: '{b}'" }
  match branchArgs with
  | .error e => return .error e
  | .ok bArgs =>
    let depthArgs :=
      match opts.depth? with
      | none => #[]
      | some d => #["--depth", toString d]
    let args :=
      #["clone"] ++
      (if opts.bare then #["--bare"] else #[]) ++
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
    if !paths.all isValidPathArg then
      return .error { kind := .invalidPath, message := "invalid path passed to git add" }
    let args :=
      if all then
        if paths.isEmpty then #["add", "--all"] else #["add", "--all", "--"] ++ paths
      else
        #["add", "--"] ++ paths
    match ← runGitChecked ops "add" { cwd := some repoPath, args := args } with
    | .error e => return .error e
    | .ok _ => return .ok ()

/-- Create a commit with validated message and optional author/committer environment overrides. -/
def commitImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath : String) (opts : CommitOptions) : m (Except GitError CommitId) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    if opts.message.isEmpty || hasNulChar opts.message.toList then
      return .error { kind := .invalidInput, message := "commit message must be non-empty without NUL bytes" }
    let nameEnv : Except GitError (Array (String × Option String)) :=
      match opts.authorName with
      | none => .ok #[]
      | some n =>
        if isValidEnvVal? (some n) then
          .ok #[("GIT_AUTHOR_NAME", some n), ("GIT_COMMITTER_NAME", some n)]
        else
          .error { kind := .invalidInput, message := "invalid author name" }
    match nameEnv with
    | .error e => return .error e
    | .ok nEnv =>
      let emailEnv : Except GitError (Array (String × Option String)) :=
        match opts.authorEmail with
        | none => .ok #[]
        | some em =>
          if isValidEnvVal? (some em) then
            .ok #[("GIT_AUTHOR_EMAIL", some em), ("GIT_COMMITTER_EMAIL", some em)]
          else
            .error { kind := .invalidInput, message := "invalid author email" }
      match emailEnv with
      | .error e => return .error e
      | .ok eEnv =>
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
    if !isValidRefNameStr branch.raw then
      return .error { kind := .invalidRef, message := s!"invalid branch name: '{branch.raw}'" }
    let spArgs : Except GitError (Array String) :=
      match startPoint? with
      | none => .ok #[]
      | some sp =>
        if isValidStrictRevSpec sp then
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
    if !isValidRefNameStr branch.raw then
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
        if isValidRefNameStr b.raw then
          .ok #[b.raw, "--"]
        else
          .error { kind := .invalidRef, message := s!"invalid branch name: '{b.raw}'" }
      | .commit cid =>
        if isValidCommitIdStr cid.hex then
          .ok #["--detach", cid.hex, "--"]
        else
          .error { kind := .invalidRef, message := s!"invalid commit ID: '{cid.hex}'" }
      | .ref spec =>
        if isValidStrictRevSpec spec then
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
    if !isValidRefNameStr branch.raw then
      return .error { kind := .invalidRef, message := s!"invalid branch name: '{branch.raw}'" }
    if !create && startPoint?.isSome then
      return .error { kind := .invalidInput, message := "switch startPoint requires create = true" }
    let spArgs : Except GitError (Array String) :=
      match startPoint? with
      | none => .ok #[]
      | some sp =>
        if isValidStrictRevSpec sp then
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
    if !isValidStrictRevSpec rev then
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
    if !isValidRemoteOrRefspec remote then
      return .error { kind := .invalidInput, message := s!"invalid remote name: '{remote}'" }
    let refArgs : Except GitError (Array String) :=
      match refspec? with
      | none => .ok #[]
      | some r =>
        if isValidRemoteOrRefspec r then
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
    if !isValidPathArg opts.path then
      return .error { kind := .invalidPath, message := "invalid worktree path" }
    if opts.detach && opts.newBranch?.isSome then
      return .error { kind := .invalidInput, message := "worktreeAdd cannot combine detach and newBranch" }
    let branchArgs : Except GitError (Array String) :=
      match opts.newBranch? with
      | none => .ok #[]
      | some b =>
        if isValidRefNameStr b.raw then
          .ok #["-b", b.raw]
        else
          .error { kind := .invalidRef, message := s!"invalid branch name: '{b.raw}'" }
    match branchArgs with
    | .error e => return .error e
    | .ok bArgs =>
      let targetArgs : Except GitError (Array String) :=
        match opts.target? with
        | none => .ok #[]
        | some t =>
          if isValidStrictRevSpec t then
            .ok #[t]
          else
            .error { kind := .invalidInput, message := s!"invalid worktree target: '{t}'" }
      match targetArgs with
      | .error e => return .error e
      | .ok tArgs =>
        let args :=
          #["worktree", "add"] ++
          (if opts.force then #["--force"] else #[]) ++
          (if opts.detach then #["--detach"] else #[]) ++
          bArgs ++ #["--", opts.path] ++ tArgs
        match ← runGitChecked ops "worktree" { cwd := some repoPath, args := args } with
        | .error e => return .error e
        | .ok _ => return .ok ()

/-- Remove a linked worktree via `git worktree remove`. -/
def worktreeRemoveImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath wtPath : String) (force : Bool) : m (Except GitError Unit) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    if !isValidPathArg wtPath then
      return .error { kind := .invalidPath, message := "invalid worktree path" }
    let args :=
      #["worktree", "remove"] ++
      (if force then #["--force"] else #[]) ++
      #["--", wtPath]
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

end LeanSwe.Git.Impl
