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

private def decodeUtf8LossyLoop : Nat → ByteArray → Nat → List Char → List Char
  | 0, _, _, acc => acc.reverse
  | fuel + 1, bs, i, acc =>
    if i >= bs.size then acc.reverse
    else
      let b0 := bs[i]!.toNat
      let isCont (k : Nat) : Bool :=
        if h : k < bs.size then
          let b := bs[k].toNat
          0x80 ≤ b && b ≤ 0xBF
        else false
      if b0 < 0x80 then
        decodeUtf8LossyLoop fuel bs (i + 1) (Char.ofNat b0 :: acc)
      else if 0xC2 ≤ b0 && b0 ≤ 0xDF && isCont (i + 1) then
        let cp := ((b0 &&& 0x1F) <<< 6) ||| (bs[i + 1]!.toNat &&& 0x3F)
        decodeUtf8LossyLoop fuel bs (i + 2) (Char.ofNat cp :: acc)
      else if 0xE0 ≤ b0 && b0 ≤ 0xEF && isCont (i + 1) && isCont (i + 2) then
        let b1 := bs[i + 1]!.toNat
        let ok := (b0 != 0xE0 || b1 ≥ 0xA0) && (b0 != 0xED || b1 ≤ 0x9F)
        if ok then
          let cp := ((b0 &&& 0x0F) <<< 12) ||| ((b1 &&& 0x3F) <<< 6) ||| (bs[i + 2]!.toNat &&& 0x3F)
          decodeUtf8LossyLoop fuel bs (i + 3) (Char.ofNat cp :: acc)
        else decodeUtf8LossyLoop fuel bs (i + 1) ('\uFFFD' :: acc)
      else if 0xF0 ≤ b0 && b0 ≤ 0xF4 && isCont (i + 1) && isCont (i + 2) && isCont (i + 3) then
        let b1 := bs[i + 1]!.toNat
        let ok := (b0 != 0xF0 || b1 ≥ 0x90) && (b0 != 0xF4 || b1 ≤ 0x8F)
        if ok then
          let cp := ((b0 &&& 0x07) <<< 18) ||| ((b1 &&& 0x3F) <<< 12) |||
            ((bs[i + 2]!.toNat &&& 0x3F) <<< 6) ||| (bs[i + 3]!.toNat &&& 0x3F)
          decodeUtf8LossyLoop fuel bs (i + 4) (Char.ofNat cp :: acc)
        else decodeUtf8LossyLoop fuel bs (i + 1) ('\uFFFD' :: acc)
      else
        decodeUtf8LossyLoop fuel bs (i + 1) ('\uFFFD' :: acc)

/-- Decode `ByteArray` as UTF-8, replacing each byte outside a valid UTF-8 sequence with the Unicode replacement character `U+FFFD` (`'\uFFFD'`). -/
def decodeUtf8Lossy (bytes : ByteArray) : String :=
  match String.fromUTF8? bytes with
  | some s => s
  | none => String.ofList (decodeUtf8LossyLoop bytes.size bytes 0 [])

/-- Decode `ByteArray` as UTF-8, failing with `.parseError` if invalid. -/
def decodeUtf8Checked (bytes : ByteArray) : Except GitError String :=
  match String.fromUTF8? bytes with
  | some s => .ok s
  | none => .error { kind := .parseError, message := "invalid UTF-8 in git output" }

/-- Strip trailing ASCII CR and LF characters from `s`. -/
def trimTrailingNewlines (s : String) : String :=
  let rev := s.toList.reverse.dropWhile (fun c => c == '\n' || c == '\r')
  String.ofList rev.reverse

/-- Strip a single trailing ASCII LF (`'\n'`) character from `s`, preserving trailing `'\r'`. -/
def stripSingleTrailingLf (s : String) : String :=
  if s.endsWith "\n" then
    let bs := s.toUTF8
    (String.fromUTF8? (bs.extract 0 (bs.size - 1))).getD s
  else s

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

private def isAsciiAlnumChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9')

private def maskQuotedLineAux (prevAlnum inSingle inDouble esc : Bool)
    (acc : List Char) : List Char → List Char
  | [] => acc.reverse
  | c :: rest =>
    if inDouble then
      if esc then maskQuotedLineAux false false true false acc rest
      else if c == '\\' then maskQuotedLineAux false false true true acc rest
      else if c == '"' then maskQuotedLineAux false false false false ('"' :: acc) rest
      else maskQuotedLineAux false false true false acc rest
    else if inSingle then
      let isApos := prevAlnum && (rest.head?.any isAsciiAlnumChar)
      if c == '\'' && !isApos then
        maskQuotedLineAux false false false false ('\'' :: acc) rest
      else
        maskQuotedLineAux (isAsciiAlnumChar c) true false false acc rest
    else if c == '"' then
      maskQuotedLineAux false false true false ('"' :: acc) rest
    else if c == '\'' && !(prevAlnum && rest.head?.any isAsciiAlnumChar) then
      maskQuotedLineAux false true false false ('\'' :: acc) rest
    else
      maskQuotedLineAux (isAsciiAlnumChar c) false false false (c :: acc) rest

private def isDiagPrefixLower (cs : List Char) : Bool :=
  startsWithChars "fatal:".toList cs || startsWithChars "error:".toList cs ||
  startsWithChars "warning:".toList cs || startsWithChars "hint:".toList cs

private def filterDiagLinesAux (skipIgnored : Bool) (acc : List String) : List String → List String
  | [] => acc.reverse
  | ln :: rest =>
    let low := ln.toList.map asciiLowerChar
    let dropTab := low.head? == some '\t'
    let trimmedLow := low.dropWhile (· == ' ')
    let isHint := startsWithChars "hint:".toList trimmedLow
    let startsIgn := startsWithChars "the following paths are ignored".toList trimmedLow
    if startsIgn then
      filterDiagLinesAux true (String.ofList low :: acc) rest
    else if skipIgnored then
      if isHint then filterDiagLinesAux false acc rest
      else if isDiagPrefixLower low then
        filterDiagLinesAux false (String.ofList (maskQuotedLineAux false false false false [] low) :: acc) rest
      else filterDiagLinesAux true acc rest
    else if dropTab || isHint then
      filterDiagLinesAux false acc rest
    else
      let masked := String.ofList (maskQuotedLineAux false false false false [] low)
      filterDiagLinesAux false (masked :: acc) rest

/-- Normalize `git` diagnostic output to lowercase, masking quoted inline arguments and dropping `hint:` and tab-indented path lines. -/
def sanitizeLowerForClassify (s : String) : List Char :=
  let kept := filterDiagLinesAux false [] (s.splitOn "\n")
  ("\n".intercalate kept).toList

private def hasLowerSubstr (needle : String) (hayLower : List Char) : Bool :=
  hasSubstrChars needle.toList hayLower

private def hasFatalOrErrorChars (lower : List Char) : Bool :=
  hasLowerSubstr "fatal:" lower || hasLowerSubstr "error:" lower

/-- Classify a non-zero `git` subprocess result into a structured `GitError`.

Lossily decodes `out.stderr` and `out.stdout` via `decodeUtf8Lossy`, selects `stderr` as the
primary diagnostic source when non-blank (after `trimAsciiWhitespace`) or falls back to `stdout`
when `stderr` is blank, and normalizes it with `sanitizeLowerForClassify`.

Error kinds are matched in precedence order:
1. `.notARepo`: repository, work-tree, or bare-repository errors in the primary diagnostic source.
2. `.nothingToCommit`: `"nothing to commit"`, `"no changes added to commit"`, or
   `"nothing added to commit"` in the primary diagnostic source, or, even when `stderr` is
   non-blank, in sanitized `stdout` when `cmd == "commit"` and sanitized `stderr` contains neither
   `"fatal:"` nor `"error:"` (`commitNothingOut`).
3. `.branchInUse`: branch already checked out or used by a worktree.
4. `.dirtyWorktree`: uncommitted/local changes or untracked files that would be overwritten, lost,
   or removed.
5. `.conflict`: unresolved/merge conflicts or unmerged index files/paths.
6. `.alreadyExists`: target already exists or is already registered.
7. `.invalidRef`: invalid, unknown, ambiguous, or unborn revision/object/branch diagnostics, or
   `pathspec` + `did not match` when `cmd == "checkout"`.
8. `.notFound`: `pathspec` + `did not match` (for commands other than `checkout`), missing
   file/worktree/remote ref diagnostics, or `branch` + `not found`.
9. `.commandFailed`: fallback when none of the above match.

Populates `stderr` with `some` decoded `out.stderr` whenever non-empty (else `none`), and sets
`message` to trimmed `stderr` if non-blank, else trimmed `stdout` if non-blank, else
`s!"git {cmd} failed with exit code {out.exitCode}"`. -/
def classifyError (cmd : String) (out : GitRawOutput) : GitError :=
  let errText := decodeUtf8Lossy out.stderr
  let outText := decodeUtf8Lossy out.stdout
  let errBlank := (trimAsciiWhitespace errText).isEmpty
  let diagSource := if errBlank then outText else errText
  let combinedLower := sanitizeLowerForClassify diagSource
  let hasAny (ps : List String) (cs : List Char) : Bool := ps.any (hasLowerSubstr · cs)
  let commitNothingOut :=
    !errBlank && cmd == "commit" && !hasFatalOrErrorChars combinedLower &&
      hasAny ["nothing to commit", "no changes added to commit", "nothing added to commit"]
        (sanitizeLowerForClassify outText)
  let kind :=
    if hasAny ["not a git repository", "must be run in a work tree", "not allowed in a bare repository"] combinedLower then
      .notARepo
    else if commitNothingOut ||
        hasAny ["nothing to commit", "no changes added to commit", "nothing added to commit"] combinedLower then
      .nothingToCommit
    else if hasAny ["is already used by worktree", "is already checked out", "used by worktree"] combinedLower then
      .branchInUse
    else if hasAny ["would be overwritten by", "would lose untracked files", "would be removed by",
        "local changes", "uncommitted changes", "contains modified or untracked files"] combinedLower then
      .dirtyWorktree
    else if hasAny ["unresolved conflict", "merge conflict", "conflict (", "fix conflicts",
        "unmerged files", "unmerged path", "is unmerged", "needs merge",
        "resolve your current index first"] combinedLower then
      .conflict
    else if hasAny ["already exists", "already registered"] combinedLower then
      .alreadyExists
    else if hasAny ["unknown revision", "ambiguous argument", "ambiguous object name",
        "matched multiple", "a branch is expected", "expected commit type",
        "not a valid object name", "not a valid commit name", "needed a single revision",
        "not a valid branch point", "could not parse object", "bad revision", "bad object",
        "failed to resolve", "invalid reference", "unable to read tree",
        "reference is not a tree", "does not have any commits yet", "not a valid branch name"] combinedLower ||
        (cmd == "checkout" && hasLowerSubstr "pathspec" combinedLower && hasLowerSubstr "did not match" combinedLower) then
      .invalidRef
    else if (hasLowerSubstr "pathspec" combinedLower && hasLowerSubstr "did not match" combinedLower) ||
        hasAny ["does not exist", "not a valid worktree", "is not a working tree",
          "couldn't find remote ref", "no such file or directory"] combinedLower ||
        (hasLowerSubstr "branch" combinedLower && hasLowerSubstr "not found" combinedLower) then
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

/-- Validate a repository directory path argument (`invalidPath` or `invalidInput`). -/
def validateRepoPath (repoPath : String) : Except GitError Unit :=
  validateFsPathArg repoPath

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
        if isValidRefNameStr b.raw then .ok #["-b", b.raw]
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
  match validateCloneEndpoint source, validateCloneEndpoint target with
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
        if isValidRefNameStr b then .ok #["--branch", b]
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

/-- Create a commit with validated message and optional author/committer overrides. -/
def commitImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath : String) (opts : CommitOptions) : m (Except GitError CommitId) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    match validateCommitOptions opts with
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
    match validateRepoPath opts.path with
    | .error e => return .error e
    | .ok () =>
      if opts.detach && opts.newBranch?.isSome then
        return .error { kind := .invalidInput, message := "worktreeAdd cannot combine detach and newBranch" }
      let branchArgs : Except GitError (Array String) :=
        match opts.newBranch? with
        | none => .ok #[]
        | some b =>
          if isValidRefNameStr b.raw then .ok #["-b", b.raw]
          else .error { kind := .invalidRef, message := s!"invalid branch name: '{b.raw}'" }
      match branchArgs with
      | .error e => return .error e
      | .ok bArgs =>
        let targetArgs : Except GitError (Array String) :=
          match opts.target? with
          | none => .ok #[]
          | some t =>
            if isValidStrictRevSpec t then .ok #[t]
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
