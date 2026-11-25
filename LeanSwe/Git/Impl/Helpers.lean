import LeanSwe.EnvVars.Types
import LeanSwe.Process.Types
import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Model.Refines

namespace LeanSwe.Git.Impl

open LeanSwe.EnvVars
open LeanSwe.Process
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

/-- Return `true` iff lowercase diagnostic characters contain `"fatal:"` or `"error:"`. -/
def hasFatalOrErrorChars (lower : List Char) : Bool :=
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

end LeanSwe.Git.Impl
