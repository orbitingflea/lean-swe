import LeanSwe.Git.Types

namespace LeanSwe.Git.Model

open LeanSwe.Git

/-- Return `true` iff `c` is a lowercase hexadecimal digit (`0`–`9` or `a`–`f`). -/
def isLowerHexChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- Return `true` iff `s` is a valid 40-char SHA-1 or 64-char SHA-256 lowercase hex commit ID. -/
def isValidCommitIdStr (s : String) : Bool :=
  let cs := s.toList
  (cs.length == 40 || cs.length == 64) && cs.all isLowerHexChar

/-- Construct a validated `CommitId`, failing with `.invalidRef` on malformed hashes. -/
def mkCommitId (s : String) : Except GitError CommitId :=
  if isValidCommitIdStr s then
    .ok { hex := s }
  else
    .error { kind := .invalidRef, message := s!"invalid commit id: '{s}'" }

/-- Return `true` iff `c` is an ASCII control character (`< 0x20` or `0x7f`). -/
def isControlChar (c : Char) : Bool :=
  c.toNat < 0x20 || c.toNat == 0x7f

/-- Return `true` iff `c` is an ASCII whitespace character (`' '`, `'\t'`, `'\n'`, or `'\r'`). -/
def isAsciiWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Return `true` iff `cs` contains a NUL character (`Char.ofNat 0`). -/
def hasNulChar : List Char → Bool
  | [] => false
  | c :: cs => c == Char.ofNat 0 || hasNulChar cs

/-- Return `true` iff `cs` starts with the four characters `['G', 'I', 'T', '_']`. -/
def isGitPrefixChars : List Char → Bool
  | 'G' :: 'I' :: 'T' :: '_' :: _ => true
  | _ => false

/-- Return `true` iff environment variable key `k` begins with `"GIT_"`. -/
def isGitKey (k : String) : Bool :=
  isGitPrefixChars k.toList

/-- Return `true` iff `k` is an allowlisted non-repo-redirecting `GIT_*` identity/date override. -/
def isAllowedExtraGitKey (k : String) : Bool :=
  k == "GIT_AUTHOR_NAME" ||
  k == "GIT_AUTHOR_EMAIL" ||
  k == "GIT_AUTHOR_DATE" ||
  k == "GIT_COMMITTER_NAME" ||
  k == "GIT_COMMITTER_EMAIL" ||
  k == "GIT_COMMITTER_DATE"

/-- Return `true` iff `cs` contains `'='` or NUL, which are illegal in POSIX env keys. -/
def hasInvalidEnvKeyChar : List Char → Bool
  | [] => false
  | c :: cs => c == '=' || c == Char.ofNat 0 || hasInvalidEnvKeyChar cs

/-- Return `true` iff `k` is a valid non-empty POSIX environment key. -/
def isValidEnvKey (k : String) : Bool :=
  !k.toList.isEmpty && !hasInvalidEnvKeyChar k.toList

/-- Return `true` iff optional environment value `v?` contains no NUL bytes. -/
def isValidEnvVal? : Option String → Bool
  | none => true
  | some v => !hasNulChar v.toList

/-- Non-interactive safety environment defaults injected into every `git` subprocess. -/
def defaultGitSafetyEnv : List (String × Option String) :=
  [ ("GIT_TERMINAL_PROMPT", some "0")
  , ("GIT_CONFIG_COUNT", some "1")
  , ("GIT_CONFIG_KEY_0", some "safe.bareRepository")
  , ("GIT_CONFIG_VALUE_0", some "all")
  ]

/-- Strip all inherited `GIT_*` keys, inject non-interactive defaults, and filter `extraEnv`. -/
def cleanGitEnv (inheritedEnv : Array (String × String))
    (extraEnv : Array (String × Option String) := #[]) : Array (String × Option String) :=
  let stripped :=
    (inheritedEnv.toList.filter fun kv => isGitKey kv.1).map fun kv => (kv.1, none)
  let filteredExtra :=
    extraEnv.toList.filter fun kv =>
      isValidEnvKey kv.1 && isValidEnvVal? kv.2 && (!isGitKey kv.1 || isAllowedExtraGitKey kv.1)
  (stripped ++ defaultGitSafetyEnv ++ filteredExtra).toArray

/-- Return `true` iff character `c` is forbidden in Git reference names. -/
def isInvalidRefChar (c : Char) : Bool :=
  isControlChar c ||
  c == ' ' || c == '~' || c == '^' || c == ':' ||
  c == '?' || c == '*' || c == '[' || c == '\\'

/-- Return `true` iff `cs` begins with `pref`. -/
def startsWithChars : List Char → List Char → Bool
  | [], _ => true
  | _, [] => false
  | p :: ps, c :: cs => p == c && startsWithChars ps cs

/-- Return `true` iff `needle` occurs as a contiguous sublist of `haystack`. -/
def hasSubstrChars (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | c :: cs => startsWithChars needle (c :: cs) || hasSubstrChars needle cs

/-- Return `true` iff `cs` ends with suffix `suf`. -/
def endsWithChars (suf cs : List Char) : Bool :=
  startsWithChars suf.reverse cs.reverse

/-- Split a `List Char` on `'/'` separators, keeping empty segments. -/
def splitSlashAux (acc : List Char) : List Char → List (List Char)
  | [] => [acc.reverse]
  | c :: cs =>
    if c == '/' then acc.reverse :: splitSlashAux [] cs
    else splitSlashAux (c :: acc) cs

/-- Split `cs` on `'/'` separators. -/
def splitSlashChars (cs : List Char) : List (List Char) :=
  splitSlashAux [] cs

/-- Validate a single slash-delimited Git ref component. -/
def isValidRefComponent (comp : List Char) : Bool :=
  !comp.isEmpty &&
  comp.head? != some '.' &&
  !endsWithChars ['.'] comp &&
  !endsWithChars ['.', 'l', 'o', 'c', 'k'] comp

/-- Return `true` iff `s` satisfies `git check-ref-format` safety rules and does not start with `'-'`. -/
def isValidRefNameStr (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty &&
  cs.head? != some '-' &&
  cs.head? != some '/' &&
  !endsWithChars ['/'] cs &&
  cs != ['@'] &&
  !cs.any isInvalidRefChar &&
  !hasSubstrChars ['.', '.'] cs &&
  !hasSubstrChars ['@', '{'] cs &&
  !hasSubstrChars ['/', '/'] cs &&
  (splitSlashChars cs).all isValidRefComponent

/-- Construct a validated `RefName`, failing with `.invalidRef` if unsafe or malformed. -/
def mkRefName (s : String) : Except GitError RefName :=
  if isValidRefNameStr s then
    .ok { raw := s }
  else
    .error { kind := .invalidRef, message := s!"invalid git reference name: '{s}'" }

/-- Return `true` iff `s` is a non-empty revision spec without leading `'-'` or control characters. -/
def isValidRevSpec (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty && cs.head? != some '-' && !cs.any isControlChar

/-- Return `true` iff `s` is a single-commit revision spec without whitespace, `':'`, or `".."`. -/
def isValidStrictRevSpec (s : String) : Bool :=
  let cs := s.toList
  isValidRevSpec s &&
  !cs.any isAsciiWhitespace &&
  !cs.contains ':' &&
  !hasSubstrChars ['.', '.'] cs

/-- Return `true` iff `s` is a non-empty path argument without NUL bytes. -/
def isValidPathArg (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty && !hasNulChar cs

/-- Return `true` iff `s` is a valid non-empty relative repository path without leading `'/'` or `".."` segments. -/
def isValidRelRepoPath (s : String) : Bool :=
  let cs := s.toList
  isValidPathArg s &&
  cs.head? != some '/' &&
  !(splitSlashChars cs).contains ['.', '.']

/-- Return `true` iff `s` is a safe non-empty remote or refspec token without leading `'-'`, control chars, or whitespace. -/
def isValidRemoteOrRefspec (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty &&
  cs.head? != some '-' &&
  !cs.any isControlChar &&
  !cs.any isAsciiWhitespace

/-- Split NUL-terminated non-empty records, rejecting unterminated non-empty input or empty records. -/
def splitNulRecordsAux (acc : List Char) : List Char → Option (List String)
  | [] => if acc.isEmpty then some [] else none
  | c :: cs =>
    if c == Char.ofNat 0 then
      if acc.isEmpty then none
      else (splitNulRecordsAux [] cs).map (String.ofList acc.reverse :: ·)
    else
      splitNulRecordsAux (c :: acc) cs

/-- Split a NUL-terminated stream into non-empty records (`[]` returns `some []`). -/
def splitNulRecords (s : String) : Option (List String) :=
  splitNulRecordsAux [] s.toList

/-- Map a single `git status --porcelain=v1` status character to `Option StatusKind`. -/
def statusCharToKind? : Char → Option (Option StatusKind)
  | ' ' => some none
  | 'M' => some (some .modified)
  | 'A' => some (some .added)
  | 'D' => some (some .deleted)
  | 'R' => some (some .renamed)
  | 'C' => some (some .copied)
  | 'T' => some (some .typeChanged)
  | 'U' => some (some .unmerged)
  | '?' => some (some .untracked)
  | '!' => some (some .ignored)
  | _ => none

/-- Return `true` iff `(x, y)` is a valid pair of `git status --porcelain=v1` status characters. -/
def isValidStatusPair (x y : Char) : Bool :=
  (statusCharToKind? x).isSome &&
  (statusCharToKind? y).isSome &&
  (x == '?' ↔ y == '?') &&
  (x == '!' ↔ y == '!') &&
  !(x == ' ' && y == ' ')

/-- Parse NUL-separated `git status --porcelain=v1 -z` records (`XY PATH1` followed by `PATH2` for `R`/`C`). -/
def parsePorcelainStatusRecords : List String → Except GitError (List StatusEntry)
  | [] => .ok []
  | recStr :: rest =>
    match recStr.toList with
    | x :: y :: ' ' :: pathChars =>
      if pathChars.isEmpty || !isValidStatusPair x y then
        .error { kind := .parseError, message := s!"invalid porcelain status entry: '{recStr}'" }
      else
        match statusCharToKind? x, statusCharToKind? y with
        | some ix, some wt =>
          let path := String.ofList pathChars
          if x == 'R' || x == 'C' || y == 'R' || y == 'C' then
            match rest with
            | [] =>
              .error { kind := .parseError, message := s!"truncated rename/copy status entry for '{path}'" }
            | orig :: tail =>
              (parsePorcelainStatusRecords tail).map
                ({ indexStatus := ix, worktreeStatus := wt, path := path, origPath := some orig } :: ·)
          else
            (parsePorcelainStatusRecords rest).map
              ({ indexStatus := ix, worktreeStatus := wt, path := path, origPath := none } :: ·)
        | _, _ =>
          .error { kind := .parseError, message := s!"invalid status characters in '{recStr}'" }
    | _ =>
      .error { kind := .parseError, message := s!"malformed porcelain status record: '{recStr}'" }

/-- Parse raw `git status --porcelain=v1 -z` output bytes into `StatusEntry` values. -/
def parsePorcelainStatusZ (bytes : ByteArray) : Except GitError (Array StatusEntry) := do
  if bytes.isEmpty then
    return #[]
  match String.fromUTF8? bytes with
  | none => .error { kind := .parseError, message := "git status output is not valid UTF-8" }
  | some text =>
    match splitNulRecords text with
    | none => .error { kind := .parseError, message := "unterminated or empty record in git status -z output" }
    | some recs =>
      let entries ← parsePorcelainStatusRecords recs
      return entries.toArray

/-- Parse a decimal digit sequence into `Nat`, returning `none` on empty or non-digit input. -/
def parseNatDigitsAux (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: cs =>
    if '0' ≤ c && c ≤ '9' then
      parseNatDigitsAux (acc * 10 + (c.toNat - '0'.toNat)) cs
    else
      none

/-- Parse optional similarity score digits (empty defaults to `100`). -/
def parseSimilarityScore (cs : List Char) : Option Nat :=
  if cs.isEmpty then some 100 else parseNatDigitsAux 0 cs

/-- Parse NUL-separated `git diff --name-status -z` tokens (`origPath` before `path` for `R`/`C`). -/
def parseDiffTokens : List String → Except GitError (List DiffEntry)
  | [] => .ok []
  | tok :: rest =>
    match tok.toList with
    | ['A'] =>
      match rest with
      | path :: tail => (parseDiffTokens tail).map ({ kind := .added, path := path } :: ·)
      | [] => .error { kind := .parseError, message := "truncated A entry in git diff -z" }
    | ['M'] =>
      match rest with
      | path :: tail => (parseDiffTokens tail).map ({ kind := .modified, path := path } :: ·)
      | [] => .error { kind := .parseError, message := "truncated M entry in git diff -z" }
    | ['D'] =>
      match rest with
      | path :: tail => (parseDiffTokens tail).map ({ kind := .deleted, path := path } :: ·)
      | [] => .error { kind := .parseError, message := "truncated D entry in git diff -z" }
    | ['T'] =>
      match rest with
      | path :: tail => (parseDiffTokens tail).map ({ kind := .typeChanged, path := path } :: ·)
      | [] => .error { kind := .parseError, message := "truncated T entry in git diff -z" }
    | ['U'] =>
      match rest with
      | path :: tail => (parseDiffTokens tail).map ({ kind := .unmerged, path := path } :: ·)
      | [] => .error { kind := .parseError, message := "truncated U entry in git diff -z" }
    | 'R' :: scoreChars =>
      match parseSimilarityScore scoreChars, rest with
      | some score, orig :: path :: tail =>
        (parseDiffTokens tail).map
          ({ kind := .renamed score, path := path, origPath := some orig } :: ·)
      | none, _ =>
        .error { kind := .parseError, message := s!"invalid rename score in '{tok}'" }
      | _, _ =>
        .error { kind := .parseError, message := s!"truncated rename entry '{tok}' in git diff -z" }
    | 'C' :: scoreChars =>
      match parseSimilarityScore scoreChars, rest with
      | some score, orig :: path :: tail =>
        (parseDiffTokens tail).map
          ({ kind := .copied score, path := path, origPath := some orig } :: ·)
      | none, _ =>
        .error { kind := .parseError, message := s!"invalid copy score in '{tok}'" }
      | _, _ =>
        .error { kind := .parseError, message := s!"truncated copy entry '{tok}' in git diff -z" }
    | _ =>
      .error { kind := .parseError, message := s!"unknown git diff status token: '{tok}'" }

/-- Parse raw `git diff --name-status -z` output bytes into `DiffEntry` values. -/
def parseDiffNameStatusZ (bytes : ByteArray) : Except GitError (Array DiffEntry) := do
  if bytes.isEmpty then
    return #[]
  match String.fromUTF8? bytes with
  | none => .error { kind := .parseError, message := "git diff output is not valid UTF-8" }
  | some text =>
    match splitNulRecords text with
    | none => .error { kind := .parseError, message := "unterminated or empty record in git diff -z output" }
    | some toks =>
      let entries ← parseDiffTokens toks
      return entries.toArray

/-- Split NUL-terminated tokens allowing empty `""` stanza-delimiter tokens. -/
def splitNulTokensAllowEmptyAux (acc : List Char) : List Char → Option (List String)
  | [] => if acc.isEmpty then some [] else none
  | c :: cs =>
    if c == Char.ofNat 0 then
      (splitNulTokensAllowEmptyAux [] cs).map (String.ofList acc.reverse :: ·)
    else
      splitNulTokensAllowEmptyAux (c :: acc) cs

/-- Group NUL-terminated tokens into non-empty worktree stanzas terminated by `""`. -/
def splitWorktreeStanzas (cur : List String) : List String → Option (List (List String))
  | [] => if cur.isEmpty then some [] else none
  | "" :: rest =>
    if cur.isEmpty then none
    else (splitWorktreeStanzas [] rest).map (cur.reverse :: ·)
  | tok :: rest => splitWorktreeStanzas (tok :: cur) rest

/-- Return `true` iff `s` is an all-zero unborn `HEAD` hash (40 or 64 `'0'` digits). -/
def isAllZerosCommitStr (s : String) : Bool :=
  let cs := s.toList
  (cs.length == 40 || cs.length == 64) && cs.all (· == '0')

/-- Strip a prefix `pref` from `cs`, returning `some suffix` if matched. -/
def stripPrefixChars : List Char → List Char → Option (List Char)
  | [], rest => some rest
  | _ :: _, [] => none
  | p :: ps, c :: cs => if p == c then stripPrefixChars ps cs else none

/-- Parse attribute lines within a single `git worktree list --porcelain -z` stanza. -/
def parseWorktreeAttrs (info : WorktreeInfo) (headSeen : Bool) :
    List String → Except GitError (WorktreeInfo × Bool)
  | [] => .ok (info, headSeen)
  | line :: rest =>
    let cs := line.toList
    if line == "bare" then
      parseWorktreeAttrs { info with isBare := true } headSeen rest
    else if line == "detached" then
      parseWorktreeAttrs { info with isDetached := true } headSeen rest
    else if line == "locked" then
      parseWorktreeAttrs { info with isLocked := true, lockReason := none } headSeen rest
    else if line == "prunable" then
      parseWorktreeAttrs { info with isPrunable := true, pruneReason := none } headSeen rest
    else
      match stripPrefixChars ['H', 'E', 'A', 'D', ' '] cs with
      | some shaChars =>
        let sha := String.ofList shaChars
        if isAllZerosCommitStr sha then
          parseWorktreeAttrs { info with head? := none } true rest
        else
          match mkCommitId sha with
          | .ok cid => parseWorktreeAttrs { info with head? := some cid } true rest
          | .error _ =>
            .error { kind := .parseError, message := s!"invalid HEAD hash in worktree list: '{sha}'" }
      | none =>
        match stripPrefixChars ['b', 'r', 'a', 'n', 'c', 'h', ' '] cs with
        | some refChars =>
          match stripPrefixChars ['r', 'e', 'f', 's', '/', 'h', 'e', 'a', 'd', 's', '/'] refChars with
          | some shortChars =>
            match mkRefName (String.ofList shortChars) with
            | .ok ref => parseWorktreeAttrs { info with branch? := some ref } headSeen rest
            | .error _ =>
              .error { kind := .parseError, message := s!"invalid branch ref in worktree list: '{String.ofList refChars}'" }
          | none =>
            .error { kind := .parseError, message := s!"worktree branch does not start with refs/heads/: '{String.ofList refChars}'" }
        | none =>
          match stripPrefixChars ['l', 'o', 'c', 'k', 'e', 'd', ' '] cs with
          | some reasonChars =>
            parseWorktreeAttrs { info with isLocked := true, lockReason := some (String.ofList reasonChars) } headSeen rest
          | none =>
            match stripPrefixChars ['p', 'r', 'u', 'n', 'a', 'b', 'l', 'e', ' '] cs with
            | some reasonChars =>
              parseWorktreeAttrs { info with isPrunable := true, pruneReason := some (String.ofList reasonChars) } headSeen rest
            | none =>
              parseWorktreeAttrs info headSeen rest

/-- Parse a single non-empty worktree stanza into a `WorktreeInfo`. -/
def parseWorktreeStanza : List String → Except GitError WorktreeInfo
  | [] => .error { kind := .parseError, message := "empty worktree stanza" }
  | header :: attrs =>
    match stripPrefixChars ['w', 'o', 'r', 'k', 't', 'r', 'e', 'e', ' '] header.toList with
    | none => .error { kind := .parseError, message := s!"worktree stanza missing 'worktree ' header: '{header}'" }
    | some pathChars =>
      if pathChars.isEmpty then
        .error { kind := .parseError, message := "empty worktree path in porcelain output" }
      else do
        let base : WorktreeInfo := { path := String.ofList pathChars, head? := none, branch? := none }
        let (info, headSeen) ← parseWorktreeAttrs base false attrs
        if !info.isBare && !headSeen then
          .error { kind := .parseError, message := s!"non-bare worktree '{info.path}' missing HEAD attribute" }
        else
          .ok info

/-- Parse all stanzas in a `git worktree list --porcelain -z` response. -/
def parseWorktreeStanzas : List (List String) → Except GitError (List WorktreeInfo)
  | [] => .ok []
  | st :: rest => do
    let info ← parseWorktreeStanza st
    let tail ← parseWorktreeStanzas rest
    .ok (info :: tail)

/-- Parse raw `git worktree list --porcelain -z` output bytes into `WorktreeInfo` values. -/
def parseWorktreeListPorcelain (bytes : ByteArray) : Except GitError (Array WorktreeInfo) := do
  if bytes.isEmpty then
    return #[]
  match String.fromUTF8? bytes with
  | none => .error { kind := .parseError, message := "git worktree output is not valid UTF-8" }
  | some text =>
    match splitNulTokensAllowEmptyAux [] text.toList with
    | none => .error { kind := .parseError, message := "unterminated NUL stream in git worktree output" }
    | some toks =>
      match splitWorktreeStanzas [] toks with
      | none => .error { kind := .parseError, message := "malformed stanza framing in git worktree output" }
      | some stanzas =>
        let infos ← parseWorktreeStanzas stanzas
        return infos.toArray

/-- Node in the logical commit DAG of `RepoState`. -/
structure CommitNode where
  /-- Unique commit identifier. -/
  id : CommitId
  /-- Parent commit identifiers (all appearing earlier in `RepoState.commits`). -/
  parents : List CommitId
  /-- Snapshot tree mapping relative file paths to file contents. -/
  tree : List (String × String) := []
  /-- Commit message. -/
  message : String := ""
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Logical representation of a main or linked worktree in `RepoState`. -/
structure WorktreeSlot where
  /-- Absolute path of the worktree root. -/
  path : String
  /-- Checked-out branch or detached commit state. -/
  head : HeadState
  /-- Staged file additions/modifications (`some`) or deletions (`none`). -/
  staged : List (String × Option String) := []
  /-- Unstaged working-tree modifications (`some`) or deletions (`none`). -/
  unstaged : List (String × Option String) := []
  /-- Untracked working-tree file paths. -/
  untracked : List String := []
  /-- Unmerged conflicted file paths. -/
  conflicts : List String := []
  /-- Whether this slot represents a bare repository. -/
  isBare : Bool := false
  /-- Whether this worktree is locked. -/
  isLocked : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Pure in-memory model of a Git repository's commits, branches, and worktrees. -/
structure RepoState where
  /-- Root path of the main repository/worktree. -/
  rootPath : String
  /-- Topologically ordered (oldest-first) finite acyclic commit DAG. -/
  commits : List CommitNode := []
  /-- Local branch tips (`RefName` to `CommitId`). -/
  branches : List (RefName × CommitId) := []
  /-- Active worktree list; `worktrees[0]` is always the main worktree. -/
  worktrees : List WorktreeSlot := []
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Return `true` iff all elements in `xs` are pairwise distinct. -/
def allDistinct {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && allDistinct xs

/-- Check topological uniqueness and parent-precedence of `commits` given `seen` IDs. -/
def validCommitDagAux (seen : List CommitId) : List CommitNode → Bool
  | [] => true
  | c :: rest =>
    !seen.contains c.id &&
    c.parents.all (seen.contains ·) &&
    validCommitDagAux (c.id :: seen) rest

/-- Return `true` iff commit `id` exists in `s.commits`. -/
def hasCommit (s : RepoState) (id : CommitId) : Bool :=
  s.commits.any (fun c => c.id == id)

/-- Collect all branch names currently attached in `worktrees`. -/
def attachedBranches : List WorktreeSlot → List RefName
  | [] => []
  | w :: rest =>
    match w.head with
    | .attached b _ => b :: attachedBranches rest
    | .detached _ => attachedBranches rest

/-- Return `true` iff `w` is consistent with `s.commits` and `s.branches`. -/
def validWorktreeSlot (s : RepoState) (w : WorktreeSlot) : Bool :=
  let headOk :=
    match w.head with
    | .detached c => hasCommit s c
    | .attached b (some c) => hasCommit s c && s.branches.contains (b, c)
    | .attached b none => !(s.branches.map (·.1)).contains b
  let bareOk :=
    !w.isBare ||
    (w.staged.isEmpty && w.unstaged.isEmpty && w.untracked.isEmpty && w.conflicts.isEmpty)
  headOk && bareOk

/-- Computable invariant predicate defining well-formed `RepoState` values. -/
def isValidRepoState (s : RepoState) : Bool :=
  validCommitDagAux [] s.commits &&
  allDistinct (s.branches.map (·.1)) &&
  s.branches.all (fun bc => hasCommit s bc.2) &&
  !s.worktrees.isEmpty &&
  (s.worktrees.head?.map (·.path) == some s.rootPath) &&
  allDistinct (s.worktrees.map (·.path)) &&
  allDistinct (attachedBranches s.worktrees) &&
  s.worktrees.all (validWorktreeSlot s)

/-- Propositional well-formedness invariant on `RepoState`. -/
def ValidRepoState (s : RepoState) : Prop :=
  isValidRepoState s = true

/-- Return the direct parent commit IDs of `id` in `s`, or `[]` if absent. -/
def parentsOf (s : RepoState) (id : CommitId) : List CommitId :=
  match s.commits.find? (fun c => c.id == id) with
  | some c => c.parents
  | none => []

/-- Deduplicate a list of `CommitId`s while preserving order. -/
def dedupCommitIds : List CommitId → List CommitId
  | [] => []
  | x :: xs =>
    let rest := dedupCommitIds xs
    if rest.contains x then rest else x :: rest

/-- Expand one parent step from `frontier` in `s`. -/
def ancestorsStep (s : RepoState) (frontier : List CommitId) : List CommitId :=
  dedupCommitIds (frontier.flatMap (parentsOf s))

/-- Collect strict ancestors of `frontier` within `fuel` steps in `s`. -/
def ancestorsFuel (s : RepoState) : Nat → List CommitId → List CommitId
  | 0, _ => []
  | n + 1, frontier =>
    if frontier.isEmpty then []
    else
      let next := ancestorsStep s frontier
      dedupCommitIds (next ++ ancestorsFuel s n next)

/-- Return `true` iff `a` and `b` exist in `s` and `a` is an ancestor of `b` (reflexive). -/
def isAncestor (s : RepoState) (a b : CommitId) : Bool :=
  hasCommit s a && hasCommit s b && (a == b || (ancestorsFuel s s.commits.length [b]).contains a)

/-- Return all commits reachable from `root` (including `root` itself when present). -/
def reachable (s : RepoState) (root : CommitId) : List CommitId :=
  if hasCommit s root then
    dedupCommitIds (root :: ancestorsFuel s s.commits.length [root])
  else
    []

/-- Return all commits in `s` that are ancestors of both `a` and `b`. -/
def commonAncestors (s : RepoState) (a b : CommitId) : List CommitId :=
  if !hasCommit s a || !hasCommit s b then []
  else (s.commits.map (·.id)).filter (fun c => isAncestor s c a && isAncestor s c b)

/-- Return the lowest (maximal-depth) common ancestors of `a` and `b` in `s`. -/
def lowestCommonAncestors (s : RepoState) (a b : CommitId) : List CommitId :=
  let ca := commonAncestors s a b
  ca.filter (fun c => !ca.any (fun d => d != c && isAncestor s c d))

/-- Return the lexicographically smallest lowest common ancestor of `a` and `b` in `s`, if any. -/
def mergeBase? (s : RepoState) (a b : CommitId) : Option CommitId :=
  (lowestCommonAncestors s a b).foldl
    (fun best c =>
      match best with
      | none => some c
      | some b => if c.hex < b.hex then some c else some b)
    none

/-- Look up the commit ID of branch `b` in `s.branches`. -/
def findBranchCommit? (s : RepoState) (b : RefName) : Option CommitId :=
  (s.branches.find? (fun p => p.1 == b)).map (·.2)

/-- Look up the `WorktreeSlot` at `wtPath` in `s.worktrees`. -/
def findWorktree? (s : RepoState) (wtPath : String) : Option WorktreeSlot :=
  s.worktrees.find? (fun w => w.path == wtPath)

/-- Replace or update the worktree at `wtPath` in `s.worktrees`. -/
def updateWorktree (s : RepoState) (wtPath : String) (f : WorktreeSlot → WorktreeSlot) : RepoState :=
  { s with worktrees := s.worktrees.map (fun w => if w.path == wtPath then f w else w) }

/-- Insert or update `(b, c)` in `s.branches`. -/
def setBranchTip (branches : List (RefName × CommitId)) (b : RefName) (c : CommitId) :
    List (RefName × CommitId) :=
  if branches.any (fun p => p.1 == b) then
    branches.map (fun p => if p.1 == b then (b, c) else p)
  else
    branches ++ [(b, c)]

/-- Return `true` iff `w` has staged, unstaged, or conflicted changes. -/
def isWorktreeDirty (w : WorktreeSlot) : Bool :=
  !w.staged.isEmpty || !w.unstaged.isEmpty || !w.conflicts.isEmpty

/-- Return `true` iff branch `b` is attached in any worktree other than `wtPath`. -/
def isBranchInUseElsewhere (s : RepoState) (wtPath : String) (b : RefName) : Bool :=
  s.worktrees.any fun w =>
    w.path != wtPath &&
    match w.head with
    | .attached wb _ => wb == b
    | .detached _ => false

/-- Return `true` iff branch `b` is attached in any worktree of `s`. -/
def isBranchCheckedOut (s : RepoState) (b : RefName) : Bool :=
  s.worktrees.any fun w =>
    match w.head with
    | .attached wb _ => wb == b
    | .detached _ => false

/-- Return the commit ID of a worktree's `HEAD`, if not unborn. -/
def headCommitOfSlot : HeadState → Option CommitId
  | .attached _ c? => c?
  | .detached c => some c

/-- Convert a natural number to a lowercase 40-character hexadecimal `CommitId` for deterministic mocks. -/
def mkSyntheticCommitId (n : Nat) : CommitId :=
  let rec hexDigits (fuel k : Nat) (acc : List Char) : List Char :=
    match fuel with
    | 0 => acc
    | f + 1 =>
      let d := k % 16
      let ch := if d < 10 then Char.ofNat ('0'.toNat + d) else Char.ofNat ('a'.toNat + (d - 10))
      hexDigits f (k / 16) (ch :: acc)
  { hex := String.ofList (hexDigits 40 n []) }

/-- Pure transition: initialize a fresh repository at `rootPath` with an unborn initial branch. -/
def stepInit (rootPath : String) (bare : Bool) (initialBranch? : Option RefName) :
    Except GitError RepoState := do
  if !isValidPathArg rootPath then
    .error { kind := .invalidPath, message := "invalid repository path" }
  else
    let branch := initialBranch?.getD { raw := "main" }
    .ok
      { rootPath := rootPath
        commits := []
        branches := []
        worktrees := [{ path := rootPath, head := .attached branch none, isBare := bare }] }

/-- Pure transition: stage explicit paths or all unstaged/untracked changes in worktree `wtPath`. -/
def stepAdd (s : RepoState) (wtPath : String) (paths : Array String) (all : Bool) :
    Except GitError RepoState := do
  if paths.isEmpty && !all then
    .error { kind := .invalidInput, message := "nothing specified to add" }
  else if !paths.toList.all isValidPathArg then
    .error { kind := .invalidPath, message := "invalid path argument" }
  else
    match findWorktree? s wtPath with
    | none => .error { kind := .notARepo, message := s!"worktree not found: '{wtPath}'" }
    | some w =>
      if w.isBare then
        .error { kind := .notARepo, message := "cannot stage files in a bare repository" }
      else if all then
        let newStaged :=
          w.staged ++ w.unstaged ++ w.untracked.map (fun p => (p, some ""))
        let s' := updateWorktree s wtPath fun slot =>
          { slot with staged := newStaged, unstaged := [], untracked := [] }
        .ok s'
      else
        let pathList := paths.toList
        let movedUnstaged := w.unstaged.filter (fun kv => pathList.contains kv.1)
        let remUnstaged := w.unstaged.filter (fun kv => !pathList.contains kv.1)
        let movedUntracked := w.untracked.filter (fun p => pathList.contains p)
        let remUntracked := w.untracked.filter (fun p => !pathList.contains p)
        let newStaged :=
          w.staged ++ movedUnstaged ++ movedUntracked.map (fun p => (p, some ""))
        let s' := updateWorktree s wtPath fun slot =>
          { slot with staged := newStaged, unstaged := remUnstaged, untracked := remUntracked }
        .ok s'

/-- Pure transition: commit staged changes in worktree `wtPath` using commit ID `newId`. -/
def stepCommit (s : RepoState) (wtPath : String) (opts : CommitOptions) (newId : CommitId) :
    Except GitError (CommitId × RepoState) := do
  if opts.message.isEmpty || hasNulChar opts.message.toList then
    .error { kind := .invalidInput, message := "commit message must be non-empty without NUL bytes" }
  else if hasCommit s newId then
    .error { kind := .alreadyExists, message := s!"commit '{newId.hex}' already exists" }
  else
    match findWorktree? s wtPath with
    | none => .error { kind := .notARepo, message := s!"worktree not found: '{wtPath}'" }
    | some w =>
      if w.isBare then
        .error { kind := .notARepo, message := "cannot commit in a bare repository" }
      else if !w.conflicts.isEmpty then
        .error { kind := .conflict, message := "unmerged conflict files prevent commit" }
      else if w.staged.isEmpty && !opts.allowEmpty then
        .error { kind := .nothingToCommit, message := "nothing to commit" }
      else
        let parents :=
          match headCommitOfSlot w.head with
          | some p => [p]
          | none => []
        let node : CommitNode := { id := newId, parents := parents, tree := [], message := opts.message }
        let (newBranches, newHead) :=
          match w.head with
          | .attached b _ => (setBranchTip s.branches b newId, .attached b (some newId))
          | .detached _ => (s.branches, .detached newId)
        let s' :=
          { s with
            commits := s.commits ++ [node]
            branches := newBranches }
        let s'' := updateWorktree s' wtPath fun slot =>
          { slot with head := newHead, staged := [] }
        .ok (newId, s'')

/-- Pure transition: create or reset `branch` to `target`. -/
def stepCreateBranch (s : RepoState) (branch : RefName) (target : CommitId) (force : Bool) :
    Except GitError RepoState := do
  if !hasCommit s target then
    .error { kind := .invalidRef, message := s!"unknown commit '{target.hex}'" }
  else
    match findBranchCommit? s branch with
    | some _ =>
      if !force then
        .error { kind := .alreadyExists, message := s!"branch '{branch.raw}' already exists" }
      else if isBranchCheckedOut s branch then
        .error { kind := .branchInUse, message := s!"branch '{branch.raw}' is checked out in a worktree" }
      else
        .ok { s with branches := setBranchTip s.branches branch target }
    | none =>
      .ok { s with branches := setBranchTip s.branches branch target }

/-- Pure transition: delete local `branch`, rejecting `.branchInUse` or `.notFound`. -/
def stepDeleteBranch (s : RepoState) (branch : RefName) (force : Bool) :
    Except GitError RepoState := do
  match findBranchCommit? s branch with
  | none => .error { kind := .notFound, message := s!"branch '{branch.raw}' not found" }
  | some c =>
    if isBranchCheckedOut s branch then
      .error { kind := .branchInUse, message := s!"cannot delete branch '{branch.raw}' used by worktree" }
    else
      let merged :=
        match findWorktree? s s.rootPath with
        | some mainWt =>
          match headCommitOfSlot mainWt.head with
          | some hc => isAncestor s c hc
          | none => false
        | none => false
      if !force && !merged then
        .error { kind := .dirtyWorktree, message := s!"branch '{branch.raw}' is not fully merged" }
      else
        .ok { s with branches := s.branches.filter (fun p => p.1 != branch) }

/-- Pure transition: check out `target` in worktree `wtPath`. -/
def stepCheckout (s : RepoState) (wtPath : String) (target : CheckoutTarget) (force : Bool) :
    Except GitError RepoState := do
  match findWorktree? s wtPath with
  | none => .error { kind := .notARepo, message := s!"worktree not found: '{wtPath}'" }
  | some w =>
    if w.isBare then
      .error { kind := .notARepo, message := "cannot checkout in a bare repository" }
    else if !force && isWorktreeDirty w then
      .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
    else
      match target with
      | .branch b =>
        match findBranchCommit? s b with
        | none => .error { kind := .invalidRef, message := s!"invalid reference '{b.raw}'" }
        | some cid =>
          if isBranchInUseElsewhere s wtPath b then
            .error { kind := .branchInUse, message := s!"branch '{b.raw}' is already used by another worktree" }
          else
            .ok (updateWorktree s wtPath fun slot =>
              { slot with head := .attached b (some cid), staged := [], unstaged := [], conflicts := [] })
      | .commit cid =>
        if !hasCommit s cid then
          .error { kind := .invalidRef, message := s!"unknown commit '{cid.hex}'" }
        else
          .ok (updateWorktree s wtPath fun slot =>
            { slot with head := .detached cid, staged := [], unstaged := [], conflicts := [] })
      | .ref spec =>
        if !isValidRevSpec spec || spec.toList.any isAsciiWhitespace then
          .error { kind := .invalidInput, message := s!"invalid ref spec '{spec}'" }
        else
          match s.branches.find? (fun p => p.1.raw == spec) with
          | some (b, cid) =>
            if isBranchInUseElsewhere s wtPath b then
              .error { kind := .branchInUse, message := s!"branch '{b.raw}' is already used by another worktree" }
            else
              .ok (updateWorktree s wtPath fun slot =>
                { slot with head := .attached b (some cid), staged := [], unstaged := [], conflicts := [] })
          | none =>
            match s.commits.find? (fun c => c.id.hex == spec) with
            | some node =>
              .ok (updateWorktree s wtPath fun slot =>
                { slot with head := .detached node.id, staged := [], unstaged := [], conflicts := [] })
            | none =>
              .error { kind := .invalidRef, message := s!"invalid reference '{spec}'" }

/-- Pure transition: switch to or create `branch` in worktree `wtPath`. -/
def stepSwitch (s : RepoState) (wtPath : String) (branch : RefName)
    (create : Bool) (startPoint? : Option CommitId) (force : Bool) : Except GitError RepoState := do
  if !create && startPoint?.isSome then
    .error { kind := .invalidInput, message := "startPoint requires create = true" }
  else if create then
    match findWorktree? s wtPath with
    | none => .error { kind := .notARepo, message := s!"worktree not found: '{wtPath}'" }
    | some w =>
      if w.isBare then
        .error { kind := .notARepo, message := "cannot switch in a bare repository" }
      else if !force && isWorktreeDirty w then
        .error { kind := .dirtyWorktree, message := "local changes would be overwritten by switch" }
      else
        let targetCommit? := startPoint? <|> headCommitOfSlot w.head
        match targetCommit? with
        | none => .error { kind := .invalidRef, message := "cannot create branch from unborn HEAD" }
        | some cid =>
          if !hasCommit s cid then
            .error { kind := .invalidRef, message := s!"unknown start point '{cid.hex}'" }
          else if (findBranchCommit? s branch).isSome && !force then
            .error { kind := .alreadyExists, message := s!"branch '{branch.raw}' already exists" }
          else if isBranchInUseElsewhere s wtPath branch then
            .error { kind := .branchInUse, message := s!"branch '{branch.raw}' is already used by another worktree" }
          else
            let s' := { s with branches := setBranchTip s.branches branch cid }
            .ok (updateWorktree s' wtPath fun slot =>
              { slot with head := .attached branch (some cid), staged := [], unstaged := [], conflicts := [] })
  else
    stepCheckout s wtPath (.branch branch) force

/-- Pure transition: reset `HEAD`/branch in `wtPath` to `target` under `mode`. -/
def stepReset (s : RepoState) (wtPath : String) (mode : ResetMode) (target : CommitId) :
    Except GitError RepoState := do
  if !hasCommit s target then
    .error { kind := .invalidRef, message := s!"unknown commit '{target.hex}'" }
  else
    match findWorktree? s wtPath with
    | none => .error { kind := .notARepo, message := s!"worktree not found: '{wtPath}'" }
    | some w =>
      if w.isBare then
        .error { kind := .notARepo, message := "cannot reset in a bare repository" }
      else
        let (newBranches, newHead) :=
          match w.head with
          | .attached b _ => (setBranchTip s.branches b target, .attached b (some target))
          | .detached _ => (s.branches, .detached target)
        let s' := { s with branches := newBranches }
        .ok (updateWorktree s' wtPath fun slot =>
          match mode with
          | .soft => { slot with head := newHead }
          | .mixed => { slot with head := newHead, staged := [], conflicts := [] }
          | .hard => { slot with head := newHead, staged := [], unstaged := [], conflicts := [] })

/-- Resolve a string target inside `RepoState` to a commit ID (checking branches, `"HEAD"`, or hex). -/
def resolveRefStrInRepo (s : RepoState) (wtPath : String) (spec : String) : Option CommitId :=
  if spec == "HEAD" then
    match findWorktree? s wtPath with
    | some w => headCommitOfSlot w.head
    | none => none
  else
    match s.branches.find? (fun p => p.1.raw == spec) with
    | some (_, cid) => some cid
    | none => (s.commits.find? (fun c => c.id.hex == spec)).map (·.id)

/-- Pure transition: add a linked worktree to `s` under `WorktreeAddOptions`. -/
def stepWorktreeAdd (s : RepoState) (opts : WorktreeAddOptions) : Except GitError RepoState := do
  if !isValidPathArg opts.path then
    .error { kind := .invalidPath, message := "invalid worktree path" }
  else if opts.detach && opts.newBranch?.isSome then
    .error { kind := .invalidInput, message := "options newBranch? and detach cannot be used together" }
  else if !opts.detach && opts.newBranch?.isNone && opts.target?.isNone then
    .error { kind := .invalidInput, message := "worktreeAdd requires newBranch?, detach, or target?" }
  else if (findWorktree? s opts.path).isSome then
    .error { kind := .alreadyExists, message := s!"worktree already exists at '{opts.path}'" }
  else
    match opts.target? with
    | some t =>
      if !isValidRevSpec t || t.toList.any isAsciiWhitespace then
        .error { kind := .invalidInput, message := s!"invalid worktree target '{t}'" }
      else
        stepWorktreeAddValidated s opts (some t)
    | none => stepWorktreeAddValidated s opts none
where
  /-- Execute validated worktree addition after input checks succeed. -/
  stepWorktreeAddValidated (s : RepoState) (opts : WorktreeAddOptions) (targetStr? : Option String) :
      Except GitError RepoState :=
    let baseCommit? : Option CommitId :=
      match targetStr? with
      | some t => resolveRefStrInRepo s s.rootPath t
      | none =>
        match s.worktrees.head? with
        | some mainWt => headCommitOfSlot mainWt.head
        | none => none
    if opts.detach then
      match baseCommit? with
      | none => .error { kind := .invalidRef, message := "cannot resolve target commit for detached worktree" }
      | some cid =>
        let slot : WorktreeSlot := { path := opts.path, head := .detached cid }
        .ok { s with worktrees := s.worktrees ++ [slot] }
    else
      match opts.newBranch? with
      | some nb =>
        if (findBranchCommit? s nb).isSome then
          .error { kind := .alreadyExists, message := s!"branch '{nb.raw}' already exists" }
        else
          match baseCommit? with
          | none => .error { kind := .invalidRef, message := "cannot resolve start point for new worktree branch" }
          | some cid =>
            let slot : WorktreeSlot := { path := opts.path, head := .attached nb (some cid) }
            .ok { s with
                  branches := setBranchTip s.branches nb cid
                  worktrees := s.worktrees ++ [slot] }
      | none =>
        match targetStr? with
        | none => .error { kind := .invalidInput, message := "missing branch target" }
        | some refStr =>
          match s.branches.find? (fun p => p.1.raw == refStr) with
          | none => .error { kind := .invalidRef, message := s!"expected existing branch, got '{refStr}'" }
          | some (b, cid) =>
            if !opts.force && isBranchCheckedOut s b then
              .error { kind := .branchInUse, message := s!"branch '{b.raw}' is already used by worktree" }
            else if opts.force && isBranchCheckedOut s b then
              .error { kind := .branchInUse, message := s!"branch '{b.raw}' is already used by worktree" }
            else
              let slot : WorktreeSlot := { path := opts.path, head := .attached b (some cid) }
              .ok { s with worktrees := s.worktrees ++ [slot] }

/-- Pure transition: remove a linked worktree from `s`, protecting main and locked worktrees. -/
def stepWorktreeRemove (s : RepoState) (wtPath : String) (force : Bool) : Except GitError RepoState := do
  if !isValidPathArg wtPath then
    .error { kind := .invalidPath, message := "invalid worktree path" }
  else if wtPath == s.rootPath then
    .error { kind := .invalidInput, message := "cannot remove main working tree" }
  else
    match findWorktree? s wtPath with
    | none => .error { kind := .notFound, message := s!"worktree '{wtPath}' not found" }
    | some w =>
      if w.isLocked then
        .error { kind := .commandFailed, message := s!"cannot remove locked working tree '{wtPath}'" }
      else if !force && (isWorktreeDirty w || !w.untracked.isEmpty) then
        .error { kind := .dirtyWorktree, message := s!"worktree '{wtPath}' contains modified or untracked files" }
      else
        .ok { s with worktrees := s.worktrees.filter (fun slot => slot.path != wtPath) }

/-- Run a `StateM RepoState` transition and update state only on `.ok`. -/
def runRepoStep {α : Type} (f : RepoState → Except GitError (α × RepoState)) :
    StateM RepoState (Except GitError α) := fun s =>
  match f s with
  | .ok (a, s') => (.ok a, s')
  | .error e => (.error e, s)

/-- Run a `StateM RepoState` unit transition and update state only on `.ok`. -/
def runRepoStepUnit (f : RepoState → Except GitError RepoState) :
    StateM RepoState (Except GitError Unit) :=
  runRepoStep fun s => (f s).map (fun s' => ((), s'))

/-- Pure in-memory `GitApiM (StateM RepoState)` driven directly by `RepoState` transition specs. -/
def mockGitApi : GitApiM (StateM RepoState) :=
  { isRepo := fun path s =>
      (.ok ((findWorktree? s path).isSome), s)
    repoRoot := fun path s =>
      match findWorktree? s path with
      | some w => if w.isBare then (.error { kind := .notARepo, message := "bare repository" }, s) else (.ok w.path, s)
      | none => (.error { kind := .notARepo, message := "not a git repository" }, s)
    commonDir := fun path s =>
      match findWorktree? s path with
      | some _ => (.ok (s.rootPath ++ "/.git"), s)
      | none => (.error { kind := .notARepo, message := "not a git repository" }, s)
    headCommit? := fun path s =>
      match findWorktree? s path with
      | some w => (.ok (headCommitOfSlot w.head), s)
      | none => (.error { kind := .notARepo, message := "not a git repository" }, s)
    headBranch? := fun path s =>
      match findWorktree? s path with
      | some w =>
        match w.head with
        | .attached b _ => (.ok (some b), s)
        | .detached _ => (.ok none, s)
      | none => (.error { kind := .notARepo, message := "not a git repository" }, s)
    headState := fun path s =>
      match findWorktree? s path with
      | some w => (.ok w.head, s)
      | none => (.error { kind := .notARepo, message := "not a git repository" }, s)
    revParseCommit := fun path rev s =>
      if !isValidRevSpec rev then
        (.error { kind := .invalidInput, message := s!"invalid rev spec '{rev}'" }, s)
      else
        match findWorktree? s path with
        | none => (.error { kind := .notARepo, message := "not a git repository" }, s)
        | some _ =>
          match resolveRefStrInRepo s path rev with
          | some cid => (.ok cid, s)
          | none => (.error { kind := .invalidRef, message := s!"unknown revision '{rev}'" }, s)
    isAncestor := fun path a b s =>
      match findWorktree? s path with
      | none => (.error { kind := .notARepo, message := "not a git repository" }, s)
      | some _ =>
        if !hasCommit s a || !hasCommit s b then
          (.error { kind := .invalidRef, message := "unknown commit in isAncestor" }, s)
        else
          (.ok (isAncestor s a b), s)
    mergeBase? := fun path a b s =>
      match findWorktree? s path with
      | none => (.error { kind := .notARepo, message := "not a git repository" }, s)
      | some _ =>
        if !hasCommit s a || !hasCommit s b then
          (.error { kind := .invalidRef, message := "unknown commit in mergeBase?" }, s)
        else
          (.ok (mergeBase? s a b), s)
    status := fun path s =>
      match findWorktree? s path with
      | none => (.error { kind := .notARepo, message := "not a git repository" }, s)
      | some w =>
        let stagedEntries := w.staged.map fun (p, v?) =>
          { indexStatus := some (if v?.isSome then .modified else .deleted), worktreeStatus := none, path := p }
        let unstagedEntries := w.unstaged.map fun (p, v?) =>
          { indexStatus := none, worktreeStatus := some (if v?.isSome then .modified else .deleted), path := p }
        let untrackedEntries := w.untracked.map fun p =>
          { indexStatus := some .untracked, worktreeStatus := some .untracked, path := p }
        let conflictEntries := w.conflicts.map fun p =>
          { indexStatus := some .unmerged, worktreeStatus := some .unmerged, path := p }
        (.ok (stagedEntries ++ unstagedEntries ++ untrackedEntries ++ conflictEntries).toArray, s)
    diffNameStatus := fun path revA revB? _ s =>
      if !isValidStrictRevSpec revA then
        (.error { kind := .invalidInput, message := s!"invalid rev '{revA}'" }, s)
      else if match revB? with | some r => !isValidStrictRevSpec r | none => false then
        (.error { kind := .invalidInput, message := "invalid revB" }, s)
      else
        match findWorktree? s path with
        | none => (.error { kind := .notARepo, message := "not a git repository" }, s)
        | some _ =>
          match resolveRefStrInRepo s path revA with
          | none => (.error { kind := .invalidRef, message := s!"unknown revision '{revA}'" }, s)
          | some _ => (.ok #[], s)
    listWorktrees := fun path s =>
      match findWorktree? s path with
      | none => (.error { kind := .notARepo, message := "not a git repository" }, s)
      | some _ =>
        let infos := s.worktrees.map fun w =>
          match w.head with
          | .attached b c? =>
            { path := w.path, head? := c?, branch? := some b, isBare := w.isBare, isLocked := w.isLocked }
          | .detached c =>
            { path := w.path, head? := some c, branch? := none, isBare := w.isBare, isDetached := true, isLocked := w.isLocked }
        (.ok infos.toArray, s)
    showFile? := fun path rev relPath s =>
      if !isValidStrictRevSpec rev || !isValidRelRepoPath relPath then
        (.error { kind := .invalidInput, message := "invalid rev or relPath" }, s)
      else
        match findWorktree? s path with
        | none => (.error { kind := .notARepo, message := "not a git repository" }, s)
        | some _ =>
          match resolveRefStrInRepo s path rev with
          | none => (.error { kind := .invalidRef, message := s!"unknown revision '{rev}'" }, s)
          | some cid =>
            match s.commits.find? (fun c => c.id == cid) with
            | none => (.ok none, s)
            | some node =>
              match node.tree.find? (fun p => p.1 == relPath) with
              | some (_, content) => (.ok (some content.toUTF8), s)
              | none => (.ok none, s)
    init := fun path bare initBranch? =>
      runRepoStepUnit fun _ => stepInit path bare initBranch?
    clone := fun source target opts =>
      if !isValidPathArg source || source.toList.head? == some '-' ||
         !isValidPathArg target || target.toList.head? == some '-' ||
         opts.depth? == some 0 then
        pure (.error { kind := .invalidInput, message := "invalid clone arguments" })
      else
        runRepoStepUnit fun _ => stepInit target opts.bare none
    add := fun path paths all =>
      runRepoStepUnit fun s => stepAdd s path paths all
    commit := fun path opts =>
      runRepoStep fun s => stepCommit s path opts (mkSyntheticCommitId s.commits.length)
    createBranch := fun path branch startPoint? force =>
      fun s =>
        let target? :=
          match startPoint? with
          | some sp => resolveRefStrInRepo s path sp
          | none =>
            match findWorktree? s path with
            | some w => headCommitOfSlot w.head
            | none => none
        match target? with
        | none => (.error { kind := .invalidRef, message := "invalid startPoint" }, s)
        | some cid => runRepoStepUnit (fun st => stepCreateBranch st branch cid force) s
    deleteBranch := fun _ branch force =>
      runRepoStepUnit fun s => stepDeleteBranch s branch force
    checkout := fun path target force =>
      runRepoStepUnit fun s => stepCheckout s path target force
    switch := fun path branch create startPoint? force =>
      fun s =>
        match startPoint? with
        | some sp =>
          if !isValidRevSpec sp then
            (.error { kind := .invalidInput, message := s!"invalid startPoint '{sp}'" }, s)
          else
            match resolveRefStrInRepo s path sp with
            | none => (.error { kind := .invalidRef, message := s!"unknown startPoint '{sp}'" }, s)
            | some cid => runRepoStepUnit (fun st => stepSwitch st path branch create (some cid) force) s
        | none => runRepoStepUnit (fun st => stepSwitch st path branch create none force) s
    reset := fun path mode rev =>
      fun s =>
        if !isValidRevSpec rev then
          (.error { kind := .invalidInput, message := s!"invalid rev '{rev}'" }, s)
        else
          match resolveRefStrInRepo s path rev with
          | none => (.error { kind := .invalidRef, message := s!"unknown rev '{rev}'" }, s)
          | some cid => runRepoStepUnit (fun st => stepReset st path mode cid) s
    fetch := fun path remote refspec? _ s =>
      if !isValidRemoteOrRefspec remote then
        (.error { kind := .invalidInput, message := s!"invalid remote '{remote}'" }, s)
      else if match refspec? with | some r => !isValidRemoteOrRefspec r | none => false then
        (.error { kind := .invalidInput, message := "invalid refspec" }, s)
      else if (findWorktree? s path).isNone then
        (.error { kind := .notARepo, message := "not a git repository" }, s)
      else
        (.ok (), s)
    worktreeAdd := fun _ opts =>
      runRepoStepUnit fun s => stepWorktreeAdd s opts
    worktreeRemove := fun _ wtPath force =>
      runRepoStepUnit fun s => stepWorktreeRemove s wtPath force
    withWorktree := fun _ opts action => do
      match ← runRepoStepUnit (fun s => stepWorktreeAdd s opts) with
      | .error e => return .error e
      | .ok () =>
        let (actRes, cleanRes) ← MonadFinally.tryFinally' (action opts.path) fun _ =>
          runRepoStepUnit (fun s => stepWorktreeRemove s opts.path opts.force)
        match actRes, cleanRes with
        | .ok a, .ok () => return .ok a
        | .ok _, .error ce => return .error ce
        | .error ae, _ => return .error ae }

/-- Pure state for mocking `RawGitOpsM` invocations and recording sanitized environment overrides. -/
structure GitCliMockState where
  /-- Inherited environment returned by `RawGitOpsM.listEnv`. -/
  inheritedEnv : Array (String × String) := #[]
  /-- Recorded sanitized environment override arrays passed to `execGit`. -/
  recordedEnvs : List (Array (String × Option String)) := []
  /-- Recorded raw git requests passed to `execGit`. -/
  recordedRequests : List GitRawRequest := []
  /-- Handler computing the simulated `GitRawOutput` or `GitError` for a request and call index. -/
  handler : GitRawRequest → Nat → Except GitError GitRawOutput := fun _ _ =>
    .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
  /-- Monotonic invocation counter. -/
  callCount : Nat := 0

/-- Pure `RawGitOpsM (StateM GitCliMockState)` adapter recording requests and sanitized environments. -/
def mockRawOps : RawGitOpsM (StateM GitCliMockState) :=
  { listEnv := fun s => (.ok s.inheritedEnv, s)
    execGit := fun envOverrides req s =>
      let res := s.handler req s.callCount
      let s' :=
        { s with
          recordedEnvs := s.recordedEnvs ++ [envOverrides]
          recordedRequests := s.recordedRequests ++ [req]
          callCount := s.callCount + 1 }
      (res, s') }

end LeanSwe.Git.Model
