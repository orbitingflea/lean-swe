import LeanSwe.EnvVars.Types
import LeanSwe.Process.Types
import LeanSwe.Git.Types

namespace LeanSwe.Git.Impl

open LeanSwe.EnvVars
open LeanSwe.Process
open LeanSwe.Git

/-- Return `true` iff `c` is a lowercase hexadecimal digit (`0`–`9` or `a`–`f`). -/
def isLowerHexCharImpl (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- Return `true` iff `s` is a valid 40-char SHA-1 or 64-char SHA-256 lowercase hex commit ID. -/
def isValidCommitIdStrImpl (s : String) : Bool :=
  let cs := s.toList
  (cs.length == 40 || cs.length == 64) && cs.all isLowerHexCharImpl

/-- Construct a validated `CommitId`, failing with `.invalidRef` on malformed hashes. -/
def mkCommitIdImpl (s : String) : Except GitError CommitId :=
  if isValidCommitIdStrImpl s then
    .ok { hex := s }
  else
    .error { kind := .invalidRef, message := s!"invalid commit id: '{s}'" }

/-- Return `true` iff `c` is an ASCII control character (`< 0x20` or `0x7f`). -/
def isControlCharImpl (c : Char) : Bool :=
  c.toNat < 0x20 || c.toNat == 0x7f

/-- Return `true` iff `c` is an ASCII whitespace character (`' '`, `'\t'`, `'\n'`, or `'\r'`). -/
def isAsciiWhitespaceImpl (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Return `true` iff `cs` contains a NUL character (`Char.ofNat 0`). -/
def hasNulCharImpl : List Char → Bool
  | [] => false
  | c :: cs => c == Char.ofNat 0 || hasNulCharImpl cs

/-- Return `true` iff `cs` starts with the four characters `['G', 'I', 'T', '_']`. -/
def isGitPrefixCharsImpl : List Char → Bool
  | 'G' :: 'I' :: 'T' :: '_' :: _ => true
  | _ => false

/-- Return `true` iff environment variable key `k` begins with `"GIT_"`. -/
def isGitKeyImpl (k : String) : Bool :=
  isGitPrefixCharsImpl k.toList

/-- Return `true` iff `k` is a locale environment variable stripped and pinned to `"C"`. -/
def isLocaleKeyImpl (k : String) : Bool :=
  k == "LC_ALL" || k == "LANG" || k == "LANGUAGE"

/-- Return `true` iff `k` is an allowlisted non-repo-redirecting `GIT_*` identity/date override. -/
def isAllowedExtraGitKeyImpl (k : String) : Bool :=
  k == "GIT_AUTHOR_NAME" ||
  k == "GIT_AUTHOR_EMAIL" ||
  k == "GIT_AUTHOR_DATE" ||
  k == "GIT_COMMITTER_NAME" ||
  k == "GIT_COMMITTER_EMAIL" ||
  k == "GIT_COMMITTER_DATE"

/-- Return `true` iff `cs` contains `'='` or NUL, which are illegal in POSIX env keys. -/
def hasInvalidEnvKeyCharImpl : List Char → Bool
  | [] => false
  | c :: cs => c == '=' || c == Char.ofNat 0 || hasInvalidEnvKeyCharImpl cs

/-- Return `true` iff `k` is a valid non-empty POSIX environment key. -/
def isValidEnvKeyImpl (k : String) : Bool :=
  !k.toList.isEmpty && !hasInvalidEnvKeyCharImpl k.toList

/-- Return `true` iff optional environment value `v?` contains no NUL bytes. -/
def isValidEnvValImpl? : Option String → Bool
  | none => true
  | some v => !hasNulCharImpl v.toList

/-- Non-interactive locale, literal-pathspec, and bare-repository safety defaults injected into every `git` subprocess. -/
def defaultGitSafetyEnvImpl : List (String × Option String) :=
  [ ("LC_ALL", some "C")
  , ("LANG", some "C")
  , ("LANGUAGE", some "C")
  , ("GIT_TERMINAL_PROMPT", some "0")
  , ("GIT_LITERAL_PATHSPECS", some "1")
  , ("GIT_CONFIG_COUNT", some "1")
  , ("GIT_CONFIG_KEY_0", some "safe.bareRepository")
  , ("GIT_CONFIG_VALUE_0", some "all")
  ]

/-- Strip inherited `GIT_*` and locale keys, inject hermetic defaults, and filter `extraEnv`. -/
def cleanGitEnvImpl (inheritedEnv : Array (String × String))
    (extraEnv : Array (String × Option String) := #[]) : Array (String × Option String) :=
  let stripped :=
    (inheritedEnv.toList.filter fun kv => isGitKeyImpl kv.1 || isLocaleKeyImpl kv.1).map fun kv => (kv.1, none)
  let filteredExtra :=
    extraEnv.toList.filter fun kv =>
      isValidEnvKeyImpl kv.1 && isValidEnvValImpl? kv.2 &&
      (!isGitKeyImpl kv.1 || isAllowedExtraGitKeyImpl kv.1) &&
      !isLocaleKeyImpl kv.1
  (stripped ++ defaultGitSafetyEnvImpl ++ filteredExtra).toArray

/-- Return `true` iff character `c` is forbidden in Git reference names. -/
def isInvalidRefCharImpl (c : Char) : Bool :=
  isControlCharImpl c ||
  c == ' ' || c == '~' || c == '^' || c == ':' ||
  c == '?' || c == '*' || c == '[' || c == '\\'

/-- Return `true` iff `cs` begins with `pref`. -/
def startsWithCharsImpl : List Char → List Char → Bool
  | [], _ => true
  | _, [] => false
  | p :: ps, c :: cs => p == c && startsWithCharsImpl ps cs

/-- Return `true` iff `needle` occurs as a contiguous sublist of `haystack`. -/
def hasSubstrCharsImpl (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | c :: cs => if startsWithCharsImpl needle (c :: cs) then true else hasSubstrCharsImpl needle cs

/-- Return `true` iff `cs` ends with suffix `suf`. -/
def endsWithCharsImpl (suf cs : List Char) : Bool :=
  startsWithCharsImpl suf.reverse cs.reverse

/-- Tail-recursive worker splitting `cs` on `'/'` separators. -/
def splitSlashLoopImpl (cur : List Char) (revSegs : List (List Char)) : List Char → List (List Char)
  | [] => (cur.reverse :: revSegs).reverse
  | c :: cs =>
    if c == '/' then splitSlashLoopImpl [] (cur.reverse :: revSegs) cs
    else splitSlashLoopImpl (c :: cur) revSegs cs

/-- Split `cs` on `'/'` separators. -/
def splitSlashCharsImpl (cs : List Char) : List (List Char) :=
  splitSlashLoopImpl [] [] cs

/-- Validate a single slash-delimited Git ref component including `.lock` headroom (`<= 240` UTF-8 bytes). -/
def isValidRefComponentImpl (comp : List Char) : Bool :=
  !comp.isEmpty &&
  comp.head? != some '.' &&
  !endsWithCharsImpl ['.'] comp &&
  !endsWithCharsImpl ['.', 'l', 'o', 'c', 'k'] comp &&
  (String.ofList comp).utf8ByteSize <= 240

/-- Return `true` iff `s` satisfies hardened `git check-ref-format` safety rules and byte bounds. -/
def isValidRefNameStrImpl (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty &&
  s.utf8ByteSize <= 1024 &&
  s != "HEAD" &&
  cs.head? != some '-' &&
  cs.head? != some '/' &&
  !endsWithCharsImpl ['/'] cs &&
  cs != ['@'] &&
  !cs.any isInvalidRefCharImpl &&
  !hasSubstrCharsImpl ['.', '.'] cs &&
  !hasSubstrCharsImpl ['@', '{'] cs &&
  !hasSubstrCharsImpl ['/', '/'] cs &&
  (splitSlashCharsImpl cs).all isValidRefComponentImpl

/-- Construct a validated `RefName`, failing with `.invalidRef` if unsafe or malformed. -/
def mkRefNameImpl (s : String) : Except GitError RefName :=
  if isValidRefNameStrImpl s then
    .ok { raw := s }
  else
    .error { kind := .invalidRef, message := s!"invalid git reference name: '{s}'" }

/-- Return `true` iff `s` is a non-empty revision spec without leading `'-'` or control characters. -/
def isValidRevSpecImpl (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty && cs.head? != some '-' && !cs.any isControlCharImpl

/-- Return `true` iff `s` is a single-commit revision spec without whitespace, `':'`, or `".."`. -/
def isValidStrictRevSpecImpl (s : String) : Bool :=
  let cs := s.toList
  isValidRevSpecImpl s &&
  !cs.any isAsciiWhitespaceImpl &&
  !cs.contains ':' &&
  !hasSubstrCharsImpl ['.', '.'] cs

/-- Return `true` iff `s` is a non-empty path argument without NUL bytes. -/
def isValidPathArgImpl (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty && !hasNulCharImpl cs

/-- Validate a filesystem path argument (`invalidPath` on empty/NUL, `invalidInput` on length/segment overflow). -/
def validateFsPathArgImpl (p : String) : Except GitError Unit :=
  if !isValidPathArgImpl p then
    .error { kind := .invalidPath, message := "invalid path argument" }
  else if p.utf8ByteSize >= 4096 || (p.splitOn "/").any (fun seg => seg.utf8ByteSize > 255) then
    .error { kind := .invalidInput, message := "path argument exceeds byte limit" }
  else
    .ok ()

/-- Validate a `clone` source or target endpoint (`invalidInput` on all malformed or oversized inputs). -/
def validateCloneEndpointImpl (p : String) : Except GitError Unit :=
  if !isValidPathArgImpl p || p.startsWith "-" || p.utf8ByteSize >= 4096 ||
      (p.splitOn "/").any (fun seg => seg.utf8ByteSize > 255) then
    .error { kind := .invalidInput, message := "invalid clone endpoint" }
  else
    .ok ()

/-- Validate a single repository-relative path (`invalidPath` on traversal/empty/leading-slash/`.git`, `invalidInput` on length overflow). -/
def validateRelRepoPathImpl (p : String) : Except GitError Unit :=
  if !isValidPathArgImpl p then
    .error { kind := .invalidPath, message := s!"invalid repository relative path: '{p}'" }
  else
    let segs := p.splitOn "/"
    if p.startsWith "/" || p.endsWith "/" ||
        segs.any (fun s => s.isEmpty || s == "." || s == ".." || s == ".git") then
      .error { kind := .invalidPath, message := s!"invalid repository relative path: '{p}'" }
    else if p.utf8ByteSize >= 4096 || segs.any (fun s => s.utf8ByteSize > 255) then
      .error { kind := .invalidInput, message := s!"repository relative path exceeds length limit: '{p}'" }
    else
      .ok ()

/-- Return `true` iff `s` is a safe non-empty remote or refspec token without leading `'-'`, control chars, whitespace, or length overflow. -/
def isValidRemoteOrRefspecImpl (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty &&
  s.utf8ByteSize <= 1024 &&
  cs.head? != some '-' &&
  !cs.any isControlCharImpl &&
  !cs.any isAsciiWhitespaceImpl

/-- Parse a decimal digit sequence into `Nat`, returning `none` on empty or non-digit input. -/
def parseNatDigitsAuxImpl (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: cs =>
    if '0' ≤ c && c ≤ '9' then
      parseNatDigitsAuxImpl (acc * 10 + (c.toNat - '0'.toNat)) cs
    else
      none

/-- Return `true` iff character `c` is treated as a CRUD character by Git's `ident.c`. -/
def isCrudCharImpl (c : Char) : Bool :=
  c ≤ ' ' || c == '.' || c == ',' || c == ':' || c == ';' ||
  c == '<' || c == '>' || c == '"' || c == '\'' || c == '\\'

/-- Return `true` iff character `c` is a non-CRUD Git ident character. -/
def isNonCrudIdentCharImpl (c : Char) : Bool :=
  !isCrudCharImpl c

/-- Validate `CommitOptions` message and optional author/committer identity fields. -/
def validateCommitOptionsImpl (opts : CommitOptions) : Except GitError Unit := do
  if opts.message.isEmpty || hasNulCharImpl opts.message.toList || opts.message.utf8ByteSize > 1048576 then
    .error { kind := .invalidInput, message := "commit message must be non-empty, <= 1 MiB, without NUL bytes" }
  if let some n := opts.authorName then
    if n.utf8ByteSize > 4096 || n.toList.any isControlCharImpl || n.contains '<' || n.contains '>' ||
        !n.toList.any isNonCrudIdentCharImpl then
      .error { kind := .invalidInput, message := "invalid commit author name" }
  if let some em := opts.authorEmail then
    if em.isEmpty || em.utf8ByteSize > 4096 || em.toList.any isControlCharImpl ||
        em.contains '<' || em.contains '>' then
      .error { kind := .invalidInput, message := "invalid commit author email" }

/-- Tail-recursive worker splitting NUL-terminated non-empty records. -/
def splitNulRecordsLoopImpl (acc : List Char) (revOut : List String) : List Char → Option (List String)
  | [] => if acc.isEmpty then some revOut.reverse else none
  | c :: cs =>
    if c == Char.ofNat 0 then
      if acc.isEmpty then none
      else splitNulRecordsLoopImpl [] (String.ofList acc.reverse :: revOut) cs
    else
      splitNulRecordsLoopImpl (c :: acc) revOut cs

/-- Split a NUL-terminated stream into non-empty records (`[]` returns `some []`). -/
def splitNulRecordsImpl (s : String) : Option (List String) :=
  splitNulRecordsLoopImpl [] [] s.toList

/-- Map a single `git status --porcelain=v1` status character to `Option StatusKind`. -/
def statusCharToKindImpl? : Char → Option (Option StatusKind)
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
def isValidStatusPairImpl (x y : Char) : Bool :=
  (statusCharToKindImpl? x).isSome &&
  (statusCharToKindImpl? y).isSome &&
  (x == '?' ↔ y == '?') &&
  (x == '!' ↔ y == '!') &&
  !(x == ' ' && y == ' ')

/-- Tail-recursive worker parsing `git status --porcelain=v1 -z` records. -/
def parsePorcelainStatusLoopImpl (revOut : List StatusEntry) :
    List String → Except GitError (List StatusEntry)
  | [] => .ok revOut.reverse
  | recStr :: rest =>
    match recStr.toList with
    | x :: y :: ' ' :: pathChars =>
      if pathChars.isEmpty || !isValidStatusPairImpl x y then
        .error { kind := .parseError, message := s!"invalid porcelain status entry: '{recStr}'" }
      else
        match statusCharToKindImpl? x, statusCharToKindImpl? y with
        | some ix, some wt =>
          let path := String.ofList pathChars
          if x == 'R' || x == 'C' || y == 'R' || y == 'C' then
            match rest with
            | [] =>
              .error { kind := .parseError, message := s!"truncated rename/copy status entry for '{path}'" }
            | orig :: tail =>
              parsePorcelainStatusLoopImpl
                ({ indexStatus := ix, worktreeStatus := wt, path := path, origPath := some orig } :: revOut)
                tail
          else
            parsePorcelainStatusLoopImpl
              ({ indexStatus := ix, worktreeStatus := wt, path := path, origPath := none } :: revOut)
              rest
        | _, _ =>
          .error { kind := .parseError, message := s!"invalid status characters in '{recStr}'" }
    | _ =>
      .error { kind := .parseError, message := s!"malformed porcelain status record: '{recStr}'" }

/-- Parse raw `git status --porcelain=v1 -z` output bytes into `StatusEntry` values. -/
def parsePorcelainStatusZImpl (bytes : ByteArray) : Except GitError (Array StatusEntry) := do
  if bytes.isEmpty then
    return #[]
  match String.fromUTF8? bytes with
  | none => .error { kind := .parseError, message := "git status output is not valid UTF-8" }
  | some text =>
    match splitNulRecordsImpl text with
    | none => .error { kind := .parseError, message := "unterminated or empty record in git status -z output" }
    | some recs =>
      let entries ← parsePorcelainStatusLoopImpl [] recs
      return entries.toArray

/-- Parse optional similarity score digits (empty defaults to `100`). -/
def parseSimilarityScoreImpl (cs : List Char) : Option Nat :=
  if cs.isEmpty then some 100 else parseNatDigitsAuxImpl 0 cs

/-- Tail-recursive worker parsing `git diff --name-status -z` tokens. -/
def parseDiffTokensLoopImpl (revOut : List DiffEntry) : List String → Except GitError (List DiffEntry)
  | [] => .ok revOut.reverse
  | tok :: rest =>
    match tok.toList with
    | ['A'] =>
      match rest with
      | path :: tail => parseDiffTokensLoopImpl ({ kind := .added, path := path } :: revOut) tail
      | [] => .error { kind := .parseError, message := "truncated A entry in git diff -z" }
    | ['M'] =>
      match rest with
      | path :: tail => parseDiffTokensLoopImpl ({ kind := .modified, path := path } :: revOut) tail
      | [] => .error { kind := .parseError, message := "truncated M entry in git diff -z" }
    | ['D'] =>
      match rest with
      | path :: tail => parseDiffTokensLoopImpl ({ kind := .deleted, path := path } :: revOut) tail
      | [] => .error { kind := .parseError, message := "truncated D entry in git diff -z" }
    | ['T'] =>
      match rest with
      | path :: tail => parseDiffTokensLoopImpl ({ kind := .typeChanged, path := path } :: revOut) tail
      | [] => .error { kind := .parseError, message := "truncated T entry in git diff -z" }
    | ['U'] =>
      match rest with
      | path :: tail => parseDiffTokensLoopImpl ({ kind := .unmerged, path := path } :: revOut) tail
      | [] => .error { kind := .parseError, message := "truncated U entry in git diff -z" }
    | 'R' :: scoreChars =>
      match parseSimilarityScoreImpl scoreChars, rest with
      | some score, orig :: path :: tail =>
        parseDiffTokensLoopImpl ({ kind := .renamed score, path := path, origPath := some orig } :: revOut) tail
      | none, _ =>
        .error { kind := .parseError, message := s!"invalid rename score in '{tok}'" }
      | _, _ =>
        .error { kind := .parseError, message := s!"truncated rename entry '{tok}' in git diff -z" }
    | 'C' :: scoreChars =>
      match parseSimilarityScoreImpl scoreChars, rest with
      | some score, orig :: path :: tail =>
        parseDiffTokensLoopImpl ({ kind := .copied score, path := path, origPath := some orig } :: revOut) tail
      | none, _ =>
        .error { kind := .parseError, message := s!"invalid copy score in '{tok}'" }
      | _, _ =>
        .error { kind := .parseError, message := s!"truncated copy entry '{tok}' in git diff -z" }
    | _ =>
      .error { kind := .parseError, message := s!"unknown git diff status token: '{tok}'" }

/-- Parse raw `git diff --name-status -z` output bytes into `DiffEntry` values. -/
def parseDiffNameStatusZImpl (bytes : ByteArray) : Except GitError (Array DiffEntry) := do
  if bytes.isEmpty then
    return #[]
  match String.fromUTF8? bytes with
  | none => .error { kind := .parseError, message := "git diff output is not valid UTF-8" }
  | some text =>
    match splitNulRecordsImpl text with
    | none => .error { kind := .parseError, message := "unterminated or empty record in git diff -z output" }
    | some toks =>
      let entries ← parseDiffTokensLoopImpl [] toks
      return entries.toArray

/-- Tail-recursive worker splitting NUL-terminated tokens allowing empty tokens. -/
def splitNulTokensAllowEmptyLoopImpl (acc : List Char) (revOut : List String) :
    List Char → Option (List String)
  | [] => if acc.isEmpty then some revOut.reverse else none
  | c :: cs =>
    if c == Char.ofNat 0 then
      splitNulTokensAllowEmptyLoopImpl [] (String.ofList acc.reverse :: revOut) cs
    else
      splitNulTokensAllowEmptyLoopImpl (c :: acc) revOut cs

/-- Tail-recursive worker grouping NUL-terminated tokens into worktree stanzas. -/
def splitWorktreeStanzasLoopImpl (cur : List String) (revOut : List (List String)) :
    List String → Option (List (List String))
  | [] => if cur.isEmpty then some revOut.reverse else none
  | "" :: rest =>
    if cur.isEmpty then none
    else splitWorktreeStanzasLoopImpl [] (cur.reverse :: revOut) rest
  | tok :: rest => splitWorktreeStanzasLoopImpl (tok :: cur) revOut rest

/-- Return `true` iff `s` is an all-zero unborn `HEAD` hash (40 or 64 `'0'` digits). -/
def isAllZerosCommitStrImpl (s : String) : Bool :=
  let cs := s.toList
  (cs.length == 40 || cs.length == 64) && cs.all (· == '0')

/-- Strip a prefix `pref` from `cs`, returning `some suffix` if matched. -/
def stripPrefixCharsImpl : List Char → List Char → Option (List Char)
  | [], rest => some rest
  | _ :: _, [] => none
  | p :: ps, c :: cs => if p == c then stripPrefixCharsImpl ps cs else none

/-- Parse attribute lines within a single `git worktree list --porcelain -z` stanza. -/
def parseWorktreeAttrsImpl (info : WorktreeInfo) (headSeen : Bool) :
    List String → Except GitError (WorktreeInfo × Bool)
  | [] => .ok (info, headSeen)
  | line :: rest =>
    let cs := line.toList
    if line == "bare" then
      parseWorktreeAttrsImpl { info with isBare := true } headSeen rest
    else if line == "detached" then
      parseWorktreeAttrsImpl { info with isDetached := true } headSeen rest
    else if line == "locked" then
      parseWorktreeAttrsImpl { info with isLocked := true, lockReason := none } headSeen rest
    else if line == "prunable" then
      parseWorktreeAttrsImpl { info with isPrunable := true, pruneReason := none } headSeen rest
    else
      match stripPrefixCharsImpl ['H', 'E', 'A', 'D', ' '] cs with
      | some shaChars =>
        let sha := String.ofList shaChars
        if isAllZerosCommitStrImpl sha then
          parseWorktreeAttrsImpl { info with head? := none } true rest
        else
          match mkCommitIdImpl sha with
          | .ok cid => parseWorktreeAttrsImpl { info with head? := some cid } true rest
          | .error _ =>
            .error { kind := .parseError, message := s!"invalid HEAD hash in worktree list: '{sha}'" }
      | none =>
        match stripPrefixCharsImpl ['b', 'r', 'a', 'n', 'c', 'h', ' '] cs with
        | some refChars =>
          match stripPrefixCharsImpl ['r', 'e', 'f', 's', '/', 'h', 'e', 'a', 'd', 's', '/'] refChars with
          | some shortChars =>
            match mkRefNameImpl (String.ofList shortChars) with
            | .ok ref => parseWorktreeAttrsImpl { info with branch? := some ref } headSeen rest
            | .error _ =>
              .error { kind := .parseError, message := s!"invalid branch ref in worktree list: '{String.ofList refChars}'" }
          | none =>
            .error { kind := .parseError, message := s!"worktree branch does not start with refs/heads/: '{String.ofList refChars}'" }
        | none =>
          match stripPrefixCharsImpl ['l', 'o', 'c', 'k', 'e', 'd', ' '] cs with
          | some reasonChars =>
            parseWorktreeAttrsImpl { info with isLocked := true, lockReason := some (String.ofList reasonChars) } headSeen rest
          | none =>
            match stripPrefixCharsImpl ['p', 'r', 'u', 'n', 'a', 'b', 'l', 'e', ' '] cs with
            | some reasonChars =>
              parseWorktreeAttrsImpl { info with isPrunable := true, pruneReason := some (String.ofList reasonChars) } headSeen rest
            | none =>
              parseWorktreeAttrsImpl info headSeen rest

/-- Parse a single non-empty worktree stanza into a `WorktreeInfo`. -/
def parseWorktreeStanzaImpl : List String → Except GitError WorktreeInfo
  | [] => .error { kind := .parseError, message := "empty worktree stanza" }
  | header :: attrs =>
    match stripPrefixCharsImpl ['w', 'o', 'r', 'k', 't', 'r', 'e', 'e', ' '] header.toList with
    | none => .error { kind := .parseError, message := s!"worktree stanza missing 'worktree ' header: '{header}'" }
    | some pathChars =>
      if pathChars.isEmpty then
        .error { kind := .parseError, message := "empty worktree path in porcelain output" }
      else do
        let base : WorktreeInfo := { path := String.ofList pathChars, head? := none, branch? := none }
        let (info, headSeen) ← parseWorktreeAttrsImpl base false attrs
        if !info.isBare && !headSeen then
          .error { kind := .parseError, message := s!"non-bare worktree '{info.path}' missing HEAD attribute" }
        else
          .ok info

/-- Tail-recursive worker parsing all stanzas in a `git worktree list --porcelain -z` response. -/
def parseWorktreeStanzasLoopImpl (revOut : List WorktreeInfo) :
    List (List String) → Except GitError (List WorktreeInfo)
  | [] => .ok revOut.reverse
  | st :: rest =>
    match parseWorktreeStanzaImpl st with
    | .ok info => parseWorktreeStanzasLoopImpl (info :: revOut) rest
    | .error e => .error e

/-- Parse raw `git worktree list --porcelain -z` output bytes into `WorktreeInfo` values. -/
def parseWorktreeListPorcelainImpl (bytes : ByteArray) : Except GitError (Array WorktreeInfo) := do
  if bytes.isEmpty then
    return #[]
  match String.fromUTF8? bytes with
  | none => .error { kind := .parseError, message := "git worktree output is not valid UTF-8" }
  | some text =>
    match splitNulTokensAllowEmptyLoopImpl [] [] text.toList with
    | none => .error { kind := .parseError, message := "unterminated NUL stream in git worktree output" }
    | some toks =>
      match splitWorktreeStanzasLoopImpl [] [] toks with
      | none => .error { kind := .parseError, message := "malformed stanza framing in git worktree output" }
      | some stanzas =>
        let infos ← parseWorktreeStanzasLoopImpl [] stanzas
        return infos.toArray

/-- Convert a single ASCII uppercase character to lowercase. -/
def asciiLowerChar (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- Convert ASCII uppercase letters in `s` to lowercase. -/
def asciiLower (s : String) : String :=
  String.ofList (s.toList.map asciiLowerChar)

/-- Return `true` iff `needle` appears in `haystack` under ASCII case-insensitive matching. -/
def containsSubstrCI (needle haystack : String) : Bool :=
  hasSubstrCharsImpl (asciiLower needle).toList (asciiLower haystack).toList

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
  let dropL := s.toList.dropWhile isAsciiWhitespaceImpl
  String.ofList (dropL.reverse.dropWhile isAsciiWhitespaceImpl).reverse

/-- Ensure `msg` is non-empty, falling back to `fallback` when empty. -/
def ensureNonEmptyMsg (fallback msg : String) : String :=
  let t := trimAsciiWhitespace msg
  if t.isEmpty then fallback else t

/-- Validate all caller-supplied environment entries via `isValidEnvKeyImpl` and `isValidEnvValImpl?`. -/
def validateExtraEnv (extra : Array (String × Option String)) : Except GitError Unit :=
  if extra.all (fun kv => isValidEnvKeyImpl kv.1 && isValidEnvValImpl? kv.2) then
    .ok ()
  else
    .error { kind := .invalidInput, message := "invalid environment key or value" }

/-- Validate `cwd` if present via `isValidPathArgImpl`. -/
def validateCwd? : Option String → Except GitError Unit
  | none => .ok ()
  | some p =>
    if isValidPathArgImpl p then
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
  startsWithCharsImpl "fatal:".toList cs || startsWithCharsImpl "error:".toList cs ||
  startsWithCharsImpl "warning:".toList cs || startsWithCharsImpl "hint:".toList cs

private def filterDiagLinesAux (skipIgnored : Bool) (acc : List String) : List String → List String
  | [] => acc.reverse
  | ln :: rest =>
    let low := ln.toList.map asciiLowerChar
    let dropTab := low.head? == some '\t'
    let trimmedLow := low.dropWhile (· == ' ')
    let isHint := startsWithCharsImpl "hint:".toList trimmedLow
    let startsIgn := startsWithCharsImpl "the following paths are ignored".toList trimmedLow
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
  hasSubstrCharsImpl needle.toList hayLower

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
      if !req.args.all (fun a => !hasNulCharImpl a.toList) then
        return .error { kind := .invalidInput, message := "git argument contains NUL byte" }
      match ← ops.listEnv with
      | .error e => return .error e
      | .ok inherited =>
        let envOverrides := cleanGitEnvImpl inherited req.extraEnv
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
  validateFsPathArgImpl repoPath

end LeanSwe.Git.Impl
