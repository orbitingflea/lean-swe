import Std.Data.TreeMap
import Std.Data.TreeMap.Raw
import Std.Data.TreeSet
import Std.Data.TreeSet.Raw
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

/-- Return `true` iff `k` is a locale environment variable stripped and pinned to `"C"`. -/
def isLocaleKey (k : String) : Bool :=
  k == "LC_ALL" || k == "LANG" || k == "LANGUAGE"

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

/-- Non-interactive locale, literal-pathspec, and bare-repository safety defaults injected into every `git` subprocess. -/
def defaultGitSafetyEnv : List (String × Option String) :=
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
def cleanGitEnv (inheritedEnv : Array (String × String))
    (extraEnv : Array (String × Option String) := #[]) : Array (String × Option String) :=
  let stripped :=
    (inheritedEnv.toList.filter fun kv => isGitKey kv.1 || isLocaleKey kv.1).map fun kv => (kv.1, none)
  let filteredExtra :=
    extraEnv.toList.filter fun kv =>
      isValidEnvKey kv.1 && isValidEnvVal? kv.2 &&
      (!isGitKey kv.1 || isAllowedExtraGitKey kv.1) &&
      !isLocaleKey kv.1
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
  | c :: cs => if startsWithChars needle (c :: cs) then true else hasSubstrChars needle cs

/-- Return `true` iff `cs` ends with suffix `suf`. -/
def endsWithChars (suf cs : List Char) : Bool :=
  startsWithChars suf.reverse cs.reverse

/-- Tail-recursive worker splitting `cs` on `'/'` separators. -/
def splitSlashLoop (cur : List Char) (revSegs : List (List Char)) : List Char → List (List Char)
  | [] => (cur.reverse :: revSegs).reverse
  | c :: cs =>
    if c == '/' then splitSlashLoop [] (cur.reverse :: revSegs) cs
    else splitSlashLoop (c :: cur) revSegs cs

/-- Split `cs` on `'/'` separators. -/
def splitSlashChars (cs : List Char) : List (List Char) :=
  splitSlashLoop [] [] cs

/-- Validate a single slash-delimited Git ref component including `.lock` headroom (`<= 240` UTF-8 bytes). -/
def isValidRefComponent (comp : List Char) : Bool :=
  !comp.isEmpty &&
  comp.head? != some '.' &&
  !endsWithChars ['.'] comp &&
  !endsWithChars ['.', 'l', 'o', 'c', 'k'] comp &&
  (String.ofList comp).utf8ByteSize <= 240

/-- Return `true` iff `s` satisfies hardened `git check-ref-format` safety rules and byte bounds. -/
def isValidRefNameStr (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty &&
  s.utf8ByteSize <= 1024 &&
  s != "HEAD" &&
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

/-- Validate a filesystem path argument (`invalidPath` on empty/NUL, `invalidInput` on length/segment overflow). -/
def validateFsPathArg (p : String) : Except GitError Unit :=
  if !isValidPathArg p then
    .error { kind := .invalidPath, message := "invalid path argument" }
  else if p.utf8ByteSize >= 4096 || (p.splitOn "/").any (fun seg => seg.utf8ByteSize > 255) then
    .error { kind := .invalidInput, message := "path argument exceeds byte limit" }
  else
    .ok ()

/-- Validate a `clone` source or target endpoint (`invalidInput` on all malformed or oversized inputs). -/
def validateCloneEndpoint (p : String) : Except GitError Unit :=
  if !isValidPathArg p || p.startsWith "-" || p.utf8ByteSize >= 4096 ||
      (p.splitOn "/").any (fun seg => seg.utf8ByteSize > 255) then
    .error { kind := .invalidInput, message := "invalid clone endpoint" }
  else
    .ok ()

/-- Validate a single repository-relative path (`invalidPath` on traversal/empty/leading-slash/`.git`, `invalidInput` on length overflow). -/
def validateRelRepoPath (p : String) : Except GitError Unit :=
  if !isValidPathArg p then
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

/-- Validate an array of repository-relative paths and enforce the 64 KiB total argument budget. -/
def validateRelRepoPaths (paths : Array String) : Except GitError Unit := do
  paths.toList.forM validateRelRepoPath
  let totalBytes := paths.foldl (fun n s => n + s.utf8ByteSize + 1) 0
  if totalBytes > 65536 then
    .error { kind := .invalidInput, message := "paths argument exceeds 64 KiB budget" }
  else
    .ok ()

/-- Return `true` iff `s` is a valid non-empty relative repository path without leading `'/'` or `".."` segments. -/
def isValidRelRepoPath (s : String) : Bool :=
  match validateRelRepoPath s with
  | .ok () => true
  | .error _ => false

/-- Return `true` iff `p` requires non-deterministic pathspec handling beyond normalized relative paths. Under `GIT_LITERAL_PATHSPECS=1`, wildcard/magic characters (`*`, `?`, `[`, `\`, leading `:`, leading `-`) are treated as literal filename characters and normalize cleanly. -/
def isExtendedPathspec (p : String) : Bool :=
  if !isValidPathArg p || p.utf8ByteSize >= 4096 then
    true
  else if p.startsWith "/" then
    true
  else if p == "." || p == "./" then
    false
  else
    let bodyCs := match p.toList with | '.' :: '/' :: rest => rest | cs => cs
    let cleanCs := if bodyCs.getLast? == some '/' && bodyCs.length > 1 then bodyCs.dropLast else bodyCs
    !isValidRelRepoPath (String.ofList cleanCs)

/-- Return `true` iff `s` is a safe non-empty remote or refspec token without leading `'-'`, control chars, whitespace, or length overflow. -/
def isValidRemoteOrRefspec (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty &&
  s.utf8ByteSize <= 1024 &&
  cs.head? != some '-' &&
  !cs.any isControlChar &&
  !cs.any isAsciiWhitespace

/-- Parse a decimal digit sequence into `Nat`, returning `none` on empty or non-digit input. -/
def parseNatDigitsAux (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: cs =>
    if '0' ≤ c && c ≤ '9' then
      parseNatDigitsAux (acc * 10 + (c.toNat - '0'.toNat)) cs
    else
      none

/-- Base target of a parsed supported revision specification. -/
inductive RevBase where
  /-- Current worktree/repository `HEAD` (or `@`). -/
  | head
  /-- Full 40-char SHA-1 or 64-char SHA-256 commit ID. -/
  | commitId (cid : CommitId)
  /-- Symbolic ref name (`main`, `refs/heads/main`, `origin/main`, etc.). -/
  | ref (name : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Single parent-traversal suffix step (`~k` or `^k`). -/
inductive RevStep where
  /-- First-parent chain traversal `~k`. -/
  | tilde (count : Nat)
  /-- `k`-th parent selection `^k` (`^0` peels to commit). -/
  | caret (parentIdx : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Parsed supported revision grammar `<base>(~<digits>? | ^<digits>?)*`. -/
structure ParsedRev where
  /-- Revision base (`HEAD`/`@`, full `CommitId`, or ref name). -/
  base : RevBase
  /-- Ordered parent-traversal suffix steps. -/
  steps : List RevStep
  deriving Repr, BEq, DecidableEq, Inhabited

private def parseRevDigits : List Char → Option (Nat × List Char)
  | cs =>
    let digits := cs.takeWhile (fun c => '0' ≤ c && c ≤ '9')
    let rest := cs.dropWhile (fun c => '0' ≤ c && c ≤ '9')
    if digits.isEmpty then
      some (1, rest)
    else if digits.length > 6 then
      none
    else
      (parseNatDigitsAux 0 digits).map (·, rest)

private def parseRevStepsLoop (fuel : Nat) (cs : List Char) (acc : List RevStep) : Option (List RevStep) :=
  match fuel with
  | 0 => none
  | f + 1 =>
    match cs with
    | [] => some acc.reverse
    | '~' :: rest =>
      match parseRevDigits rest with
      | none => none
      | some (k, tail) =>
        match tail with
        | [] => some ((.tilde k :: acc).reverse)
        | '~' :: _ | '^' :: _ => parseRevStepsLoop f tail (.tilde k :: acc)
        | _ => none
    | '^' :: rest =>
      match parseRevDigits rest with
      | none => none
      | some (k, tail) =>
        match tail with
        | [] => some ((.caret k :: acc).reverse)
        | '~' :: _ | '^' :: _ => parseRevStepsLoop f tail (.caret k :: acc)
        | _ => none
    | _ => none

/-- Parse `~<digits>?` and `^<digits>?` revision suffix steps bounded by `fuel`. -/
def parseRevStepsAux (fuel : Nat) (cs : List Char) : Option (List RevStep) :=
  parseRevStepsLoop fuel cs []

/-- Parse a revision string under `<base>(~<digits>? | ^<digits>?)*` (`utf8ByteSize <= 1024`). -/
def parseSupportedRevSpec (s : String) : Option ParsedRev :=
  if s.toList.isEmpty || s.utf8ByteSize > 1024 then
    none
  else
    let cs := s.toList
    let baseChars := cs.takeWhile (fun c => c != '~' && c != '^')
    let suffixChars := cs.dropWhile (fun c => c != '~' && c != '^')
    let baseStr := String.ofList baseChars
    let base? : Option RevBase :=
      if baseStr == "HEAD" || baseStr == "@" then
        some .head
      else if isValidCommitIdStr baseStr then
        some (.commitId { hex := baseStr })
      else if isValidRefNameStr baseStr then
        some (.ref baseStr)
      else
        none
    match base?, parseRevStepsAux (suffixChars.length + 1) suffixChars with
    | some b, some steps => some { base := b, steps := steps }
    | _, _ => none

/-- Return `true` iff character `c` is treated as a CRUD character by Git's `ident.c`. -/
def isCrudChar (c : Char) : Bool :=
  c ≤ ' ' || c == '.' || c == ',' || c == ':' || c == ';' ||
  c == '<' || c == '>' || c == '"' || c == '\'' || c == '\\'

/-- Return `true` iff character `c` is a non-CRUD Git ident character. -/
def isNonCrudIdentChar (c : Char) : Bool :=
  !isCrudChar c

/-- Validate `CommitOptions` message and optional author/committer identity fields. -/
def validateCommitOptions (opts : CommitOptions) : Except GitError Unit := do
  if opts.message.isEmpty || hasNulChar opts.message.toList || opts.message.utf8ByteSize > 1048576 then
    .error { kind := .invalidInput, message := "commit message must be non-empty, <= 1 MiB, without NUL bytes" }
  if let some n := opts.authorName then
    if n.utf8ByteSize > 4096 || n.toList.any isControlChar || n.contains '<' || n.contains '>' ||
        !n.toList.any isNonCrudIdentChar then
      .error { kind := .invalidInput, message := "invalid commit author name" }
  if let some em := opts.authorEmail then
    if em.isEmpty || em.utf8ByteSize > 4096 || em.toList.any isControlChar ||
        em.contains '<' || em.contains '>' then
      .error { kind := .invalidInput, message := "invalid commit author email" }

/-- Parsed fetch refspec (`[+]<src>[:<dst>]`), including single-`'*'`-anywhere wildcard patterns. -/
structure ParsedFetchRefspec where
  /-- Whether leading `'+'` force flag was set. -/
  force : Bool
  /-- Source ref name, or source prefix before `'*'` when `isGlob = true`. -/
  src : String
  /-- Source suffix after `'*'` when `isGlob = true` (empty for non-glob or trailing `*`). -/
  srcSuffix : String := ""
  /-- Optional destination ref name, or destination prefix before `'*'` when `isGlob = true`. -/
  dst? : Option String
  /-- Destination suffix after `'*'` when `isGlob = true` (empty for non-glob or trailing `*`). -/
  dstSuffix : String := ""
  /-- Whether both `src` and `dst` carry a single `'*'` wildcard pattern. -/
  isGlob : Bool
  /-- Whether missing source ref is silently ignored (default branch-merge fallback). -/
  ignoreMissing : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

private def isValidFetchSrc (s : String) : Bool :=
  s == "HEAD" || isValidRefNameStr s

/-- Match `s` against single-`'*'` glob pattern `pfx ++ "*" ++ sfx`, returning the matched stem. -/
def matchSingleGlob? (pfx sfx s : String) : Option String :=
  if s.startsWith pfx && s.endsWith sfx then
    let cs := s.toList
    let pLen := pfx.toList.length
    let sLen := sfx.toList.length
    if cs.length >= pLen + sLen then
      some (String.ofList ((cs.drop pLen).take (cs.length - pLen - sLen)))
    else
      none
  else
    none

/-- Split a single-`'*'` wildcard pattern into `(prefix, suffix)` matching Git's `REFNAME_REFSPEC_PATTERN` validation. -/
def splitSingleGlob? (s : String) : Option (String × String) :=
  match s.splitOn "*" with
  | [pfx, sfx] =>
    if isValidRefNameStr (pfx ++ "x" ++ sfx) then some (pfx, sfx) else none
  | _ => none

/-- Qualify a non-empty non-glob `git fetch` destination ref matching `remote.c:get_fetch_map`. -/
def qualifyFetchDstRef (dstRaw : String) : String :=
  if dstRaw.startsWith "refs/" then
    dstRaw
  else if dstRaw.startsWith "heads/" || dstRaw.startsWith "tags/" || dstRaw.startsWith "remotes/" then
    "refs/" ++ dstRaw
  else
    "refs/heads/" ++ dstRaw

private def isValidFetchDst (s : String) : Bool :=
  isValidRefNameStr s

/-- Parse and validate a `git fetch` refspec (`[+]<src>`, `[+]<src>:<dst>`, or single-`'*'`-anywhere pattern pair). -/
def parseFetchRefspec? (raw : String) : Option ParsedFetchRefspec :=
  if !isValidRemoteOrRefspec raw then
    none
  else
    let (force, body) :=
      if raw.startsWith "+" then (true, String.ofList (raw.toList.drop 1)) else (false, raw)
    if body.isEmpty then
      none
    else
      match body.splitOn ":" with
      | [src] =>
        if !src.contains '*' && isValidFetchSrc src then
          some { force := force, src := src, dst? := none, isGlob := false }
        else
          none
      | [src, dst] =>
        if src.isEmpty || dst.isEmpty then
          none
        else if !src.contains '*' && !dst.contains '*' then
          if isValidFetchSrc src && isValidFetchDst dst then
            some { force := force, src := src, dst? := some dst, isGlob := false }
          else
            none
        else
          match splitSingleGlob? src, splitSingleGlob? dst with
          | some (sp, ss), some (dp, ds) =>
            some { force := force, src := sp, srcSuffix := ss, dst? := some dp, dstSuffix := ds, isGlob := true }
          | _, _ => none
      | _ => none

/-- Strip trailing `'/'` characters from `p`, preserving `"/"` when `p` consists solely of slashes. -/
def stripTrailingSlashes (p : String) : String :=
  let rev := p.toList.reverse.dropWhile (· == '/')
  if rev.isEmpty then
    if p.toList.head? == some '/' then "/" else ""
  else
    String.ofList rev.reverse

/-- Compute the parent directory path character list by stripping the last `'/'`-separated component. -/
def parentPrefixChars? (cs : List Char) : Option (List Char) :=
  let rev := cs.reverse
  match rev.dropWhile (· != '/') with
  | [] => none
  | c :: rest =>
    if c == '/' then
      let stripped := rest.dropWhile (· == '/')
      if stripped.isEmpty then
        if cs != ['/'] && cs.head? == some '/' then some ['/'] else none
      else
        some stripped.reverse
    else
      none

/-- Tail-recursive worker collecting normalized path ancestor candidates left-to-right. -/
def ancestorLoop (revPref : List Char) (acc : List String) : List Char → List String
  | [] =>
    if revPref.isEmpty then acc
    else
      let cur := String.ofList revPref.reverse
      if acc.head? == some cur then acc else cur :: acc
  | '/' :: rest =>
    let acc' :=
      if revPref.isEmpty || revPref.head? == some '/' then acc
      else String.ofList revPref.reverse :: acc
    ancestorLoop ('/' :: revPref) acc' rest
  | c :: rest =>
    ancestorLoop (c :: revPref) acc rest

/-- Return candidate directory paths from `p` itself up to `"/"` or `"."` for anti-nesting probing. -/
def ancestorCandidates (p : String) : List String :=
  let norm := stripTrailingSlashes p
  match norm.toList with
  | [] => []
  | '/' :: rest => ancestorLoop ['/'] ["/"] rest
  | cs => ancestorLoop [] ["."] cs

/-- Return the Git `dwim_ref` candidate full ref names for `r` in exact lookup order. -/
def dwimRefCandidates (r : String) : List String :=
  [r, "refs/" ++ r, "refs/tags/" ++ r, "refs/heads/" ++ r, "refs/remotes/" ++ r, "refs/remotes/" ++ r ++ "/HEAD"]

/-- Tail-recursive worker splitting NUL-terminated non-empty records. -/
def splitNulRecordsLoop (acc : List Char) (revOut : List String) : List Char → Option (List String)
  | [] => if acc.isEmpty then some revOut.reverse else none
  | c :: cs =>
    if c == Char.ofNat 0 then
      if acc.isEmpty then none
      else splitNulRecordsLoop [] (String.ofList acc.reverse :: revOut) cs
    else
      splitNulRecordsLoop (c :: acc) revOut cs

/-- Split NUL-terminated non-empty records, rejecting unterminated non-empty input or empty records. -/
def splitNulRecordsAux (acc : List Char) (cs : List Char) : Option (List String) :=
  splitNulRecordsLoop acc [] cs

/-- Split a NUL-terminated stream into non-empty records (`[]` returns `some []`). -/
def splitNulRecords (s : String) : Option (List String) :=
  splitNulRecordsLoop [] [] s.toList

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

/-- Tail-recursive worker parsing `git status --porcelain=v1 -z` records. -/
def parsePorcelainStatusLoop (revOut : List StatusEntry) :
    List String → Except GitError (List StatusEntry)
  | [] => .ok revOut.reverse
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
              parsePorcelainStatusLoop
                ({ indexStatus := ix, worktreeStatus := wt, path := path, origPath := some orig } :: revOut)
                tail
          else
            parsePorcelainStatusLoop
              ({ indexStatus := ix, worktreeStatus := wt, path := path, origPath := none } :: revOut)
              rest
        | _, _ =>
          .error { kind := .parseError, message := s!"invalid status characters in '{recStr}'" }
    | _ =>
      .error { kind := .parseError, message := s!"malformed porcelain status record: '{recStr}'" }

/-- Parse NUL-separated `git status --porcelain=v1 -z` records (`XY PATH1` followed by `PATH2` for `R`/`C`). -/
def parsePorcelainStatusRecords (xs : List String) : Except GitError (List StatusEntry) :=
  parsePorcelainStatusLoop [] xs

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
      let entries ← parsePorcelainStatusLoop [] recs
      return entries.toArray

/-- Parse optional similarity score digits (empty defaults to `100`). -/
def parseSimilarityScore (cs : List Char) : Option Nat :=
  if cs.isEmpty then some 100 else parseNatDigitsAux 0 cs

/-- Tail-recursive worker parsing `git diff --name-status -z` tokens. -/
def parseDiffTokensLoop (revOut : List DiffEntry) : List String → Except GitError (List DiffEntry)
  | [] => .ok revOut.reverse
  | tok :: rest =>
    match tok.toList with
    | ['A'] =>
      match rest with
      | path :: tail => parseDiffTokensLoop ({ kind := .added, path := path } :: revOut) tail
      | [] => .error { kind := .parseError, message := "truncated A entry in git diff -z" }
    | ['M'] =>
      match rest with
      | path :: tail => parseDiffTokensLoop ({ kind := .modified, path := path } :: revOut) tail
      | [] => .error { kind := .parseError, message := "truncated M entry in git diff -z" }
    | ['D'] =>
      match rest with
      | path :: tail => parseDiffTokensLoop ({ kind := .deleted, path := path } :: revOut) tail
      | [] => .error { kind := .parseError, message := "truncated D entry in git diff -z" }
    | ['T'] =>
      match rest with
      | path :: tail => parseDiffTokensLoop ({ kind := .typeChanged, path := path } :: revOut) tail
      | [] => .error { kind := .parseError, message := "truncated T entry in git diff -z" }
    | ['U'] =>
      match rest with
      | path :: tail => parseDiffTokensLoop ({ kind := .unmerged, path := path } :: revOut) tail
      | [] => .error { kind := .parseError, message := "truncated U entry in git diff -z" }
    | 'R' :: scoreChars =>
      match parseSimilarityScore scoreChars, rest with
      | some score, orig :: path :: tail =>
        parseDiffTokensLoop ({ kind := .renamed score, path := path, origPath := some orig } :: revOut) tail
      | none, _ =>
        .error { kind := .parseError, message := s!"invalid rename score in '{tok}'" }
      | _, _ =>
        .error { kind := .parseError, message := s!"truncated rename entry '{tok}' in git diff -z" }
    | 'C' :: scoreChars =>
      match parseSimilarityScore scoreChars, rest with
      | some score, orig :: path :: tail =>
        parseDiffTokensLoop ({ kind := .copied score, path := path, origPath := some orig } :: revOut) tail
      | none, _ =>
        .error { kind := .parseError, message := s!"invalid copy score in '{tok}'" }
      | _, _ =>
        .error { kind := .parseError, message := s!"truncated copy entry '{tok}' in git diff -z" }
    | _ =>
      .error { kind := .parseError, message := s!"unknown git diff status token: '{tok}'" }

/-- Parse NUL-separated `git diff --name-status -z` tokens (`origPath` before `path` for `R`/`C`). -/
def parseDiffTokens (xs : List String) : Except GitError (List DiffEntry) :=
  parseDiffTokensLoop [] xs

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
      let entries ← parseDiffTokensLoop [] toks
      return entries.toArray

/-- Tail-recursive worker splitting NUL-terminated tokens allowing empty tokens. -/
def splitNulTokensAllowEmptyLoop (acc : List Char) (revOut : List String) :
    List Char → Option (List String)
  | [] => if acc.isEmpty then some revOut.reverse else none
  | c :: cs =>
    if c == Char.ofNat 0 then
      splitNulTokensAllowEmptyLoop [] (String.ofList acc.reverse :: revOut) cs
    else
      splitNulTokensAllowEmptyLoop (c :: acc) revOut cs

/-- Split NUL-terminated tokens allowing empty `""` stanza-delimiter tokens. -/
def splitNulTokensAllowEmptyAux (acc : List Char) (cs : List Char) : Option (List String) :=
  splitNulTokensAllowEmptyLoop acc [] cs

/-- Tail-recursive worker grouping NUL-terminated tokens into worktree stanzas. -/
def splitWorktreeStanzasLoop (cur : List String) (revOut : List (List String)) :
    List String → Option (List (List String))
  | [] => if cur.isEmpty then some revOut.reverse else none
  | "" :: rest =>
    if cur.isEmpty then none
    else splitWorktreeStanzasLoop [] (cur.reverse :: revOut) rest
  | tok :: rest => splitWorktreeStanzasLoop (tok :: cur) revOut rest

/-- Group NUL-terminated tokens into non-empty worktree stanzas terminated by `""`. -/
def splitWorktreeStanzas (cur : List String) (xs : List String) : Option (List (List String)) :=
  splitWorktreeStanzasLoop cur [] xs

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

/-- Tail-recursive worker parsing all stanzas in a `git worktree list --porcelain -z` response. -/
def parseWorktreeStanzasLoop (revOut : List WorktreeInfo) :
    List (List String) → Except GitError (List WorktreeInfo)
  | [] => .ok revOut.reverse
  | st :: rest =>
    match parseWorktreeStanza st with
    | .ok info => parseWorktreeStanzasLoop (info :: revOut) rest
    | .error e => .error e

/-- Parse all stanzas in a `git worktree list --porcelain -z` response. -/
def parseWorktreeStanzas (xs : List (List String)) : Except GitError (List WorktreeInfo) :=
  parseWorktreeStanzasLoop [] xs

/-- Parse raw `git worktree list --porcelain -z` output bytes into `WorktreeInfo` values. -/
def parseWorktreeListPorcelain (bytes : ByteArray) : Except GitError (Array WorktreeInfo) := do
  if bytes.isEmpty then
    return #[]
  match String.fromUTF8? bytes with
  | none => .error { kind := .parseError, message := "git worktree output is not valid UTF-8" }
  | some text =>
    match splitNulTokensAllowEmptyLoop [] [] text.toList with
    | none => .error { kind := .parseError, message := "unterminated NUL stream in git worktree output" }
    | some toks =>
      match splitWorktreeStanzasLoop [] [] toks with
      | none => .error { kind := .parseError, message := "malformed stanza framing in git worktree output" }
      | some stanzas =>
        let infos ← parseWorktreeStanzasLoop [] stanzas
        return infos.toArray

private instance : Repr ByteArray where
  reprPrec bs _ := repr bs.toList

/-- Mode/kind of a tracked Git tree/index entry. -/
inductive GitBlobKind where
  /-- Regular file with optional executable bit (`100644` vs `100755`). -/
  | regular (executable : Bool)
  /-- Symbolic link (`120000`). -/
  | symlink
  /-- Embedded repository gitlink (`160000`). -/
  | gitlink
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Content and mode of a tracked Git blob or symlink entry. -/
structure GitTreeEntry where
  /-- Entry mode/kind. -/
  kind : GitBlobKind
  /-- Raw blob bytes (or symlink target bytes). -/
  bytes : ByteArray
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Pure in-memory host VFS node with raw byte segment names (supporting non-UTF-8 `.parseError` paths). -/
inductive VfsNode where
  /-- Regular file with executable flag and byte payload. -/
  | file (executable : Bool) (bytes : ByteArray)
  /-- Symbolic link storing raw target bytes. -/
  | symlink (target : ByteArray)
  /-- Directory with search/write permissions and named child entries. -/
  | dir (searchable : Bool) (writable : Bool) (children : List (ByteArray × VfsNode))
  deriving Inhabited

private noncomputable def vfsPairStackWeight : List (VfsNode × VfsNode) → Nat
  | [] => 0
  | (a, _) :: rest => sizeOf a + vfsPairStackWeight rest

private def pushVfsChildPairs (acc : List (VfsNode × VfsNode)) :
    List (ByteArray × VfsNode) → List (ByteArray × VfsNode) → Option (List (VfsNode × VfsNode))
  | [], [] => some acc
  | (k1, v1) :: r1, (k2, v2) :: r2 =>
    if k1 == k2 then pushVfsChildPairs ((v1, v2) :: acc) r1 r2 else none
  | _, _ => none

private theorem vfsPairStackWeight_pushVfsChildPairs
    (acc : List (VfsNode × VfsNode)) (cs1 cs2 : List (ByteArray × VfsNode))
    (out : List (VfsNode × VfsNode))
    (h : pushVfsChildPairs acc cs1 cs2 = some out) :
    vfsPairStackWeight out ≤ vfsPairStackWeight acc + sizeOf cs1 := by
  induction cs1 generalizing acc cs2 with
  | nil =>
    cases cs2 with
    | nil =>
      simp only [pushVfsChildPairs, Option.some.injEq] at h
      subst h
      simp
    | cons _ _ =>
      simp [pushVfsChildPairs] at h
  | cons hd1 tl1 ih =>
    cases cs2 with
    | nil =>
      simp [pushVfsChildPairs] at h
    | cons hd2 tl2 =>
      rcases hd1 with ⟨k1, v1⟩
      rcases hd2 with ⟨k2, v2⟩
      simp only [pushVfsChildPairs] at h
      split at h
      · have hRec := ih ((v1, v2) :: acc) tl2 h
        have hSz : sizeOf ((k1, v1) :: tl1) = 1 + (1 + sizeOf k1 + sizeOf v1) + sizeOf tl1 := rfl
        have hW : vfsPairStackWeight ((v1, v2) :: acc) = sizeOf v1 + vfsPairStackWeight acc := rfl
        omega
      · simp at h

private def beqVfsStackLoop : List (VfsNode × VfsNode) → Bool
  | [] => true
  | (.file e1 b1, .file e2 b2) :: stack =>
    if e1 == e2 && b1 == b2 then beqVfsStackLoop stack else false
  | (.symlink t1, .symlink t2) :: stack =>
    if t1 == t2 then beqVfsStackLoop stack else false
  | (.dir sr1 wr1 cs1, .dir sr2 wr2 cs2) :: stack =>
    if sr1 == sr2 && wr1 == wr2 then
      match _h : pushVfsChildPairs stack cs1 cs2 with
      | some stack' => beqVfsStackLoop stack'
      | none => false
    else
      false
  | _ :: _ => false
termination_by stack => vfsPairStackWeight stack
decreasing_by
  · simp only [vfsPairStackWeight, VfsNode.file.sizeOf_spec]
    omega
  · simp only [vfsPairStackWeight, VfsNode.symlink.sizeOf_spec]
    omega
  · have hPush := vfsPairStackWeight_pushVfsChildPairs stack cs1 cs2 stack' _h
    simp only [vfsPairStackWeight, VfsNode.dir.sizeOf_spec]
    omega

instance : BEq VfsNode where
  beq a b := beqVfsStackLoop [(a, b)]

/-- Internal work-stack task for iterative `VfsNode` string formatting. -/
inductive VfsReprTask where
  /-- Format a `VfsNode` entry. -/
  | visit (node : VfsNode)
  /-- Emit a literal string fragment. -/
  | emit (s : String)

private noncomputable def vfsReprTaskWeight : List VfsReprTask → Nat
  | [] => 0
  | .visit n :: rest => 3 * sizeOf n + 3 + vfsReprTaskWeight rest
  | .emit _ :: rest => 1 + vfsReprTaskWeight rest

private def pushReprChildrenRev (first : Bool) (acc : List VfsReprTask) :
    List (ByteArray × VfsNode) → List VfsReprTask
  | [] => acc
  | (k, c) :: rest =>
    let sep := if first then "(" else ", ("
    let hd := sep ++ reprStr k ++ ", "
    pushReprChildrenRev false (.emit ")" :: .visit c :: .emit hd :: acc) rest

private def transferReprTasks (src dst : List VfsReprTask) : List VfsReprTask :=
  match src with
  | [] => dst
  | t :: rest => transferReprTasks rest (t :: dst)

private theorem vfsReprTaskWeight_transfer (src dst : List VfsReprTask) :
    vfsReprTaskWeight (transferReprTasks src dst) = vfsReprTaskWeight src + vfsReprTaskWeight dst := by
  induction src generalizing dst with
  | nil => simp [transferReprTasks, vfsReprTaskWeight]
  | cons t rest ih =>
    simp only [transferReprTasks, ih]
    cases t <;> simp only [vfsReprTaskWeight] <;> omega

private theorem vfsReprTaskWeight_pushReprChildrenRev
    (first : Bool) (acc : List VfsReprTask) (cs : List (ByteArray × VfsNode)) :
    vfsReprTaskWeight (pushReprChildrenRev first acc cs) ≤ vfsReprTaskWeight acc + 3 * sizeOf cs := by
  induction cs generalizing first acc with
  | nil => simp [pushReprChildrenRev]
  | cons hd tl ih =>
    rcases hd with ⟨k, c⟩
    simp only [pushReprChildrenRev]
    have hRec := ih false (.emit ")" :: .visit c :: .emit ((if first then "(" else ", (") ++ reprStr k ++ ", ") :: acc)
    have hSz : sizeOf ((k, c) :: tl) = 1 + (1 + sizeOf k + sizeOf c) + sizeOf tl := rfl
    simp only [vfsReprTaskWeight] at hRec
    omega

private def reprVfsLoop (acc : String) : List VfsReprTask → String
  | [] => acc
  | .emit s :: stack => reprVfsLoop (acc ++ s) stack
  | .visit (.file ex bs) :: stack =>
    reprVfsLoop (acc ++ s!"LeanSwe.Git.Model.VfsNode.file {repr ex} {reprStr bs}") stack
  | .visit (.symlink t) :: stack =>
    reprVfsLoop (acc ++ s!"LeanSwe.Git.Model.VfsNode.symlink {reprStr t}") stack
  | .visit (.dir s w cs) :: stack =>
    let pfx := s!"LeanSwe.Git.Model.VfsNode.dir {repr s} {repr w} ["
    let revTasks := pushReprChildrenRev true [] cs
    let stack' := transferReprTasks revTasks (.emit "]" :: stack)
    reprVfsLoop (acc ++ pfx) stack'
termination_by stack => vfsReprTaskWeight stack
decreasing_by
  · simp only [vfsReprTaskWeight]
    omega
  · simp only [vfsReprTaskWeight, VfsNode.file.sizeOf_spec]
    omega
  · simp only [vfsReprTaskWeight, VfsNode.symlink.sizeOf_spec]
    omega
  · have hPush := vfsReprTaskWeight_pushReprChildrenRev true [] cs
    rw [vfsReprTaskWeight_transfer]
    simp only [vfsReprTaskWeight, VfsNode.dir.sizeOf_spec] at hPush ⊢
    omega

instance : Repr VfsNode where
  reprPrec n _ := Std.Format.text (reprVfsLoop "" [.visit n])

/-- Empty searchable and writable VFS directory node. -/
def VfsNode.emptyDir : VfsNode :=
  .dir true true []

/-- Worktree or bare-repo `HEAD` pointer (`symbolic` resolves `refs/heads/<branch>` dynamically). -/
inductive SymbolicHead where
  /-- Attached to local branch `branch` (unborn iff `refs/heads/<branch>` is absent). -/
  | symbolic (branch : RefName)
  /-- Detached `HEAD` pointing directly at `commit`. -/
  | detached (commit : CommitId)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Unmerged conflict entry in `.git/index`. -/
structure ConflictEntry where
  /-- Repo-relative raw byte path of the conflicted entry. -/
  path : ByteArray
  /-- Stage-2 status character mapped to `StatusKind` (typically `.unmerged`, `.added`, `.deleted`). -/
  oursStatus : StatusKind := .unmerged
  /-- Stage-3 status character mapped to `StatusKind` (typically `.unmerged`, `.added`, `.deleted`). -/
  theirsStatus : StatusKind := .unmerged
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Staging index of a non-bare worktree. -/
structure IndexState where
  /-- Stage-0 tracked entries sorted lexicographically by repo-relative `ByteArray` path. -/
  entries : List (ByteArray × GitTreeEntry) := []
  /-- Unmerged conflict entries (`!conflicts.isEmpty` blocks `commit`, non-force `checkout`/`switch`). -/
  conflicts : List ConflictEntry := []
  /-- Whether `MERGE_HEAD` exists in the worktree gitdir (blocks `switch` and `reset --soft`). -/
  hasMergeHead : Bool := false
  /-- Additional parent commits recorded in `MERGE_HEAD` for the next merge commit. -/
  mergeParents : List CommitId := []
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Commit object in a repository's shared object database. -/
structure CommitNode where
  /-- Unique commit identifier. -/
  id : CommitId
  /-- Parent commit identifiers (all preceding this commit in topological order). -/
  parents : List CommitId
  /-- Sorted snapshot mapping repo-relative `ByteArray` paths to `GitTreeEntry`. -/
  tree : List (ByteArray × GitTreeEntry) := []
  /-- Commit message. -/
  message : String := ""
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Main or linked worktree slot (`worktrees[0]` is main worktree or bare repo slot). -/
structure WorktreeSlot where
  /-- Canonical (`realpath`) absolute path bytes of the worktree root (or bare repo dir). -/
  rootPath : ByteArray
  /-- Symbolic or detached `HEAD`. -/
  head : SymbolicHead
  /-- Worktree staging index state. -/
  index : IndexState := {}
  /-- Whether the linked worktree is locked. -/
  isLocked : Bool := false
  /-- Optional lock reason string. -/
  lockReason : Option String := none
  /-- Whether the linked worktree is marked prunable. -/
  isPrunable : Bool := false
  /-- Optional prunable reason string. -/
  pruneReason : Option String := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Configured named remote in `.git/config`. -/
structure RemoteEntry where
  /-- Remote name (e.g. `"origin"`). -/
  name : String
  /-- Configured remote URL or local path. -/
  url : String
  /-- Default fetch refspecs configured for this remote. -/
  fetchSpecs : List String := []
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One Git repository's shared `.git` object store, `refs/` hierarchy, remotes, and worktrees. -/
structure RepoInstance where
  /-- Canonical absolute path bytes of common `.git` dir (`<mainRoot>/.git` or `<bareRoot>`). -/
  commonDir : ByteArray
  /-- Whether this repository is bare. -/
  isBare : Bool := false
  /-- Topologically ordered commits (parents precede children). -/
  commits : List CommitNode := []
  /-- Full ref table mapping `"refs/heads/..."`, `"refs/remotes/..."`, `"refs/tags/..."` to `CommitId`. -/
  refs : List (String × CommitId) := []
  /-- Symbolic refs (e.g. `"refs/remotes/origin/HEAD"` -> `"refs/remotes/origin/main"`). -/
  symRefs : List (String × String) := []
  /-- Configured remotes. -/
  remotes : List RemoteEntry := []
  /-- Registered worktrees (`worktrees[0]` is main worktree or bare repo slot). -/
  worktrees : List WorktreeSlot := []
  /-- Configured upstream tracking ref per local branch short name. -/
  branchUpstreams : List (String × String) := []
  /-- Configured `(branch, remote, mergeRef)` tracking entries in `.git/config`. -/
  branchRemotes : List (String × String × String) := []
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Unified pure behavior model state for `LeanSwe.Git`. -/
structure GitRepoState where
  /-- Process working directory used when `cwd = none` (`init`, `clone`). -/
  processCwd : ByteArray := "/".toUTF8
  /-- Root VFS directory (`"/"`). -/
  vfs : VfsNode := VfsNode.emptyDir
  /-- Registered repositories on the modeled filesystem. -/
  repos : List RepoInstance := []
  /-- Modeled process environment returned by `listEnv`. -/
  inheritedEnv : Array (String × String) := #[]
  /-- Default initial branch created by `init` when `initialBranch? = none`. -/
  defaultInitBranch : RefName := { raw := "main" }
  deriving Repr, BEq, Inhabited

/-- Lexicographic unsigned-byte comparison on `ByteArray` (`memcmp` order). -/
def ltBytes (a b : ByteArray) : Bool :=
  go 0 (min a.size b.size)
where
  go (i bound : Nat) : Bool :=
    if h : i < bound then
      let ba := a[i]!
      let bb := b[i]!
      if ba != bb then ba < bb else go (i + 1) bound
    else
      a.size < b.size
  termination_by bound - i

private def mergeKeyedRev {α : Type} :
    Nat → List (ByteArray × α) → List (ByteArray × α) → List (ByteArray × α) → List (ByteArray × α)
  | 0, acc, xs, ys => acc.reverseAux (xs ++ ys)
  | _, acc, [], ys => acc.reverseAux ys
  | _, acc, xs, [] => acc.reverseAux xs
  | f + 1, acc, x :: xs, y :: ys =>
    if ltBytes y.1 x.1 then
      mergeKeyedRev f (y :: acc) (x :: xs) ys
    else
      mergeKeyedRev f (x :: acc) xs (y :: ys)

private def mergePassKeyed {α : Type} (acc : List (List (ByteArray × α))) :
    List (List (ByteArray × α)) → List (List (ByteArray × α))
  | [] => acc.reverse
  | [r] => (r :: acc).reverse
  | r1 :: r2 :: rest =>
    mergePassKeyed (mergeKeyedRev (r1.length + r2.length) [] r1 r2 :: acc) rest

private def mergeAllKeyed {α : Type} : Nat → List (List (ByteArray × α)) → List (ByteArray × α)
  | 0, runs => runs.head?.getD []
  | _, [] => []
  | _, [r] => r
  | fuel + 1, runs => mergeAllKeyed fuel (mergePassKeyed [] runs)

/-- Sort `xs` lexicographically by unsigned `ByteArray` key `key`. -/
def sortByBytes {α : Type} (key : α → ByteArray) (xs : List α) : List α :=
  let runs := (xs.foldl (fun acc x => [(key x, x)] :: acc) []).reverse
  (mergeAllKeyed runs.length runs).map Prod.snd

private def cmpBytes (a b : ByteArray) : Ordering :=
  if ltBytes a b then .lt else if a == b then .eq else .gt

private def dedupSortedByteArraysLoop (acc : List ByteArray) : List ByteArray → List ByteArray
  | [] => acc.reverse
  | [x] => (x :: acc).reverse
  | x :: y :: rest =>
    if x == y then dedupSortedByteArraysLoop acc (y :: rest)
    else dedupSortedByteArraysLoop (x :: acc) (y :: rest)

private def dedupStringsLoop (acc : List String) : List String → List String
  | [] => acc.reverse
  | x :: xs => if acc.contains x then dedupStringsLoop acc xs else dedupStringsLoop (x :: acc) xs

/-- Return `true` iff `p` equals `pfx` or starts with `pfx ++ "/"`. -/
def isPathPrefixBytes (pfx p : ByteArray) : Bool :=
  p == pfx ||
  (p.size > pfx.size &&
   p.extract 0 pfx.size == pfx &&
   p[pfx.size]! == 0x2f)

/-- Strip directory prefix `pfx` from `p`, returning `none` if `p == pfx` or unrelated, or `some rel`. -/
def stripPathPrefixBytes (pfx p : ByteArray) : Option ByteArray :=
  if p.size > pfx.size && p.extract 0 pfx.size == pfx && p[pfx.size]! == 0x2f then
    some (p.extract (pfx.size + 1) p.size)
  else
    none

/-- Split raw `ByteArray` on `'/'` (`0x2f`), dropping empty segments. -/
def splitByteSlash (bs : ByteArray) : List ByteArray :=
  go 0 0 [] |>.reverse
where
  go (start i : Nat) (acc : List ByteArray) : List ByteArray :=
    if h : i < bs.size then
      if bs[i]! == 0x2f then
        let acc' := if i > start then bs.extract start i :: acc else acc
        go (i + 1) (i + 1) acc'
      else
        go start (i + 1) acc
    else
      if i > start then bs.extract start i :: acc else acc
  termination_by bs.size - i

/-- Join canonical absolute path segments with leading `'/'` (`[]` gives `"/"`). -/
def joinAbsByteParts (parts : List ByteArray) : ByteArray :=
  match parts with
  | [] => "/".toUTF8
  | p :: rest =>
    rest.foldl (fun acc seg => (acc.push 0x2f) ++ seg) (ByteArray.empty.push 0x2f ++ p)

/-- Join relative path segments with `'/'`. -/
def joinRelByteParts : List ByteArray → ByteArray
  | [] => ByteArray.empty
  | [p] => p
  | p :: rest => rest.foldl (fun acc seg => (acc.push 0x2f) ++ seg) p

/-- Return the basename segment of a raw `ByteArray` path. -/
def basenameBytes (p : ByteArray) : ByteArray :=
  match (splitByteSlash p).reverse with
  | b :: _ => b
  | [] => p

/-- Join two raw `ByteArray` path segments with `'/'` when both are non-empty. -/
def joinPathsBytes (base rel : ByteArray) : ByteArray :=
  if base.isEmpty then rel
  else if rel.isEmpty then base
  else if base == "/".toUTF8 then ByteArray.empty.push 0x2f ++ rel
  else (base.push 0x2f) ++ rel

private inductive NormPathFilter where
  | allWorktree
  | exactOrDir (rel : ByteArray) (dirOnly : Bool)
  deriving DecidableEq, BEq

private def normalizeSimpleCliPathspec? (wtRootStr : String) (cwdRel? : Option ByteArray)
    (raw : String) : Option NormPathFilter :=
  if !isValidPathArg raw || raw.utf8ByteSize >= 4096 then
    none
  else if raw == "." || raw == "./" then
    match cwdRel? with
    | none => some .allWorktree
    | some pref => some (.exactOrDir pref true)
  else if raw.startsWith "/" then
    if raw == "/" then none
    else
      let cs := raw.toList
      let dirOnly := cs.getLast? == some '/'
      let cleanAbs := String.ofList (if dirOnly then cs.dropLast else cs)
      let segs := (String.ofList (cleanAbs.toList.drop 1)).splitOn "/"
      if cleanAbs.isEmpty || segs.any (fun s => s.isEmpty || s == "." || s == ".." || s == ".git" || s.utf8ByteSize > 255) then
        none
      else if cleanAbs == wtRootStr then
        some .allWorktree
      else if cleanAbs.startsWith (wtRootStr ++ "/") then
        let rel := String.ofList (cleanAbs.toList.drop (wtRootStr.toList.length + 1))
        if rel.isEmpty then some .allWorktree
        else some (.exactOrDir rel.toUTF8 dirOnly)
      else
        none
  else
    let bodyCs := match raw.toList with | '.' :: '/' :: rest => rest | cs => cs
    let body := String.ofList bodyCs
    if body.isEmpty || body == "." then none
    else
      let dirOnly := bodyCs.getLast? == some '/'
      let cleanRel := String.ofList (if dirOnly then bodyCs.dropLast else bodyCs)
      if !isValidRelRepoPath cleanRel then
        none
      else
        let fullRel :=
          match cwdRel? with
          | none => cleanRel.toUTF8
          | some pref => joinPathsBytes pref cleanRel.toUTF8
        some (.exactOrDir fullRel dirOnly)

private def normalizeCliPathspecs? (wtRootStr : String) (cwdRel? : Option ByteArray)
    (paths : Array String) : Option (List (String × NormPathFilter)) :=
  paths.toList.mapM fun p =>
    (normalizeSimpleCliPathspec? wtRootStr cwdRel? p).map (p, ·)

private def matchesNormPathFilter (f : NormPathFilter) (p : ByteArray) : Bool :=
  match f with
  | .allWorktree => true
  | .exactOrDir q false => isPathPrefixBytes q p
  | .exactOrDir q true => (stripPathPrefixBytes q p).isSome

private def matchesAnyNormPathFilter (filters : List NormPathFilter) (p : ByteArray) : Bool :=
  filters.isEmpty || filters.any (matchesNormPathFilter · p)

/-- Look up child entry named `seg` in directory entry list `children`. -/
def lookupDirChild (seg : ByteArray) : List (ByteArray × VfsNode) → Option VfsNode
  | [] => none
  | (k, v) :: rest => if k == seg then some v else lookupDirChild seg rest

private def upsertDirChildLoop (seg : ByteArray) (node : VfsNode) (acc : List (ByteArray × VfsNode)) :
    List (ByteArray × VfsNode) → List (ByteArray × VfsNode)
  | [] => ((seg, node) :: acc).reverse
  | (k, v) :: rest =>
    if k == seg then acc.reverse ++ ((seg, node) :: rest)
    else upsertDirChildLoop seg node ((k, v) :: acc) rest

private def upsertDirChild (seg : ByteArray) (node : VfsNode)
    (cs : List (ByteArray × VfsNode)) : List (ByteArray × VfsNode) :=
  upsertDirChildLoop seg node [] cs

private def eraseDirChildLoop (seg : ByteArray) (acc : List (ByteArray × VfsNode)) :
    List (ByteArray × VfsNode) → List (ByteArray × VfsNode)
  | [] => acc.reverse
  | (k, v) :: rest =>
    if k == seg then acc.reverse ++ rest
    else eraseDirChildLoop seg ((k, v) :: acc) rest

private def eraseDirChild (seg : ByteArray)
    (cs : List (ByteArray × VfsNode)) : List (ByteArray × VfsNode) :=
  eraseDirChildLoop seg [] cs

/-- Look up the `VfsNode` at canonical segment list `parts` from `vfs`. -/
def lookupNodeAtParts (node : VfsNode) : List ByteArray → Option VfsNode
  | [] => some node
  | seg :: rest =>
    match node with
    | .dir _ _ children =>
      match lookupDirChild seg children with
      | some child => lookupNodeAtParts child rest
      | none => none
    | _ => none

private def updateNodeAscend (updated : VfsNode) :
    List (ByteArray × Bool × Bool × List (ByteArray × VfsNode)) → VfsNode
  | [] => updated
  | (seg, s, w, cs) :: rest =>
    updateNodeAscend (.dir s w (upsertDirChild seg updated cs)) rest

private def updateNodeDescend (trail : List (ByteArray × Bool × Bool × List (ByteArray × VfsNode)))
    (f : VfsNode → VfsNode) (node : VfsNode) : List ByteArray → VfsNode
  | [] => updateNodeAscend (f node) trail
  | seg :: rest =>
    match node with
    | .dir s w children =>
      match lookupDirChild seg children with
      | some child => updateNodeDescend ((seg, s, w, children) :: trail) f child rest
      | none => updateNodeAscend node trail
    | _ => updateNodeAscend node trail

/-- Update the `VfsNode` at canonical segment list `parts` via `f`. -/
def updateNodeAtParts (node : VfsNode) (parts : List ByteArray) (f : VfsNode → VfsNode) : VfsNode :=
  updateNodeDescend [] f node parts

private def addChildAtParts (node : VfsNode) (parentParts : List ByteArray)
    (seg : ByteArray) (child : VfsNode) : VfsNode :=
  updateNodeAtParts node parentParts fun
    | .dir s w cs => .dir s w (upsertDirChild seg child cs)
    | other => other

private def removeChildAtParts (node : VfsNode) (parentParts : List ByteArray) (seg : ByteArray) : VfsNode :=
  updateNodeAtParts node parentParts fun
    | .dir s w cs => .dir s w (eraseDirChild seg cs)
    | other => other

/-- POSIX-style VFS traversal error code for pure behavior modeling. -/
inductive VfsErr where
  /-- Missing path component (`ENOENT`). -/
  | enoent
  /-- Non-directory encountered where directory required (`ENOTDIR`). -/
  | enotdir
  /-- Unsearchable or unwritable directory (`EACCES`). -/
  | eacces
  /-- Symlink traversal loop / depth limit (`ELOOP`). -/
  | eloop
  deriving Repr, BEq, DecidableEq

/-- Resolved VFS target node together with canonical absolute path segments. -/
inductive VfsLookupResult where
  /-- Resolved directory node. -/
  | dir (canonParts : List ByteArray) (searchable writable : Bool) (children : List (ByteArray × VfsNode))
  /-- Resolved regular file node. -/
  | file (canonParts : List ByteArray) (executable : Bool) (bytes : ByteArray)
  /-- Resolved symbolic link node (`followLast = false`). -/
  | symlink (canonParts : List ByteArray) (target : ByteArray)
  deriving Repr, BEq

/-- Return `true` iff raw path bytes `bs` start with `'/'` (`0x2f`). -/
def startsWithSlashByte (bs : ByteArray) : Bool :=
  bs.size > 0 && bs[0]! == 0x2f

/-- Resolve path segments `rem` starting from canonical `cur` in `vfs`, bounded by symlink `fuel`. -/
def resolveVfsFuel (fuel : Nat) (vfs : VfsNode) (cur rem : List ByteArray)
    (followLast : Bool := true) : Except VfsErr VfsLookupResult :=
  match fuel with
  | 0 => .error .eloop
  | fuel' + 1 =>
    match rem with
    | [] =>
      match lookupNodeAtParts vfs cur with
      | some (.dir s w cs) => .ok (.dir cur s w cs)
      | some (.file ex b) => .ok (.file cur ex b)
      | some (.symlink t) => .ok (.symlink cur t)
      | none => .error .enoent
    | seg :: rest =>
      match lookupNodeAtParts vfs cur with
      | none => .error .enoent
      | some (.file _ _) | some (.symlink _) => .error .enotdir
      | some (.dir searchable _ children) =>
        if !searchable then
          .error .eacces
        else if seg == ".".toUTF8 then
          resolveVfsFuel (fuel' + 1) vfs cur rest followLast
        else if seg == "..".toUTF8 then
          resolveVfsFuel (fuel' + 1) vfs cur.dropLast rest followLast
        else
          match lookupDirChild seg children with
          | none => .error .enoent
          | some (.dir s w cs) =>
            if rest.isEmpty then .ok (.dir (cur ++ [seg]) s w cs)
            else resolveVfsFuel (fuel' + 1) vfs (cur ++ [seg]) rest followLast
          | some (.file ex b) =>
            if rest.isEmpty then .ok (.file (cur ++ [seg]) ex b)
            else .error .enotdir
          | some (.symlink target) =>
            if rest.isEmpty && !followLast then
              .ok (.symlink (cur ++ [seg]) target)
            else
              let targetParts := splitByteSlash target
              let baseCur := if startsWithSlashByte target then [] else cur
              resolveVfsFuel fuel' vfs baseCur (targetParts ++ rest) followLast
  termination_by (fuel, rem.length)

/-- Resolve a directory path in `s.vfs` relative to `s.processCwd`, mapping VFS failures to `.commandFailed`. -/
def resolveDirInVfs (s : GitRepoState) (pathStr : String) : Except GitError (List ByteArray) :=
  let pathBytes := pathStr.toUTF8
  let cwdParts := if startsWithSlashByte pathBytes then [] else splitByteSlash s.processCwd
  match resolveVfsFuel 41 s.vfs cwdParts (splitByteSlash pathBytes) true with
  | .ok (.dir canonParts searchable _ _) =>
    if searchable then .ok canonParts
    else .error { kind := .commandFailed, message := s!"permission denied: '{pathStr}'" }
  | .ok _ => .error { kind := .commandFailed, message := s!"not a directory: '{pathStr}'" }
  | .error .enoent => .error { kind := .commandFailed, message := s!"no such file or directory: '{pathStr}'" }
  | .error .enotdir => .error { kind := .commandFailed, message := s!"not a directory: '{pathStr}'" }
  | .error .eacces => .error { kind := .commandFailed, message := s!"permission denied: '{pathStr}'" }
  | .error .eloop => .error { kind := .invalidInput, message := s!"too many levels of symbolic links: '{pathStr}'" }

/-- Return `true` iff `parts` resolves to an existing directory node in `vfs`. -/
def isLiveDirAtParts (vfs : VfsNode) (parts : List ByteArray) : Bool :=
  match lookupNodeAtParts vfs parts with
  | some (.dir _ _ _) => true
  | _ => false

private def hasLinkedGitFileAtParts (vfs : VfsNode) (parts : List ByteArray) : Bool :=
  match lookupNodeAtParts vfs (parts ++ [".git".toUTF8]) with
  | some (.file _ _) => true
  | _ => false

private def isSearchableDirAtParts (vfs : VfsNode) (parts : List ByteArray) : Bool :=
  match resolveVfsFuel 41 vfs [] parts true with
  | .ok (.dir _ true _ _) => true
  | _ => false

private def isDirEmptyAtParts (vfs : VfsNode) (parts : List ByteArray) : Bool :=
  match lookupNodeAtParts vfs parts with
  | some (.dir _ _ cs) => cs.isEmpty
  | _ => false

/-- Create missing directory segments along `rem` from `cur`, bounded by symlink `fuel`. -/
def mkdirPVfsFuel (fuel : Nat) (vfs : VfsNode) (cur rem : List ByteArray) :
    Except GitError (VfsNode × List ByteArray) :=
  match fuel with
  | 0 => .error { kind := .commandFailed, message := "too many levels of symbolic links" }
  | fuel' + 1 =>
    match rem with
    | [] =>
      match lookupNodeAtParts vfs cur with
      | some (.dir s _ _) =>
        if s then .ok (vfs, cur)
        else .error { kind := .commandFailed, message := "permission denied" }
      | _ => .error { kind := .commandFailed, message := "not a directory" }
    | seg :: rest =>
      match lookupNodeAtParts vfs cur with
      | none => .error { kind := .commandFailed, message := "parent directory missing" }
      | some (.file _ _) | some (.symlink _) => .error { kind := .commandFailed, message := "not a directory" }
      | some (.dir searchable writable cs) =>
        if !searchable then
          .error { kind := .commandFailed, message := "permission denied" }
        else if seg == ".".toUTF8 then
          mkdirPVfsFuel (fuel' + 1) vfs cur rest
        else if seg == "..".toUTF8 then
          mkdirPVfsFuel (fuel' + 1) vfs cur.dropLast rest
        else
          match lookupDirChild seg cs with
          | none =>
            if !writable then
              .error { kind := .commandFailed, message := "permission denied" }
            else
              let vfs' := addChildAtParts vfs cur seg (.dir true true [])
              mkdirPVfsFuel (fuel' + 1) vfs' (cur ++ [seg]) rest
          | some (.dir s _ _) =>
            if !s then .error { kind := .commandFailed, message := "permission denied" }
            else mkdirPVfsFuel (fuel' + 1) vfs (cur ++ [seg]) rest
          | some (.file _ _) => .error { kind := .commandFailed, message := "file exists" }
          | some (.symlink _) =>
            match resolveVfsFuel fuel' vfs cur [seg] true with
            | .ok (.dir canonT sT _ _) =>
              if !sT then .error { kind := .commandFailed, message := "permission denied" }
              else mkdirPVfsFuel fuel' vfs canonT rest
            | .error .eacces => .error { kind := .commandFailed, message := "permission denied" }
            | .error .eloop => .error { kind := .invalidInput, message := "too many levels of symbolic links" }
            | .error .enoent =>
              if rest.isEmpty then .error { kind := .commandFailed, message := "file exists" }
              else .error { kind := .notFound, message := "no such file or directory" }
            | _ => .error { kind := .commandFailed, message := "file exists" }
  termination_by (fuel, rem.length)

private def isVfsChainWritable (vfs : VfsNode) (rootParts relDirParts : List ByteArray) : Bool :=
  let rec go (node : VfsNode) : List ByteArray → Bool
    | [] =>
      match node with
      | .dir s w _ => s && w
      | _ => false
    | seg :: rest =>
      match node with
      | .dir s w cs =>
        if !s then false
        else
          match lookupDirChild seg cs with
          | some (child@(.dir _ _ _)) => go child rest
          | _ => w
      | _ => false
  match lookupNodeAtParts vfs rootParts with
  | some rootNode => go rootNode relDirParts
  | none => false

private def pruneEmptyParentsRev (vfs : VfsNode) (rootLen : Nat) : List ByteArray → VfsNode
  | [] => vfs
  | leaf :: revParent =>
    let parts := (leaf :: revParent).reverse
    if parts.length <= rootLen then vfs
    else if isDirEmptyAtParts vfs parts then
      pruneEmptyParentsRev (removeChildAtParts vfs revParent.reverse leaf) rootLen revParent
    else
      vfs

private def removeEntryAndPruneVfs (vfs : VfsNode) (rootParts relParts : List ByteArray)
    (preserveNonEmptyDir : Bool := false) : VfsNode :=
  if preserveNonEmptyDir then
    match lookupNodeAtParts vfs (rootParts ++ relParts) with
    | some (.dir _ _ (_ :: _)) => vfs
    | _ =>
      match relParts.reverse with
      | [] => vfs
      | leaf :: revParent =>
        let revParentAbs := revParent ++ rootParts.reverse
        let v' := removeChildAtParts vfs revParentAbs.reverse leaf
        pruneEmptyParentsRev v' rootParts.length revParentAbs
  else
    match relParts.reverse with
    | [] => vfs
    | leaf :: revParent =>
      let revParentAbs := revParent ++ rootParts.reverse
      let v' := removeChildAtParts vfs revParentAbs.reverse leaf
      pruneEmptyParentsRev v' rootParts.length revParentAbs

private def removeEntryAndPruneVfsChecked (vfs : VfsNode) (rootParts relParts : List ByteArray)
    (preserveNonEmptyDir : Bool := false) : VfsNode × Bool :=
  match relParts.reverse with
  | [] => (vfs, false)
  | _ :: revParent =>
    let dirParts := revParent.reverse
    match lookupNodeAtParts vfs (rootParts ++ relParts) with
    | none => (vfs, false)
    | some (.dir _ _ (_ :: _)) =>
      if preserveNonEmptyDir then (vfs, false)
      else if !isVfsChainWritable vfs rootParts dirParts then (vfs, true)
      else (removeEntryAndPruneVfs vfs rootParts relParts preserveNonEmptyDir, false)
    | some _ =>
      if !isVfsChainWritable vfs rootParts dirParts then (vfs, true)
      else (removeEntryAndPruneVfs vfs rootParts relParts preserveNonEmptyDir, false)

private noncomputable def vfsStackWeight : List VfsNode → Nat
  | [] => 0
  | n :: ns => sizeOf n + vfsStackWeight ns

private noncomputable def pushDirChildrenRev (acc : List VfsNode) : List (ByteArray × VfsNode) → List VfsNode
  | [] => acc
  | (_, c) :: rest => pushDirChildrenRev (c :: acc) rest

private theorem vfsStackWeight_pushDirChildrenRev (acc : List VfsNode) (cs : List (ByteArray × VfsNode)) :
    vfsStackWeight (pushDirChildrenRev acc cs) ≤ vfsStackWeight acc + sizeOf cs := by
  induction cs generalizing acc with
  | nil => simp [pushDirChildrenRev]
  | cons hd tl ih =>
    rcases hd with ⟨k, c⟩
    simp only [pushDirChildrenRev]
    have h1 := ih (c :: acc)
    have hSz : sizeOf ((k, c) :: tl) = 1 + (1 + sizeOf k + sizeOf c) + sizeOf tl := rfl
    have hW : vfsStackWeight (c :: acc) = sizeOf c + vfsStackWeight acc := rfl
    omega

private theorem sizeOf_vfsDir_gt (s w : Bool) (cs : List (ByteArray × VfsNode)) :
    sizeOf cs < sizeOf (VfsNode.dir s w cs) := by
  simp only [VfsNode.dir.sizeOf_spec]
  omega

private theorem sizeOf_vfsFile_pos (ex : Bool) (bs : ByteArray) :
    0 < sizeOf (VfsNode.file ex bs) := by
  simp only [VfsNode.file.sizeOf_spec]
  omega

private theorem sizeOf_vfsSymlink_pos (t : ByteArray) :
    0 < sizeOf (VfsNode.symlink t) := by
  simp only [VfsNode.symlink.sizeOf_spec]
  omega

private def pushDirChildrenRuntime (acc : List VfsNode) : List (ByteArray × VfsNode) → List VfsNode
  | [] => acc
  | (_, c) :: rest => pushDirChildrenRuntime (c :: acc) rest

private theorem pushDirChildrenRuntime_eq (acc : List VfsNode) (cs : List (ByteArray × VfsNode)) :
    pushDirChildrenRuntime acc cs = pushDirChildrenRev acc cs := by
  induction cs generalizing acc with
  | nil => rfl
  | cons hd tl ih => simp [pushDirChildrenRuntime, pushDirChildrenRev, ih]

private def vfsNodeCountLoop (acc : Nat) : List VfsNode → Nat
  | [] => acc
  | .file ex bs :: stack => vfsNodeCountLoop (acc + 1) stack
  | .symlink t :: stack => vfsNodeCountLoop (acc + 1) stack
  | .dir s w cs :: stack => vfsNodeCountLoop (acc + 1) (pushDirChildrenRuntime stack cs)
termination_by stack => vfsStackWeight stack
decreasing_by
  · have hPos := sizeOf_vfsFile_pos ex bs
    simp only [vfsStackWeight]
    omega
  · have hPos := sizeOf_vfsSymlink_pos t
    simp only [vfsStackWeight]
    omega
  · have hPush := vfsStackWeight_pushDirChildrenRev stack cs
    have hDir := sizeOf_vfsDir_gt s w cs
    rw [pushDirChildrenRuntime_eq]
    simp only [vfsStackWeight]
    omega

private def vfsNodeCount (node : VfsNode) : Nat :=
  vfsNodeCountLoop 0 [node]

private structure RmDirFrame where
  name : ByteArray
  searchable : Bool
  writable : Bool
  rem : List (ByteArray × VfsNode)
  keptRev : List (ByteArray × VfsNode)
  errAcc : Bool

private def removeDirNodeLoop : Nat → List RmDirFrame → Bool × Option VfsNode
  | 0, _ | _, [] => (false, none)
  | f + 1, { name := dName, searchable := ds, writable := dw, rem := [], keptRev, errAcc } :: parentStack =>
    let res? : Option VfsNode :=
      if keptRev.isEmpty then none else some (.dir ds dw keptRev.reverse)
    let hadErr := errAcc || res?.isSome
    match parentStack with
    | [] => (hadErr, res?)
    | p :: prest =>
      let p' :=
        match res? with
        | none => { p with errAcc := p.errAcc || hadErr }
        | some remNode => { p with errAcc := true, keptRev := (dName, remNode) :: p.keptRev }
      removeDirNodeLoop f (p' :: prest)
  | f + 1, { name := dName, searchable := ds, writable := dw, rem := (cName, cNode) :: rest, keptRev, errAcc } :: stack =>
    match cNode with
    | .dir cs cw cChildren =>
      if cChildren.isEmpty then
        removeDirNodeLoop f ({ name := dName, searchable := ds, writable := dw, rem := rest, keptRev, errAcc } :: stack)
      else if !cs || !cw then
        removeDirNodeLoop f ({ name := dName, searchable := ds, writable := dw, rem := rest, keptRev := (cName, cNode) :: keptRev, errAcc := true } :: stack)
      else
        let suspended : RmDirFrame := { name := dName, searchable := ds, writable := dw, rem := rest, keptRev, errAcc }
        let childFrame : RmDirFrame := { name := cName, searchable := cs, writable := cw, rem := cChildren, keptRev := [], errAcc := false }
        removeDirNodeLoop f (childFrame :: suspended :: stack)
    | _ =>
      removeDirNodeLoop f ({ name := dName, searchable := ds, writable := dw, rem := rest, keptRev, errAcc } :: stack)

private def removeDirNodeChecked (node : VfsNode) : Bool × Option VfsNode :=
  match node with
  | .dir s w cs =>
    if cs.isEmpty then (false, none)
    else if !s || !w then (true, some (.dir s w cs))
    else
      let fuel := 2 * vfsNodeCount node + 4
      removeDirNodeLoop fuel [{ name := ByteArray.empty, searchable := s, writable := w, rem := cs, keptRev := [], errAcc := false }]
  | other => (false, some other)

private def lookupNodeChecked (node : VfsNode) : List ByteArray → Except VfsErr VfsNode
  | [] => .ok node
  | seg :: rest =>
    match node with
    | .dir searchable _ children =>
      if !searchable then .error .eacces
      else
        match lookupDirChild seg children with
        | some child => lookupNodeChecked child rest
        | none => .error .enoent
    | _ => .error .enotdir

private def hasSymlinkAncestorInVfs (vfs : VfsNode) (rootParts relParts : List ByteArray) : Bool :=
  match lookupNodeAtParts vfs rootParts with
  | none => false
  | some rootNode => go rootNode relParts
where
  go (node : VfsNode) : List ByteArray → Bool
    | [] | [_] => false
    | seg :: rest =>
      match node with
      | .dir searchable _ cs =>
        if !searchable then false
        else
          match lookupDirChild seg cs with
          | some (.symlink _) => true
          | some child => go child rest
          | none => false
      | _ => false

private def hasAnyFileUnderLoop : List VfsNode → Bool
  | [] => false
  | .file _ _ :: _ | .symlink _ :: _ => true
  | .dir searchable _ cs :: stack =>
    if !searchable then hasAnyFileUnderLoop stack
    else if cs.any (fun p => p.1 == ".git".toUTF8) then true
    else hasAnyFileUnderLoop (pushDirChildrenRuntime stack cs)
termination_by stack => vfsStackWeight stack
decreasing_by
  · simp only [vfsStackWeight, VfsNode.dir.sizeOf_spec]
    omega
  · have hPush := vfsStackWeight_pushDirChildrenRev stack cs
    rw [pushDirChildrenRuntime_eq]
    simp only [vfsStackWeight, VfsNode.dir.sizeOf_spec]
    omega

private def hasAnyFileUnderNode (node : VfsNode) : Bool :=
  hasAnyFileUnderLoop [node]

private def dirSubtreeRemovableLoop : List VfsNode → Bool
  | [] => true
  | .file _ _ :: stack => dirSubtreeRemovableLoop stack
  | .symlink _ :: stack => dirSubtreeRemovableLoop stack
  | .dir searchable writable cs :: stack =>
    if !searchable then false
    else if !writable && !cs.isEmpty then false
    else dirSubtreeRemovableLoop (pushDirChildrenRuntime stack cs)
termination_by stack => vfsStackWeight stack
decreasing_by
  · simp only [vfsStackWeight, VfsNode.file.sizeOf_spec]
    omega
  · simp only [vfsStackWeight, VfsNode.symlink.sizeOf_spec]
    omega
  · have hPush := vfsStackWeight_pushDirChildrenRev stack cs
    rw [pushDirChildrenRuntime_eq]
    simp only [vfsStackWeight, VfsNode.dir.sizeOf_spec]
    omega

private def dirTreeCanBeRemovedChecked (vfs : VfsNode) (rootParts relParts : List ByteArray) : Bool :=
  match lookupNodeAtParts vfs (rootParts ++ relParts) with
  | some (d@(.dir _ _ _)) => dirSubtreeRemovableLoop [d]
  | _ => true

private def isNestedGitDir (child : VfsNode) : Bool :=
  match child with
  | .dir searchable _ cs => searchable && (lookupDirChild ".git".toUTF8 cs).isSome
  | _ => false

private noncomputable def vfsTaggedStackWeight : List (Bool × VfsNode) → Nat
  | [] => 0
  | (_, n) :: rest => sizeOf n + vfsTaggedStackWeight rest

private def pushOwnWorktreeChildrenRev (isRoot : Bool) (acc : List (Bool × VfsNode)) :
    List (ByteArray × VfsNode) → List (Bool × VfsNode)
  | [] => acc
  | (name, c) :: rest =>
    if (isRoot && name == ".git".toUTF8) || (!isRoot && isNestedGitDir c) then
      pushOwnWorktreeChildrenRev isRoot acc rest
    else
      pushOwnWorktreeChildrenRev isRoot ((false, c) :: acc) rest

private theorem vfsTaggedStackWeight_pushOwn
    (isRoot : Bool) (acc : List (Bool × VfsNode)) (cs : List (ByteArray × VfsNode)) :
    vfsTaggedStackWeight (pushOwnWorktreeChildrenRev isRoot acc cs) ≤
      vfsTaggedStackWeight acc + sizeOf cs := by
  induction cs generalizing acc with
  | nil => simp [pushOwnWorktreeChildrenRev]
  | cons hd tl ih =>
    rcases hd with ⟨name, c⟩
    simp only [pushOwnWorktreeChildrenRev]
    split
    · have h1 := ih acc
      have hSz : sizeOf ((name, c) :: tl) = 1 + (1 + sizeOf name + sizeOf c) + sizeOf tl := rfl
      omega
    · have h1 := ih ((false, c) :: acc)
      have hSz : sizeOf ((name, c) :: tl) = 1 + (1 + sizeOf name + sizeOf c) + sizeOf tl := rfl
      have hW : vfsTaggedStackWeight ((false, c) :: acc) = sizeOf c + vfsTaggedStackWeight acc := rfl
      omega

private def vfsOwnNodeCountLoop (acc : Nat) : List (Bool × VfsNode) → Nat
  | [] => acc
  | (_, .file ex bs) :: stack => vfsOwnNodeCountLoop (acc + 1) stack
  | (_, .symlink t) :: stack => vfsOwnNodeCountLoop (acc + 1) stack
  | (isRoot, .dir s w cs) :: stack =>
    if !s then vfsOwnNodeCountLoop (acc + 1) stack
    else vfsOwnNodeCountLoop (acc + 1) (pushOwnWorktreeChildrenRev isRoot stack cs)
termination_by stack => vfsTaggedStackWeight stack
decreasing_by
  · have hPos := sizeOf_vfsFile_pos ex bs
    simp only [vfsTaggedStackWeight]
    omega
  · have hPos := sizeOf_vfsSymlink_pos t
    simp only [vfsTaggedStackWeight]
    omega
  · have hDir := sizeOf_vfsDir_gt s w cs
    simp only [vfsTaggedStackWeight]
    omega
  · have hPush := vfsTaggedStackWeight_pushOwn isRoot stack cs
    have hDir := sizeOf_vfsDir_gt s w cs
    simp only [vfsTaggedStackWeight]
    omega

private def vfsOwnNodeCount (node : VfsNode) : Nat :=
  vfsOwnNodeCountLoop 0 [(true, node)]

private def collectVfsFilesLoop (skipGit : Bool) :
    Nat → List (ByteArray × GitTreeEntry) → List (List ByteArray × VfsNode) → List (ByteArray × GitTreeEntry)
  | 0, acc, _ | _, acc, [] => acc.reverse
  | f + 1, acc, (revPref, .file ex bs) :: stack =>
    let acc' :=
      if revPref.isEmpty then acc else (joinRelByteParts revPref.reverse, { kind := .regular ex, bytes := bs }) :: acc
    collectVfsFilesLoop skipGit f acc' stack
  | f + 1, acc, (revPref, .symlink target) :: stack =>
    let acc' :=
      if revPref.isEmpty then acc else (joinRelByteParts revPref.reverse, { kind := .symlink, bytes := target }) :: acc
    collectVfsFilesLoop skipGit f acc' stack
  | f + 1, acc, (revPref, .dir searchable _ cs) :: stack =>
    if !searchable then
      collectVfsFilesLoop skipGit f acc stack
    else
      let revChildren := cs.foldl (fun st (name, child) =>
        if skipGit && revPref.isEmpty && name == ".git".toUTF8 then st
        else if skipGit && isNestedGitDir child then st
        else (name :: revPref, child) :: st) []
      let stack' := revChildren.foldl (fun s item => item :: s) stack
      collectVfsFilesLoop skipGit f acc stack'

private def noSpecialDirsUnderLoop : Nat → List (Bool × VfsNode) → Bool
  | 0, _ | _, [] => true
  | f + 1, (_, .file _ _) :: stack | f + 1, (_, .symlink _) :: stack =>
    noSpecialDirsUnderLoop f stack
  | f + 1, (isRoot, .dir searchable _ cs) :: stack =>
    if !searchable then false
    else if !isRoot && (lookupDirChild ".git".toUTF8 cs).isSome then false
    else
      let stack' := cs.foldl (fun st (name, child) =>
        if isRoot && name == ".git".toUTF8 then st else (false, child) :: st) stack
      noSpecialDirsUnderLoop f stack'

private def noSpecialDirsUnderNode (node : VfsNode) : Bool :=
  noSpecialDirsUnderLoop (vfsOwnNodeCount node + 2) [(true, node)]

private def hasNamedFileUnderLoop (target : ByteArray) : Nat → List (Bool × VfsNode) → Bool
  | 0, _ | _, [] => false
  | f + 1, (_, .file _ _) :: stack | f + 1, (_, .symlink _) :: stack =>
    hasNamedFileUnderLoop target f stack
  | f + 1, (isRoot, .dir searchable _ cs) :: stack =>
    if !searchable then
      hasNamedFileUnderLoop target f stack
    else
      let hitHere := cs.any fun (name, child) =>
        name == target && match child with | .file _ _ => true | _ => false
      if hitHere then true
      else
        let stack' := cs.foldl (fun st (name, child) =>
          if (isRoot && name == ".git".toUTF8) || (!isRoot && isNestedGitDir child) then st
          else (false, child) :: st) stack
        hasNamedFileUnderLoop target f stack'

private def hasNamedFileUnderNode (target : ByteArray) (node : VfsNode) : Bool :=
  hasNamedFileUnderLoop target (vfsOwnNodeCount node + 1) [(true, node)]

private def hasNestedGitUnderLoop : Nat → List (Bool × VfsNode) → Bool
  | 0, _ | _, [] => false
  | f + 1, (_, .file _ _) :: stack | f + 1, (_, .symlink _) :: stack =>
    hasNestedGitUnderLoop f stack
  | f + 1, (isRoot, .dir searchable _ cs) :: stack =>
    if !searchable then
      hasNestedGitUnderLoop f stack
    else if !isRoot && (lookupDirChild ".git".toUTF8 cs).isSome then
      true
    else
      let stack' := cs.foldl (fun st (name, child) =>
        if isRoot && name == ".git".toUTF8 then st else (false, child) :: st) stack
      hasNestedGitUnderLoop f stack'

private def hasNestedGitUnderNode (node : VfsNode) : Bool :=
  hasNestedGitUnderLoop (vfsOwnNodeCount node + 2) [(true, node)]

private def collectVfsFilesUnderNode (node : VfsNode) : List (ByteArray × GitTreeEntry) :=
  sortByBytes (·.1) (collectVfsFilesLoop true (vfsOwnNodeCount node + 1) [] [([], node)])

private def collectVfsFilesUnder (vfs : VfsNode) (rootParts : List ByteArray) :
    List (ByteArray × GitTreeEntry) :=
  match lookupNodeAtParts vfs rootParts with
  | some node => collectVfsFilesUnderNode node
  | none => []

private def lookupVfsRelEntryChecked (vfs : VfsNode) (rootParts : List ByteArray)
    (relPath : ByteArray) : Except VfsErr (Option GitTreeEntry) :=
  match lookupNodeAtParts vfs rootParts with
  | none => .ok none
  | some rootNode =>
    match lookupNodeChecked rootNode (splitByteSlash relPath) with
    | .ok (.file ex bs) => .ok (some { kind := .regular ex, bytes := bs })
    | .ok (.symlink t) => .ok (some { kind := .symlink, bytes := t })
    | .ok (.dir _ _ _) => .ok none
    | .error .eacces => .error .eacces
    | .error _ => .ok none

private def lookupVfsRelEntry (vfs : VfsNode) (rootParts : List ByteArray)
    (relPath : ByteArray) : Option GitTreeEntry :=
  match lookupVfsRelEntryChecked vfs rootParts relPath with
  | .ok opt => opt
  | .error _ => none

private def existsVfsRelAny (vfs : VfsNode) (rootParts : List ByteArray) (relPath : ByteArray) : Bool :=
  match lookupNodeAtParts vfs rootParts with
  | none => false
  | some rootNode =>
    match lookupNodeChecked rootNode (splitByteSlash relPath) with
    | .ok _ => true
    | .error _ => false

private def existsVfsRelDir (vfs : VfsNode) (rootParts : List ByteArray) (relPath : ByteArray) : Bool :=
  match lookupNodeAtParts vfs rootParts with
  | none => false
  | some rootNode =>
    match lookupNodeChecked rootNode (splitByteSlash relPath) with
    | .ok (.dir _ _ _) => true
    | _ => false

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

/-- Return `true` iff commit `id` exists in `repo.commits`. -/
def hasCommit (repo : RepoInstance) (id : CommitId) : Bool :=
  repo.commits.any (fun c => c.id == id)

/-- Look up the tree of commit `id` in `repo.commits`, or `[]` if absent. -/
def treeOfCommit (repo : RepoInstance) (id : CommitId) : List (ByteArray × GitTreeEntry) :=
  match repo.commits.find? (fun c => c.id == id) with
  | some c => c.tree
  | none => []

/-- Look up a full ref name (`"refs/..."`) in `repo.refs` (following `symRefs`). -/
def lookupFullRef (repo : RepoInstance) (fullRef : String) : Option CommitId :=
  match repo.refs.find? (fun p => p.1 == fullRef) with
  | some (_, cid) => some cid
  | none =>
    match repo.symRefs.find? (fun p => p.1 == fullRef) with
    | some (_, target) => (repo.refs.find? (fun p => p.1 == target)).map (·.2)
    | none => none

/-- Look up `"refs/heads/" ++ branch.raw` in `repo.refs`. -/
def findBranchCommit? (repo : RepoInstance) (branch : RefName) : Option CommitId :=
  lookupFullRef repo ("refs/heads/" ++ branch.raw)

/-- Resolve the current commit ID of `SymbolicHead` in `repo`. -/
def headCommitOfSymbolic (repo : RepoInstance) : SymbolicHead → Option CommitId
  | .symbolic b => findBranchCommit? repo b
  | .detached cid => some cid

/-- Convert a `SymbolicHead` in `repo` to public `HeadState`. -/
def toPublicHeadState (repo : RepoInstance) : SymbolicHead → HeadState
  | .symbolic b => .attached b (findBranchCommit? repo b)
  | .detached cid => .detached cid

/-- Return `true` iff `branch` is attached in any worktree of `repo` other than `wtRoot`. -/
def isBranchInUseElsewhere (repo : RepoInstance) (wtRoot : ByteArray) (branch : RefName) : Bool :=
  let slots := if repo.isBare then repo.worktrees.drop 1 else repo.worktrees
  slots.any fun w =>
    w.rootPath != wtRoot &&
    match w.head with
    | .symbolic wb => wb == branch
    | .detached _ => false

/-- Return `true` iff `branch` is attached in any worktree of `repo`. -/
def isBranchCheckedOutAnywhere (repo : RepoInstance) (branch : RefName) : Bool :=
  let slots := if repo.isBare then repo.worktrees.drop 1 else repo.worktrees
  slots.any fun w =>
    match w.head with
    | .symbolic wb => wb == branch
    | .detached _ => false

/-- Return `true` iff `repo` is well-formed (topological DAG, valid refs, non-empty worktrees). -/
def isValidRepoInstance (repo : RepoInstance) : Bool :=
  validCommitDagAux [] repo.commits &&
  allDistinct (repo.refs.map (·.1)) &&
  repo.refs.all (fun rc => hasCommit repo rc.2) &&
  !repo.worktrees.isEmpty &&
  allDistinct (repo.worktrees.map (·.rootPath)) &&
  repo.worktrees.all fun w =>
    match w.head with
    | .detached c => hasCommit repo c
    | .symbolic b =>
      match findBranchCommit? repo b with
      | some c => hasCommit repo c
      | none => true

/-- Return `true` iff all repositories in `s` satisfy `isValidRepoInstance`. -/
def isValidGitRepoState (s : GitRepoState) : Bool :=
  s.repos.all isValidRepoInstance

/-- Propositional well-formedness invariant on `GitRepoState`. -/
def ValidGitRepoState (s : GitRepoState) : Prop :=
  isValidGitRepoState s = true

/-- Return direct parent commit IDs of `id` in `repo`, or `[]` if absent. -/
def parentsOf (repo : RepoInstance) (id : CommitId) : List CommitId :=
  match repo.commits.find? (fun c => c.id == id) with
  | some c => c.parents
  | none => []

/-- Tail-recursive BFS collecting ancestors starting from `frontier` with `visited` invariant. -/
def bfsAncestorsLoop (repo : RepoInstance) : Nat → List CommitId → List CommitId → List CommitId
  | 0, _, visited => visited
  | n + 1, frontier, visited =>
    if frontier.isEmpty then visited
    else
      let next := frontier.foldl (fun acc cid =>
        (parentsOf repo cid).foldl (fun acc2 p =>
          if hasCommit repo p && !visited.contains p && !acc2.contains p then p :: acc2
          else acc2) acc) []
      let visited' := next.foldl (fun v x => x :: v) visited
      bfsAncestorsLoop repo n next visited'

/-- Build a raw map from commit hex string to parent commit IDs (preserving first-entry semantics of `List.find?`). -/
def buildCommitParentsMap (commits : List CommitNode) : Std.TreeMap.Raw String (List CommitId) compare :=
  commits.foldl (fun m c => if m.contains c.id.hex then m else m.insert c.id.hex c.parents) .empty

/-- Fast `O((V + E) log V)` tail-recursive BFS collecting ancestors in the exact same order as `bfsAncestorsLoop`. -/
def bfsAncestorsFastLoop (pMap : Std.TreeMap.Raw String (List CommitId) compare) :
    Nat → List CommitId → List CommitId → Std.TreeSet.Raw String compare → List CommitId
  | 0, _, visited, _ => visited
  | n + 1, frontier, visited, visSet =>
    if frontier.isEmpty then visited
    else
      let (next, visSet') := frontier.foldl (fun (acc, vs) cid =>
        (pMap.getD cid.hex []).foldl (fun (acc2, vs2) p =>
          if pMap.contains p.hex && !vs2.contains p.hex then
            (p :: acc2, vs2.insert p.hex)
          else
            (acc2, vs2)) (acc, vs)) ([], visSet)
      let visited' := next.foldl (fun v x => x :: v) visited
      bfsAncestorsFastLoop pMap n next visited' visSet'

/-- Fast `O((V + E) log V)` BFS equivalent to `bfsAncestorsLoop repo n roots roots`. -/
def bfsAncestorsFast (repo : RepoInstance) (n : Nat) (roots : List CommitId) : List CommitId :=
  let pMap := buildCommitParentsMap repo.commits
  let initSet := roots.foldl (fun s c => s.insert c.hex) (Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare)
  bfsAncestorsFastLoop pMap n roots roots initSet

/-- Return `true` iff `a` and `b` exist in `repo` and `a` is an ancestor of `b` (reflexive). -/
def isAncestor (repo : RepoInstance) (a b : CommitId) : Bool :=
  if repo.commits.length ≤ 16 then
    hasCommit repo a && hasCommit repo b &&
    (a == b || (bfsAncestorsLoop repo repo.commits.length [b] [b]).contains a)
  else
    let pMap := buildCommitParentsMap repo.commits
    pMap.contains a.hex && pMap.contains b.hex &&
    (a == b || (bfsAncestorsFastLoop pMap repo.commits.length [b] [b]
      ((Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare).insert b.hex)).contains a)

/-- Return all commits reachable from `root` (including `root` itself when present). -/
def reachableCommits (repo : RepoInstance) (root : CommitId) : List CommitId :=
  if repo.commits.length ≤ 16 then
    if hasCommit repo root then
      bfsAncestorsLoop repo repo.commits.length [root] [root]
    else
      []
  else
    let pMap := buildCommitParentsMap repo.commits
    if pMap.contains root.hex then
      bfsAncestorsFastLoop pMap repo.commits.length [root] [root]
        ((Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare).insert root.hex)
    else
      []

private def reachableCommitHexSet (repo : RepoInstance) (roots : List CommitId) :
    Std.TreeSet.Raw String compare :=
  let pMap := buildCommitParentsMap repo.commits
  let (uniqRootsRev, initSet) := roots.foldl
    (fun (acc, vs) r =>
      if pMap.contains r.hex && !vs.contains r.hex then
        (r :: acc, vs.insert r.hex)
      else
        (acc, vs))
    ([], (Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare))
  if uniqRootsRev.isEmpty then
    .empty
  else
    let startRoots := uniqRootsRev.reverse
    let reached := bfsAncestorsFastLoop pMap repo.commits.length startRoots startRoots initSet
    reached.foldl (fun st c => st.insert c.hex) (Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare)

/-- Return all commits in `repo` that are ancestors of both `a` and `b`. -/
def commonAncestors (repo : RepoInstance) (a b : CommitId) : List CommitId :=
  if repo.commits.length ≤ 16 then
    if !hasCommit repo a || !hasCommit repo b then []
    else
      let reachA := bfsAncestorsLoop repo repo.commits.length [a] [a]
      let reachB := bfsAncestorsLoop repo repo.commits.length [b] [b]
      reachA.filter (fun c => reachB.contains c)
  else
    let pMap := buildCommitParentsMap repo.commits
    if !pMap.contains a.hex || !pMap.contains b.hex then []
    else
      let reachA := bfsAncestorsFastLoop pMap repo.commits.length [a] [a]
        ((Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare).insert a.hex)
      let reachB := bfsAncestorsFastLoop pMap repo.commits.length [b] [b]
        ((Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare).insert b.hex)
      let reachBSet := reachB.foldl (fun s c => s.insert c.hex) (Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare)
      reachA.filter (fun c => reachBSet.contains c.hex)

/-- Return the lowest (maximal-depth) common ancestors of `a` and `b` in `repo`. -/
def lowestCommonAncestors (repo : RepoInstance) (a b : CommitId) : List CommitId :=
  if repo.commits.length ≤ 16 then
    let ca :=
      if !hasCommit repo a || !hasCommit repo b then []
      else
        let reachA := bfsAncestorsLoop repo repo.commits.length [a] [a]
        let reachB := bfsAncestorsLoop repo repo.commits.length [b] [b]
        reachA.filter (fun c => reachB.contains c)
    let strictStarts := ca.foldl (fun acc d =>
      (parentsOf repo d).foldl (fun acc2 p =>
        if hasCommit repo p && !acc2.contains p then p :: acc2 else acc2) acc) []
    let strictAncs := bfsAncestorsLoop repo repo.commits.length strictStarts strictStarts
    ca.filter (fun c => !strictAncs.contains c)
  else
    let pMap := buildCommitParentsMap repo.commits
    if !pMap.contains a.hex || !pMap.contains b.hex then []
    else
      let reachA := bfsAncestorsFastLoop pMap repo.commits.length [a] [a]
        ((Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare).insert a.hex)
      let reachB := bfsAncestorsFastLoop pMap repo.commits.length [b] [b]
        ((Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare).insert b.hex)
      let reachBSet := reachB.foldl (fun s c => s.insert c.hex) (Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare)
      let ca := reachA.filter (fun c => reachBSet.contains c.hex)
      let (strictStarts, strictSet) := ca.foldl (fun (acc, ss) d =>
        (pMap.getD d.hex []).foldl (fun (acc2, ss2) p =>
          if pMap.contains p.hex && !ss2.contains p.hex then
            (p :: acc2, ss2.insert p.hex)
          else
            (acc2, ss2)) (acc, ss)) ([], (Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare))
      let strictAncs := bfsAncestorsFastLoop pMap repo.commits.length strictStarts strictStarts strictSet
      let strictAncsSet := strictAncs.foldl (fun s c => s.insert c.hex) (Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare)
      ca.filter (fun c => !strictAncsSet.contains c.hex)

/-- Return the lexicographically smallest lowest common ancestor of `a` and `b` in `repo`, if any. -/
def mergeBase? (repo : RepoInstance) (a b : CommitId) : Option CommitId :=
  (lowestCommonAncestors repo a b).foldl
    (fun best c =>
      match best with
      | none => some c
      | some b => if c.hex < b.hex then some c else some b)
    none

/-- Convert a natural number to a lowercase 40-character hexadecimal `CommitId` for deterministic tests. -/
def mkSyntheticCommitId (n : Nat) : CommitId :=
  let rec hexDigits (fuel k : Nat) (acc : List Char) : List Char :=
    match fuel with
    | 0 => acc
    | f + 1 =>
      let d := k % 16
      let ch := if d < 10 then Char.ofNat ('0'.toNat + d) else Char.ofNat ('a'.toNat + (d - 10))
      hexDigits f (k / 16) (ch :: acc)
  { hex := String.ofList (hexDigits 40 n []) }

/-- Search `remaining` candidate synthetic IDs starting at `idx`, falling back to a strictly longer all-zero commit ID not in `repo`. -/
def freshSyntheticCommitIdAux (repo : RepoInstance) (idx : Nat) : Nat → CommitId
  | 0 =>
    let maxLen := repo.commits.foldl (fun m c => Nat.max m c.id.hex.length) 40
    { hex := String.ofList (List.replicate (maxLen + 1) '0') }
  | r + 1 =>
    let cand := mkSyntheticCommitId idx
    if !hasCommit repo cand then cand else freshSyntheticCommitIdAux repo (idx + 1) r

/-- Return a `CommitId` guaranteed not to appear in `repo.commits`. -/
def freshSyntheticCommitId (repo : RepoInstance) : CommitId :=
  freshSyntheticCommitIdAux repo repo.commits.length (repo.commits.length + 1)

/-- Insert or update `name` -> `cid` in a repository ref list. -/
def setRefInList (refs : List (String × CommitId)) (name : String) (cid : CommitId) :
    List (String × CommitId) :=
  if refs.any (fun p => p.1 == name) then
    refs.map (fun p => if p.1 == name then (name, cid) else p)
  else
    refs ++ [(name, cid)]

/-- Remove `name` from a repository ref list. -/
def eraseRefInList (refs : List (String × CommitId)) (name : String) :
    List (String × CommitId) :=
  refs.filter (fun p => p.1 != name)

private def isRefDFConflictPair (a b : String) : Bool :=
  a != b &&
  ((b.startsWith (a ++ "/")) || (a.startsWith (b ++ "/")))

/-- Return `true` iff creating `fullRef` conflicts D/F-wise with any existing ref or symref in `repo`. -/
def hasRefDFConflict (repo : RepoInstance) (fullRef : String) : Bool :=
  repo.refs.any (fun p => isRefDFConflictPair fullRef p.1) ||
  repo.symRefs.any (fun p => isRefDFConflictPair fullRef p.1)

/-- Update the repository matching `commonDir` in `repos` using `f`. -/
def updateRepoInList (repos : List RepoInstance) (commonDir : ByteArray)
    (f : RepoInstance → RepoInstance) : List RepoInstance :=
  repos.map (fun r => if r.commonDir == commonDir then f r else r)

/-- Update the worktree slot matching `wtRoot` in `repo` using `f`. -/
def updateWorktreeInRepo (repo : RepoInstance) (wtRoot : ByteArray)
    (f : WorktreeSlot → WorktreeSlot) : RepoInstance :=
  { repo with worktrees := repo.worktrees.map (fun w => if w.rootPath == wtRoot then f w else w) }

/-- Select the active `WorktreeSlot` (or main/bare slot when invoked inside `.git`). -/
def activeHeadSlot (repo : RepoInstance) (wt? : Option WorktreeSlot) : Option WorktreeSlot :=
  match wt? with
  | some wt => some wt
  | none => repo.worktrees.head?

/-- Discover the enclosing `RepoInstance`, active worktree slot, and relative subdir path at `canonParts`. -/
def discoverRepoAtParts (s : GitRepoState) (canonParts : List ByteArray) :
    Option (RepoInstance × Option WorktreeSlot × Option ByteArray) :=
  let canonPath := joinAbsByteParts canonParts
  go canonParts.reverse canonPath
where
  go (revParts : List ByteArray) (fullCanon : ByteArray) :
      Option (RepoInstance × Option WorktreeSlot × Option ByteArray) :=
    let parts := revParts.reverse
    let curPath := joinAbsByteParts parts
    let found? := s.repos.findSome? fun repo =>
      if repo.commonDir == curPath then
        some (repo, none, none)
      else
        let candidateWts := if repo.isBare then repo.worktrees.drop 1 else repo.worktrees
        match candidateWts.find? (fun w =>
          w.rootPath == curPath && isLiveDirAtParts s.vfs parts &&
          (let isMainWt := !repo.isBare && match repo.worktrees.head? with | some mw => mw.rootPath == w.rootPath | none => false
           isMainWt || hasLinkedGitFileAtParts s.vfs parts)) with
        | some wt => some (repo, some wt, stripPathPrefixBytes curPath fullCanon)
        | none => none
    match found? with
    | some res => some res
    | none =>
      match revParts with
      | [] => none
      | _ :: rest => go rest fullCanon

/-- Resolve `repoPath` in `s.vfs` and discover the enclosing `RepoInstance` and worktree slot. -/
def resolveCwdAndDiscover (s : GitRepoState) (repoPath : String) :
    Except GitError (RepoInstance × Option WorktreeSlot × Option ByteArray × List ByteArray) := do
  validateFsPathArg repoPath
  let canonParts ← resolveDirInVfs s repoPath
  match discoverRepoAtParts s canonParts with
  | some (repo, wt?, rel?) => .ok (repo, wt?, rel?, canonParts)
  | none => .error { kind := .notARepo, message := s!"not a git repository: '{repoPath}'" }

private def resolveDwimRefEntry? (repo : RepoInstance) (name : String) : Option (String × CommitId) :=
  (dwimRefCandidates name).findSome? fun full =>
    if full.startsWith "refs/" then
      (lookupFullRef repo full).map (full, ·)
    else none

private def resolveDwimRefCommit? (repo : RepoInstance) (name : String) : Option CommitId :=
  (resolveDwimRefEntry? repo name).map (·.2)

private def resolveCommitIdArg? (repo : RepoInstance) (cid : CommitId) : Option CommitId :=
  if hasCommit repo cid then some cid
  else if cid.hex.length == 64 then resolveDwimRefCommit? repo cid.hex
  else none

/-- Resolve a `ParsedRev` in `repo` relative to `slot`, failing with `.invalidRef` if missing. -/
def resolveParsedRevInRepo (repo : RepoInstance) (slot : WorktreeSlot) (rev : ParsedRev) :
    Except GitError CommitId := do
  let baseCid ←
    match rev.base with
    | .head =>
      match headCommitOfSymbolic repo slot.head with
      | some cid => .ok cid
      | none => .error { kind := .invalidRef, message := "unborn HEAD" }
    | .commitId cid =>
      match resolveCommitIdArg? repo cid with
      | some c => .ok c
      | none => .error { kind := .invalidRef, message := s!"unknown commit '{cid.hex}'" }
    | .ref name =>
      match resolveDwimRefCommit? repo name with
      | some cid => .ok cid
      | none => .error { kind := .invalidRef, message := s!"unknown revision '{name}'" }
  match rev.steps with
  | [] => .ok baseCid
  | steps =>
    let useFastMap := repo.commits.length > 16
    let pMap := if useFastMap then buildCommitParentsMap repo.commits else .empty
    let getParents (c : CommitId) : List CommitId :=
      if useFastMap then pMap.getD c.hex [] else parentsOf repo c
    let rec walk (cur : CommitId) : List RevStep → Except GitError CommitId
      | [] => .ok cur
      | .tilde k :: rest =>
        let rec step1 (c : CommitId) : Nat → Except GitError CommitId
          | 0 => .ok c
          | n + 1 =>
            match (getParents c)[0]? with
            | some p => step1 p n
            | none => .error { kind := .invalidRef, message := "revision has no parent" }
        match step1 cur k with
        | .ok next => walk next rest
        | .error e => .error e
      | .caret k :: rest =>
        if k == 0 then
          walk cur rest
        else
          match (getParents cur)[k - 1]? with
          | some p => walk p rest
          | none => .error { kind := .invalidRef, message := "revision has no such parent" }
    walk baseCid steps

private def hasMultipleDwimHits (repo : RepoInstance) (name : String) : Bool :=
  let cands := dedupStringsLoop [] (dwimRefCandidates name)
  let hits := cands.filter fun full =>
    full.startsWith "refs/" && (lookupFullRef repo full).isSome
  hits.length > 1

private def isAmbiguousBareRef (repo : RepoInstance) (parsed : ParsedRev)
    (check40Hex : Bool := false) : Bool :=
  match parsed with
  | { base := .ref name, steps := [] } => hasMultipleDwimHits repo name
  | { base := .commitId cid, steps := [] } =>
    (check40Hex || (!hasCommit repo cid && cid.hex.length == 64)) && hasMultipleDwimHits repo cid.hex
  | _ => false

private def lookupTreeEntry (entries : List (ByteArray × GitTreeEntry)) (path : ByteArray) :
    Option GitTreeEntry :=
  (entries.find? (fun p => p.1 == path)).map (·.2)

private def upsertTreeEntry (entries : List (ByteArray × GitTreeEntry))
    (path : ByteArray) (entry : GitTreeEntry) : List (ByteArray × GitTreeEntry) :=
  let updated :=
    if entries.any (fun p => p.1 == path) then
      entries.map (fun p => if p.1 == path then (path, entry) else p)
    else
      entries ++ [(path, entry)]
  sortByBytes (·.1) updated

private def eraseTreeEntry (entries : List (ByteArray × GitTreeEntry)) (path : ByteArray) :
    List (ByteArray × GitTreeEntry) :=
  entries.filter (fun p => p.1 != path)

private def isSameBlobClass (a b : GitBlobKind) : Bool :=
  match a, b with
  | .symlink, .symlink => true
  | .regular _, .regular _ => true
  | .gitlink, .gitlink => true
  | _, _ => false

private def blobClassTag : GitBlobKind → UInt8
  | .regular _ => 1
  | .symlink => 2
  | .gitlink => 3

private def mkRenameBaseKey (kind : GitBlobKind) (base bytes : ByteArray) : ByteArray :=
  (ByteArray.empty.push (blobClassTag kind)) ++ base ++ (ByteArray.empty.push 0) ++ bytes

private def mkRenameBytesKey (kind : GitBlobKind) (bytes : ByteArray) : ByteArray :=
  (ByteArray.empty.push (blobClassTag kind)) ++ bytes

private def popUnusedSrc : Std.TreeSet ByteArray cmpBytes → List ByteArray → Option (ByteArray × List ByteArray)
  | _, [] => none
  | used, s :: rest =>
    if used.contains s then popUnusedSrc used rest else some (s, rest)

/-- Exact 100% rename pairing matching Git's `find_identical_files` (Pass 1 basename match, Pass 2 bytewise order). -/
def pairExactRenames (srcs : List (ByteArray × GitTreeEntry)) (dsts : List (ByteArray × GitTreeEntry)) :
    List (ByteArray × ByteArray) × List ByteArray × List ByteArray :=
  let srcsSorted := sortByBytes (·.1) srcs
  let dstsSorted := sortByBytes (·.1) dsts
  let byBaseRev : Std.TreeMap ByteArray (List ByteArray) cmpBytes :=
    srcsSorted.foldl (fun m (sPath, sEntry) =>
      let k := mkRenameBaseKey sEntry.kind (basenameBytes sPath) sEntry.bytes
      m.insert k (sPath :: (m.get? k).getD [])) {}
  let byBase0 : Std.TreeMap ByteArray (List ByteArray) cmpBytes :=
    byBaseRev.foldl (fun m k v => m.insert k v.reverse) {}
  let rec pass1 (m : Std.TreeMap ByteArray (List ByteArray) cmpBytes)
      (used : Std.TreeSet ByteArray cmpBytes)
      (pairs : List (ByteArray × ByteArray))
      (remDsts : List (ByteArray × GitTreeEntry)) :
      List (ByteArray × GitTreeEntry) →
        Std.TreeSet ByteArray cmpBytes × List (ByteArray × ByteArray) × List (ByteArray × GitTreeEntry)
    | [] => (used, pairs, remDsts.reverse)
    | (dPath, dEntry) :: rest =>
      let k := mkRenameBaseKey dEntry.kind (basenameBytes dPath) dEntry.bytes
      match m.get? k >>= popUnusedSrc used with
      | some (sPath, qRest) =>
        pass1 (m.insert k qRest) (used.insert sPath) ((sPath, dPath) :: pairs) remDsts rest
      | none =>
        pass1 m used pairs ((dPath, dEntry) :: remDsts) rest
  let (used1, pairs1, remDsts1) := pass1 byBase0 {} [] [] dstsSorted
  let byBytesRev : Std.TreeMap ByteArray (List ByteArray) cmpBytes :=
    srcsSorted.foldl (fun m (sPath, sEntry) =>
      if used1.contains sPath then m
      else
        let k := mkRenameBytesKey sEntry.kind sEntry.bytes
        m.insert k (sPath :: (m.get? k).getD [])) {}
  let byBytes0 : Std.TreeMap ByteArray (List ByteArray) cmpBytes :=
    byBytesRev.foldl (fun m k v => m.insert k v.reverse) {}
  let rec pass2 (m : Std.TreeMap ByteArray (List ByteArray) cmpBytes)
      (used : Std.TreeSet ByteArray cmpBytes)
      (pairs : List (ByteArray × ByteArray))
      (remDsts : List (ByteArray × GitTreeEntry)) :
      List (ByteArray × GitTreeEntry) →
        Std.TreeSet ByteArray cmpBytes × List (ByteArray × ByteArray) × List (ByteArray × GitTreeEntry)
    | [] => (used, pairs, remDsts.reverse)
    | (dPath, dEntry) :: rest =>
      let k := mkRenameBytesKey dEntry.kind dEntry.bytes
      match m.get? k >>= popUnusedSrc used with
      | some (sPath, qRest) =>
        pass2 (m.insert k qRest) (used.insert sPath) ((sPath, dPath) :: pairs) remDsts rest
      | none =>
        pass2 m used pairs ((dPath, dEntry) :: remDsts) rest
  let (used2, pairs2, remDsts2) := pass2 byBytes0 used1 pairs1 [] remDsts1
  let unpairedSrcs := (srcsSorted.filter (fun p => !used2.contains p.1)).map (·.1)
  let unpairedDsts := remDsts2.map (·.1)
  (pairs2.reverse, unpairedSrcs, unpairedDsts)

private def hasRepoUnderDir (repos : List RepoInstance) (absParts : List ByteArray) : Bool :=
  let absPath := joinAbsByteParts absParts
  repos.any fun r => r.commonDir == absPath || isPathPrefixBytes absPath r.commonDir

private def ensureDirChainForce (vfs : VfsNode) (cur : List ByteArray) : List ByteArray → VfsNode
  | [] => vfs
  | seg :: rest =>
    match lookupNodeAtParts vfs (cur ++ [seg]) with
    | some (.dir _ _ _) => ensureDirChainForce vfs (cur ++ [seg]) rest
    | _ =>
      let vfs' := addChildAtParts vfs cur seg (.dir true true [])
      ensureDirChainForce vfs' (cur ++ [seg]) rest

private def ensureParentsAndWriteEntry (vfs : VfsNode) (rootParts : List ByteArray)
    (relParts : List ByteArray) (entry : GitTreeEntry) : VfsNode :=
  let leafNode : VfsNode :=
    match entry.kind with
    | .regular ex => .file ex entry.bytes
    | .symlink => .symlink entry.bytes
    | .gitlink => .dir true true []
  match relParts.reverse with
  | [] => vfs
  | leaf :: revDirs =>
    let dirParts := revDirs.reverse
    let vfs' := ensureDirChainForce vfs rootParts dirParts
    match entry.kind, lookupNodeAtParts vfs' (rootParts ++ relParts) with
    | .gitlink, some (.dir _ _ _) => vfs'
    | _, _ => addChildAtParts vfs' (rootParts ++ dirParts) leaf leafNode

private def ensureParentsAndWriteEntryChecked (vfs : VfsNode) (rootParts : List ByteArray)
    (relParts : List ByteArray) (entry : GitTreeEntry) : VfsNode × Bool :=
  match relParts.reverse with
  | [] => (vfs, false)
  | _ :: revDirs =>
    let dirParts := revDirs.reverse
    if !isVfsChainWritable vfs rootParts dirParts then
      (vfs, true)
    else
      (ensureParentsAndWriteEntry vfs rootParts relParts entry, false)

/-- Child entry stored inside the flat-array fast VFS directory representation. -/
inductive VfsFastChild where
  /-- Subdirectory referencing its index in the directory table. -/
  | dir (id : Nat)
  /-- Regular file with executable bit and raw contents. -/
  | file (executable : Bool) (bytes : ByteArray)
  /-- Symbolic link storing its raw target bytes. -/
  | symlink (target : ByteArray)

private structure VfsFastDir where
  searchable : Bool
  writable : Bool
  nextOrd : Nat
  children : Std.TreeMap ByteArray (Nat × VfsFastChild) cmpBytes

private instance : Inhabited VfsFastDir :=
  ⟨{ searchable := false, writable := false, nextOrd := 0, children := {} }⟩

private structure VfsFastArena where
  dirs : Array VfsFastDir
  rootId : Nat

private def emptyFastArena : VfsFastArena :=
  { dirs := #[{ searchable := false, writable := false, nextOrd := 0, children := {} }], rootId := 0 }

private def natOrdBytes (n : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat ((n >>> 24) &&& 0xff),
    UInt8.ofNat ((n >>> 16) &&& 0xff),
    UInt8.ofNat ((n >>> 8) &&& 0xff),
    UInt8.ofNat (n &&& 0xff)
  ]

private def vfsDepthWithinLoop (maxDepth : Nat) : Nat → List (Nat × VfsNode) → Bool
  | 0, _ => false
  | _, [] => true
  | f + 1, (_, .file _ _) :: stack | f + 1, (_, .symlink _) :: stack =>
    vfsDepthWithinLoop maxDepth f stack
  | f + 1, (d, .dir _ _ cs) :: stack =>
    if d >= maxDepth then false
    else
      let stack' := cs.foldl (fun st (_, c) => (d + 1, c) :: st) stack
      vfsDepthWithinLoop maxDepth f stack'

private def vfsDepthWithin (maxDepth : Nat) (node : VfsNode) : Bool :=
  vfsDepthWithinLoop maxDepth (vfsNodeCount node + 1) [(0, node)]

private def toFastArenaAux : Nat → Array VfsFastDir → VfsNode → Array VfsFastDir × VfsFastChild
  | 0, dirs, _ =>
    let id := dirs.size
    (dirs.push { searchable := false, writable := false, nextOrd := 0, children := {} }, .dir id)
  | _ + 1, dirs, .file ex bs => (dirs, .file ex bs)
  | _ + 1, dirs, .symlink t => (dirs, .symlink t)
  | f + 1, dirs, .dir s w cs =>
    let (dirs1, m, nextOrd) := cs.foldl (fun (dAcc, mAcc, i) (k, c) =>
      let (dAcc', fc) := toFastArenaAux f dAcc c
      (dAcc', mAcc.insert k (i, fc), i + 1)) (dirs, {}, 0)
    let id := dirs1.size
    (dirs1.push { searchable := s, writable := w, nextOrd := nextOrd, children := m }, .dir id)

private def toFastArena (wtNode : VfsNode) : VfsFastArena :=
  let (dirs, rootChild) := toFastArenaAux 66 #[] wtNode
  match rootChild with
  | .dir id => { dirs := dirs, rootId := id }
  | _ => emptyFastArena

private def fromFastChild : Nat → Array VfsFastDir → VfsFastChild → VfsNode
  | 0, _, _ => .emptyDir
  | _ + 1, _, .file ex bs => .file ex bs
  | _ + 1, _, .symlink t => .symlink t
  | f + 1, dirs, .dir id =>
    let d := dirs[id]!
    let raw := d.children.foldl (fun acc k (ord, fc) =>
      (natOrdBytes ord, k, fromFastChild f dirs fc) :: acc) []
    let sorted := sortByBytes (·.1) raw.reverse
    .dir d.searchable d.writable (sorted.map (fun (_, k, vn) => (k, vn)))

private def fromFastArena (a : VfsFastArena) : VfsNode :=
  fromFastChild 66 a.dirs (.dir a.rootId)

private def arenaUpsertChild (d : VfsFastDir) (seg : ByteArray) (fc : VfsFastChild) : VfsFastDir :=
  match d.children.get? seg with
  | some (ord, _) => { d with children := d.children.insert seg (ord, fc) }
  | none => { d with nextOrd := d.nextOrd + 1, children := d.children.insert seg (d.nextOrd, fc) }

private def arenaLookupAtAux (dirs : Array VfsFastDir) (fc : VfsFastChild) : List ByteArray → Option VfsFastChild
  | [] => some fc
  | seg :: rest =>
    match fc with
    | .dir id =>
      match dirs[id]!.children.get? seg with
      | some (_, c) => arenaLookupAtAux dirs c rest
      | none => none
    | _ => none

private def arenaLookupAt (a : VfsFastArena) (relParts : List ByteArray) : Option VfsFastChild :=
  arenaLookupAtAux a.dirs (.dir a.rootId) relParts

private def arenaLookupCheckedAux (dirs : Array VfsFastDir) (fc : VfsFastChild) :
    List ByteArray → Except VfsErr VfsFastChild
  | [] => .ok fc
  | seg :: rest =>
    match fc with
    | .dir id =>
      let d := dirs[id]!
      if !d.searchable then .error .eacces
      else
        match d.children.get? seg with
        | some (_, c) => arenaLookupCheckedAux dirs c rest
        | none => .error .enoent
    | _ => .error .enotdir

private def arenaLookupRelEntryChecked (a : VfsFastArena)
    (relParts : List ByteArray) : Except VfsErr (Option GitTreeEntry) :=
  match arenaLookupCheckedAux a.dirs (.dir a.rootId) relParts with
  | .ok (.file ex bs) => .ok (some { kind := .regular ex, bytes := bs })
  | .ok (.symlink t) => .ok (some { kind := .symlink, bytes := t })
  | .ok (.dir _) => .ok none
  | .error .eacces => .error .eacces
  | .error _ => .ok none

private def arenaExistsRelDir (a : VfsFastArena) (relParts : List ByteArray) : Bool :=
  match arenaLookupCheckedAux a.dirs (.dir a.rootId) relParts with
  | .ok (.dir _) => true
  | _ => false

private def arenaIsChainWritableAux (dirs : Array VfsFastDir) (dirId : Nat) : List ByteArray → Bool
  | [] =>
    let d := dirs[dirId]!
    d.searchable && d.writable
  | seg :: rest =>
    let d := dirs[dirId]!
    if !d.searchable then false
    else
      match d.children.get? seg with
      | some (_, .dir cid) => arenaIsChainWritableAux dirs cid rest
      | _ => d.writable

private def arenaWriteAt (a : VfsFastArena) (dirId : Nat) : List ByteArray → GitTreeEntry → VfsFastArena
  | [], _ => a
  | [leaf], entry =>
    let d := a.dirs[dirId]!
    match entry.kind, d.children.get? leaf with
    | .gitlink, some (_, .dir _) => a
    | .gitlink, _ =>
      let newId := a.dirs.size
      let a1 := { a with dirs := a.dirs.push { searchable := true, writable := true, nextOrd := 0, children := {} } }
      let d' := arenaUpsertChild d leaf (.dir newId)
      { a1 with dirs := a1.dirs.set! dirId d' }
    | .regular ex, _ =>
      let d' := arenaUpsertChild d leaf (.file ex entry.bytes)
      { a with dirs := a.dirs.set! dirId d' }
    | .symlink, _ =>
      let d' := arenaUpsertChild d leaf (.symlink entry.bytes)
      { a with dirs := a.dirs.set! dirId d' }
  | seg :: rest, entry =>
    let d := a.dirs[dirId]!
    let (a1, childId) :=
      match d.children.get? seg with
      | some (_, .dir cid) => (a, cid)
      | _ =>
        let cid := a.dirs.size
        let a' := { a with dirs := a.dirs.push { searchable := true, writable := true, nextOrd := 0, children := {} } }
        let d' := arenaUpsertChild d seg (.dir cid)
        ({ a' with dirs := a'.dirs.set! dirId d' }, cid)
    arenaWriteAt a1 childId rest entry

private def arenaWriteEntryChecked (a : VfsFastArena) (relParts : List ByteArray)
    (entry : GitTreeEntry) : VfsFastArena × Bool :=
  match relParts.reverse with
  | [] => (a, false)
  | _ :: revDirs =>
    let dirParts := revDirs.reverse
    if !arenaIsChainWritableAux a.dirs a.rootId dirParts then (a, true)
    else (arenaWriteAt a a.rootId relParts entry, false)

private def arenaEraseAndPruneAux (a : VfsFastArena) (dirId : Nat) : List ByteArray → VfsFastArena × Bool
  | [] => (a, a.dirs[dirId]!.children.isEmpty)
  | [leaf] =>
    let d := a.dirs[dirId]!
    let m' := d.children.erase leaf
    ({ a with dirs := a.dirs.set! dirId { d with children := m' } }, m'.isEmpty)
  | seg :: rest =>
    let d := a.dirs[dirId]!
    match d.children.get? seg with
    | some (_, .dir cid) =>
      let (a1, childEmpty) := arenaEraseAndPruneAux a cid rest
      if childEmpty then
        let d1 := a1.dirs[dirId]!
        let m' := d1.children.erase seg
        ({ a1 with dirs := a1.dirs.set! dirId { d1 with children := m' } }, m'.isEmpty)
      else
        (a1, false)
    | _ => (a, d.children.isEmpty)

private def arenaRemoveAndPruneChecked (a : VfsFastArena) (relParts : List ByteArray)
    (preserveNonEmptyDir : Bool) : VfsFastArena × Bool :=
  match relParts.reverse with
  | [] => (a, false)
  | _ :: revParent =>
    let dirParts := revParent.reverse
    match arenaLookupAt a relParts with
    | none => (a, false)
    | some (.dir cid) =>
      if !a.dirs[cid]!.children.isEmpty && preserveNonEmptyDir then (a, false)
      else if !arenaIsChainWritableAux a.dirs a.rootId dirParts then (a, true)
      else ((arenaEraseAndPruneAux a a.rootId relParts).1, false)
    | some _ =>
      if !arenaIsChainWritableAux a.dirs a.rootId dirParts then (a, true)
      else ((arenaEraseAndPruneAux a a.rootId relParts).1, false)

private def arenaDirSubtreeRemovable (dirs : Array VfsFastDir) : Nat → VfsFastChild → Bool
  | 0, _ => true
  | _ + 1, .file _ _ | _ + 1, .symlink _ => true
  | f + 1, .dir id =>
    let d := dirs[id]!
    if !d.searchable then false
    else if !d.writable && !d.children.isEmpty then false
    else d.children.foldl (fun ok _ (_, c) => ok && arenaDirSubtreeRemovable dirs f c) true

private def arenaHasAnyUnignoredNoIgnore (dirs : Array VfsFastDir) : Nat → VfsFastChild → Bool
  | 0, _ => false
  | _ + 1, .file _ _ | _ + 1, .symlink _ => true
  | f + 1, .dir id =>
    let d := dirs[id]!
    if !d.searchable then false
    else if d.children.contains ".git".toUTF8 then true
    else d.children.foldl (fun found _ (_, c) => found || arenaHasAnyUnignoredNoIgnore dirs f c) false

private def arenaCheckCollisionNoIgnore (a : VfsFastArena) (relParts : List ByteArray)
    (allowDirLeaf skipExistingLeafFile : Bool) : Except GitError Unit :=
  let rec go (dirId : Nat) : List ByteArray → Except GitError Unit
    | [] => .ok ()
    | [leaf] =>
      let d := a.dirs[dirId]!
      match d.children.get? leaf with
      | none => .ok ()
      | some (_, .file _ _) | some (_, .symlink _) =>
        if skipExistingLeafFile then .ok ()
        else .error { kind := .dirtyWorktree, message := "untracked working tree file would be overwritten" }
      | some (_, .dir cid) =>
        if allowDirLeaf then .ok ()
        else if arenaHasAnyUnignoredNoIgnore a.dirs 66 (.dir cid) then
          .error { kind := .dirtyWorktree, message := "untracked working tree files would be overwritten" }
        else if !arenaDirSubtreeRemovable a.dirs 66 (.dir cid) then
          .error { kind := .commandFailed, message := "cannot opendir: permission denied" }
        else .ok ()
    | seg :: rest =>
      let d := a.dirs[dirId]!
      match d.children.get? seg with
      | none => .ok ()
      | some (_, .dir cid) =>
        if !a.dirs[cid]!.searchable then .error { kind := .commandFailed, message := "cannot opendir: permission denied" }
        else go cid rest
      | some (_, .file _ _) | some (_, .symlink _) =>
        .error { kind := .dirtyWorktree, message := "untracked working tree file would be overwritten" }
  go a.rootId relParts

private def writeTreeToVfs (vfs : VfsNode) (rootParts : List ByteArray)
    (entries : List (ByteArray × GitTreeEntry)) : VfsNode :=
  match lookupNodeAtParts vfs rootParts with
  | some (wtNode@(.dir _ _ _)) =>
    if entries.length > 8 && vfsDepthWithin 64 wtNode &&
        entries.all (fun (p, _) => (splitByteSlash p).length <= 64) then
      let fast0 := toFastArena wtNode
      let fast1 := entries.foldl (fun a (relPath, entry) =>
        arenaWriteAt a a.rootId (splitByteSlash relPath) entry) fast0
      updateNodeAtParts vfs rootParts (fun _ => fromFastArena fast1)
    else
      entries.foldl (fun v (relPath, entry) =>
        ensureParentsAndWriteEntry v rootParts (splitByteSlash relPath) entry) vfs
  | _ =>
    entries.foldl (fun v (relPath, entry) =>
      ensureParentsAndWriteEntry v rootParts (splitByteSlash relPath) entry) vfs

private def writeTreeToVfsChecked (vfs : VfsNode) (rootParts : List ByteArray)
    (entries : List (ByteArray × GitTreeEntry)) : VfsNode × Bool :=
  match lookupNodeAtParts vfs rootParts with
  | some (wtNode@(.dir _ _ _)) =>
    if entries.length > 8 && vfsDepthWithin 64 wtNode &&
        entries.all (fun (p, _) => (splitByteSlash p).length <= 64) then
      let fast0 := toFastArena wtNode
      let (fast1, hadErr) := entries.foldl (fun (a, errAcc) (relPath, entry) =>
        let (a', err') := arenaWriteEntryChecked a (splitByteSlash relPath) entry
        (a', errAcc || err')) (fast0, false)
      (updateNodeAtParts vfs rootParts (fun _ => fromFastArena fast1), hadErr)
    else
      entries.foldl (fun (v, hadErr) (relPath, entry) =>
        let (v', err') := ensureParentsAndWriteEntryChecked v rootParts (splitByteSlash relPath) entry
        (v', hadErr || err')) (vfs, false)
  | _ =>
    entries.foldl (fun (v, hadErr) (relPath, entry) =>
      let (v', err') := ensureParentsAndWriteEntryChecked v rootParts (splitByteSlash relPath) entry
      (v', hadErr || err')) (vfs, false)

private def hasAnyDirContentLoop (subRepos : List RepoInstance) (rootParts : List ByteArray) :
    Nat → List (List ByteArray × VfsNode) → Bool
  | 0, _ | _, [] => false
  | f + 1, (revPref, .file _ _) :: stack | f + 1, (revPref, .symlink _) :: stack =>
    if !revPref.isEmpty then true
    else hasAnyDirContentLoop subRepos rootParts f stack
  | f + 1, (revPref, .dir searchable _ cs) :: stack =>
    if !searchable then
      hasAnyDirContentLoop subRepos rootParts f stack
    else if !revPref.isEmpty && (lookupDirChild ".git".toUTF8 cs).isSome then
      true
    else if !revPref.isEmpty && !subRepos.isEmpty && hasRepoUnderDir subRepos (rootParts ++ revPref.reverse) then
      true
    else
      let (foundLeaf, revChildren) := cs.foldl (fun (hit, st) (name, child) =>
        if hit then (true, st)
        else if revPref.isEmpty && name == ".git".toUTF8 then (false, st)
        else
          match child with
          | .file _ _ | .symlink _ => (true, st)
          | .dir cSearch _ _ =>
            if !cSearch then (false, st)
            else (false, (name :: revPref, child) :: st)) (false, [])
      if foundLeaf then true
      else
        let stack' := revChildren.foldl (fun s item => item :: s) stack
        hasAnyDirContentLoop subRepos rootParts f stack'

private def collectPrefixDirsLoop (acc : Std.TreeSet ByteArray cmpBytes) (prefRev : List ByteArray) :
    List ByteArray → Std.TreeSet ByteArray cmpBytes
  | [] => acc
  | [_] => acc
  | seg :: rest =>
    let prefRev' := seg :: prefRev
    let dirKey := joinRelByteParts prefRev'.reverse
    collectPrefixDirsLoop (acc.insert dirKey) prefRev' rest

private def buildTrackedPrefixSet (trackedPaths : List ByteArray) : Std.TreeSet ByteArray cmpBytes :=
  trackedPaths.foldl (fun s p => collectPrefixDirsLoop s [] (splitByteSlash p)) {}

private def buildByteSet (xs : List ByteArray) : Std.TreeSet ByteArray cmpBytes :=
  xs.foldl (fun s x => s.insert x) {}

private def buildEntryMap (xs : List (ByteArray × GitTreeEntry)) :
    Std.TreeMap ByteArray GitTreeEntry cmpBytes :=
  xs.foldl (fun m (k, v) => m.insert k v) {}

private def collectUntrackedLoop (subRepos : List RepoInstance) (rootParts : List ByteArray)
    (trackedSet trackedPrefixSet trackedGitlinkSet : Std.TreeSet ByteArray cmpBytes) :
    Nat → List ByteArray → List (ByteArray × List ByteArray × VfsNode) → List ByteArray
  | 0, acc, _ | _, acc, [] => acc.reverse
  | f + 1, acc, (dirRel, revPref, .dir searchable _ cs) :: stack =>
    if !searchable then
      collectUntrackedLoop subRepos rootParts trackedSet trackedPrefixSet trackedGitlinkSet f acc stack
    else
      let (acc1, revSub) := cs.foldl (fun (a, sub) (name, child) =>
        if revPref.isEmpty && name == ".git".toUTF8 then (a, sub)
        else
          let rel := joinPathsBytes dirRel name
          match child with
          | .file _ _ | .symlink _ =>
            if trackedSet.contains rel then (a, sub) else (rel :: a, sub)
          | .dir searchableC _ _ =>
            if !searchableC || trackedGitlinkSet.contains rel then (a, sub)
            else
              let revSegs := name :: revPref
              let dirPfx := rel.push 0x2f
              let hasTrackedUnder := trackedSet.contains rel || trackedPrefixSet.contains rel
              if hasTrackedUnder then
                if trackedSet.contains rel then (a, sub)
                else (a, (rel, revSegs, child) :: sub)
              else if hasAnyDirContentLoop subRepos rootParts (vfsNodeCount child + 1) [(revSegs, child)] then
                (dirPfx :: a, sub)
              else (a, sub)) (acc, [])
      let stack' := revSub.foldl (fun s item => item :: s) stack
      collectUntrackedLoop subRepos rootParts trackedSet trackedPrefixSet trackedGitlinkSet f acc1 stack'
  | f + 1, acc, _ :: stack =>
    collectUntrackedLoop subRepos rootParts trackedSet trackedPrefixSet trackedGitlinkSet f acc stack

private structure RawStatusRec where
  pathBytes : ByteArray
  origBytes : Option ByteArray := none
  ix : Option StatusKind := none
  wt : Option StatusKind := none

private def lookupRelEntryOnNode (wtNode? : Option VfsNode)
    (relPath : ByteArray) : Except VfsErr (Option GitTreeEntry) :=
  match wtNode? with
  | none => .ok none
  | some rootNode =>
    match lookupNodeChecked rootNode (splitByteSlash relPath) with
    | .ok (.file ex bs) => .ok (some { kind := .regular ex, bytes := bs })
    | .ok (.symlink t) => .ok (some { kind := .symlink, bytes := t })
    | .ok (.dir _ _ _) => .ok none
    | .error .eacces => .error .eacces
    | .error _ => .ok none

private def existsRelAnyOnNode (wtNode? : Option VfsNode) (relPath : ByteArray) : Bool :=
  match wtNode? with
  | none => false
  | some rootNode =>
    match lookupNodeChecked rootNode (splitByteSlash relPath) with
    | .ok _ => true
    | .error _ => false

private def computeStatusEntries (s : GitRepoState) (repo : RepoInstance) (wt : WorktreeSlot) :
    Except GitError (Array StatusEntry) := do
  let wtNode? := lookupNodeAtParts s.vfs (splitByteSlash wt.rootPath)
  let wtNode := wtNode?.getD VfsNode.emptyDir
  let fastDisk := noSpecialDirsUnderNode wtNode
  let fastDiskMap : Std.TreeMap ByteArray GitTreeEntry cmpBytes :=
    if fastDisk then buildEntryMap (collectVfsFilesUnderNode wtNode) else {}
  let headTree :=
    match headCommitOfSymbolic repo wt.head with
    | some cid => treeOfCommit repo cid
    | none => []
  let conflictPaths := wt.index.conflicts.map (·.path)
  let conflictSet := buildByteSet conflictPaths
  let indexNonConf := wt.index.entries.filter (fun p => !conflictSet.contains p.1)
  let headNonConf := headTree.filter (fun p => !conflictSet.contains p.1)
  let headMap := buildEntryMap headNonConf
  let indexMap := buildEntryMap indexNonConf
  let allXPaths := dedupSortedByteArraysLoop [] (sortByBytes id (headNonConf.map (·.1) ++ indexNonConf.map (·.1)))
  let (xPlain, xSrcs, xDsts) := allXPaths.foldl
    (fun (acc : List (ByteArray × StatusKind) × List (ByteArray × GitTreeEntry) × List (ByteArray × GitTreeEntry)) p =>
      match headMap.get? p, indexMap.get? p with
      | some hE, some iE =>
        if hE == iE then acc
        else if !isSameBlobClass hE.kind iE.kind then ((p, .typeChanged) :: acc.1, acc.2.1, acc.2.2)
        else ((p, .modified) :: acc.1, acc.2.1, acc.2.2)
      | some hE, none => (acc.1, (p, hE) :: acc.2.1, acc.2.2)
      | none, some iE => (acc.1, acc.2.1, (p, iE) :: acc.2.2)
      | none, none => acc)
    ([], [], [])
  let (renPairs, unpSrcs, unpDsts) := pairExactRenames xSrcs xDsts
  let xMapList : List (ByteArray × StatusKind × Option ByteArray) :=
    xPlain.map (fun (p, k) => (p, k, none)) ++
    renPairs.map (fun (src, dst) => (dst, .renamed, some src)) ++
    unpSrcs.map (fun p => (p, .deleted, none)) ++
    unpDsts.map (fun p => (p, .added, none))
  let yMapList : List (ByteArray × StatusKind) :=
    indexNonConf.filterMap fun (p, iE) =>
      match iE.kind with
      | .gitlink =>
        match lookupRelEntryOnNode wtNode? p with
        | .error .eacces => none
        | .ok (some _) => some (p, .typeChanged)
        | _ => if existsRelAnyOnNode wtNode? p then none else some (p, .deleted)
      | _ =>
        let diskLookup : Except VfsErr (Option GitTreeEntry) :=
          if fastDisk then .ok (fastDiskMap.get? p)
          else lookupRelEntryOnNode wtNode? p
        match diskLookup with
        | .error .eacces => none
        | .ok none => some (p, .deleted)
        | .ok (some dE) =>
          if dE == iE then none
          else if !isSameBlobClass dE.kind iE.kind then some (p, .typeChanged)
          else some (p, .modified)
        | .error _ => some (p, .deleted)
  let trackedAll := indexNonConf.map (·.1) ++ conflictPaths
  let trackedSet := buildByteSet trackedAll
  let trackedPrefixSet := buildTrackedPrefixSet trackedAll
  let trackedGitlinkSet :=
    buildByteSet (indexNonConf.filterMap (fun (p, e) => if e.kind == .gitlink then some p else none))
  let hasNonGitlinkSubdir :=
    match wtNode? with
    | some (.dir true _ cs) =>
      cs.any fun (nm, ch) =>
        nm != ".git".toUTF8 &&
        match ch with
        | .dir true _ _ => !trackedGitlinkSet.contains nm
        | _ => false
    | _ => false
  let otherRepos :=
    if hasNonGitlinkSubdir then s.repos.filter (fun r => r.commonDir != repo.commonDir) else []
  let rootParts :=
    if otherRepos.isEmpty then [] else splitByteSlash wt.rootPath
  let untrackedPaths :=
    match wtNode? with
    | some node =>
      collectUntrackedLoop otherRepos rootParts trackedSet trackedPrefixSet trackedGitlinkSet
        (vfsOwnNodeCount node + 1) [] [(ByteArray.empty, [], node)]
    | none => []
  let xMapTree : Std.TreeMap ByteArray (StatusKind × Option ByteArray) cmpBytes :=
    xMapList.foldl (fun m (p, k, o?) => m.insert p (k, o?)) {}
  let yMapTree : Std.TreeMap ByteArray StatusKind cmpBytes :=
    yMapList.foldl (fun m (p, k) => m.insert p k) {}
  let trackedPathsUnion := dedupSortedByteArraysLoop [] (sortByBytes id (xMapList.map (·.1) ++ yMapList.map (·.1)))
  let trackedRecs : List RawStatusRec := trackedPathsUnion.map fun p =>
    let (ix?, orig?) :=
      match xMapTree.get? p with
      | some (k, o?) => (some k, o?)
      | none => (none, none)
    let wt? := yMapTree.get? p
    { pathBytes := p, origBytes := orig?, ix := ix?, wt := wt? }
  let confRecs : List RawStatusRec := wt.index.conflicts.map fun c =>
    { pathBytes := c.path, origBytes := none, ix := some c.oursStatus, wt := some c.theirsStatus }
  let untrackRecs : List RawStatusRec := untrackedPaths.map fun p =>
    { pathBytes := p, origBytes := none, ix := some .untracked, wt := some .untracked }
  let allSorted :=
    sortByBytes (·.pathBytes) (confRecs ++ trackedRecs) ++ sortByBytes (·.pathBytes) untrackRecs
  let entries ← allSorted.mapM fun rec => do
    let pathStr ←
      match String.fromUTF8? rec.pathBytes with
      | some str => .ok str
      | none => .error { kind := .parseError, message := "invalid UTF-8 in status path" }
    let origStr? ←
      match rec.origBytes with
      | none => .ok none
      | some bs =>
        match String.fromUTF8? bs with
        | some str => .ok (some str)
        | none => .error { kind := .parseError, message := "invalid UTF-8 in status origPath" }
    .ok { indexStatus := rec.ix, worktreeStatus := rec.wt, path := pathStr, origPath := origStr? }
  return entries.toArray

private def matchesAnyNormDirFilter (filters : List NormPathFilter) (p : ByteArray) : Bool :=
  filters.isEmpty || filters.any fun
    | .allWorktree => true
    | .exactOrDir q _ => isPathPrefixBytes q p

private def computeDiffEntries (s : GitRepoState) (repo : RepoInstance) (wt? : Option WorktreeSlot)
    (cwdRel? : Option ByteArray) (revA : ParsedRev) (revB? : Option ParsedRev)
    (paths : Array String) : Except GitError (Array DiffEntry) := do
  let slot ←
    match activeHeadSlot repo wt? with
    | some sl => .ok sl
    | none => .error { kind := .notARepo, message := "repository has no worktree slot" }
  let cidA ← resolveParsedRevInRepo repo slot revA
  let cidB? ← revB?.mapM (resolveParsedRevInRepo repo slot)
  let wtWork? ←
    if revB?.isNone then
      match wt? with
      | some wt => .ok (some wt)
      | none => .error { kind := .notARepo, message := "this operation must be run in a work tree" }
    else
      .ok none
  if wt?.isNone && !paths.isEmpty then
    .error { kind := .commandFailed, message := "diff pathspecs require a work tree" }
  let normPairs? : Option (List (String × NormPathFilter)) :=
    if paths.isEmpty then some []
    else
      match wt? with
      | some wt =>
        match String.fromUTF8? wt.rootPath with
        | some rootStr => normalizeCliPathspecs? rootStr cwdRel? paths
        | none => none
      | none => some []
  let filters ←
    match normPairs? with
    | some pairs => .ok (pairs.map Prod.snd)
    | none => .error { kind := .commandFailed, message := "unsupported or outside-repository diff pathspec" }
  let rawTreeA := treeOfCommit repo cidA
  let rawTreeB :=
    match cidB?, wtWork? with
    | some cidB, _ => treeOfCommit repo cidB
    | none, some wt =>
      let rootParts := splitByteSlash wt.rootPath
      let wtNode := (lookupNodeAtParts s.vfs rootParts).getD .emptyDir
      let fastDisk := noSpecialDirsUnderNode wtNode
      let fastDiskMap : Std.TreeMap ByteArray GitTreeEntry cmpBytes :=
        if fastDisk then buildEntryMap (collectVfsFilesUnder s.vfs rootParts) else {}
      let idxMap := buildEntryMap wt.index.entries
      let universePaths : List ByteArray :=
        (wt.index.entries.map Prod.fst) ++ (wt.index.conflicts.map ConflictEntry.path)
      let uniq := dedupSortedByteArraysLoop [] (sortByBytes id universePaths)
      uniq.filterMap fun p =>
        let fastLookup := if fastDisk then fastDiskMap.get? p else lookupVfsRelEntry s.vfs rootParts p
        match idxMap.get? p with
        | some { kind := .gitlink, bytes := bs } =>
          if existsVfsRelDir s.vfs rootParts p then
            some (p, { kind := .gitlink, bytes := bs })
          else
            fastLookup.map (p, ·)
        | _ =>
          fastLookup.map (p, ·)
    | none, none => []
  let treeA := rawTreeA.filter (fun p => matchesAnyNormPathFilter filters p.1)
  let treeB := rawTreeB.filter (fun p => matchesAnyNormPathFilter filters p.1)
  let treeAMap := buildEntryMap treeA
  let treeBMap := buildEntryMap treeB
  let allPaths := dedupSortedByteArraysLoop [] (sortByBytes id (treeA.map (·.1) ++ treeB.map (·.1)))
  let (plain, srcs, dsts) := allPaths.foldl
    (fun (acc : List (ByteArray × DiffKind) × List (ByteArray × GitTreeEntry) × List (ByteArray × GitTreeEntry)) p =>
      match treeAMap.get? p, treeBMap.get? p with
      | some aE, some bE =>
        if aE == bE then acc
        else if !isSameBlobClass aE.kind bE.kind then ((p, .typeChanged) :: acc.1, acc.2.1, acc.2.2)
        else ((p, .modified) :: acc.1, acc.2.1, acc.2.2)
      | some aE, none => (acc.1, (p, aE) :: acc.2.1, acc.2.2)
      | none, some bE => (acc.1, acc.2.1, (p, bE) :: acc.2.2)
      | none, none => acc)
    ([], [], [])
  let (renPairs, unpSrcs, unpDsts) := pairExactRenames srcs dsts
  let allRecs : List (ByteArray × DiffKind × Option ByteArray) :=
    plain.map (fun (p, k) => (p, k, none)) ++
    renPairs.map (fun (src, dst) => (dst, .renamed 100, some src)) ++
    unpSrcs.map (fun p => (p, .deleted, none)) ++
    unpDsts.map (fun p => (p, .added, none))
  let sortedRecs := sortByBytes (·.1) allRecs
  let out ← sortedRecs.mapM fun (pBytes, kind, orig?) => do
    let pStr ←
      match String.fromUTF8? pBytes with
      | some str => .ok str
      | none => .error { kind := .parseError, message := "invalid UTF-8 in diff path" }
    let oStr? ←
      match orig? with
      | none => .ok none
      | some obs =>
        match String.fromUTF8? obs with
        | some str => .ok (some str)
        | none => .error { kind := .parseError, message := "invalid UTF-8 in diff origPath" }
    .ok { kind := kind, path := pStr, origPath := oStr? }
  return out.toArray

private def collectOverwrittenDirPaths (vfs : VfsNode) (rootParts : List ByteArray)
    (newTree : List (ByteArray × GitTreeEntry)) : List ByteArray :=
  newTree.filterMap fun (relPath, entry) =>
    if entry.kind == .gitlink then none
    else
      let fullParts := rootParts ++ splitByteSlash relPath
      match lookupNodeAtParts vfs fullParts with
      | some (.dir _ _ _) => some (joinAbsByteParts fullParts)
      | _ => none

private def pruneReposUnderPaths (ownCommonDir : ByteArray) (overwritten : List ByteArray)
    (repos : List RepoInstance) : List RepoInstance :=
  if overwritten.isEmpty then repos
  else
    repos.filter fun r =>
      r.commonDir == ownCommonDir ||
      !overwritten.any (fun d => r.commonDir == d || isPathPrefixBytes d r.commonDir)

private def isGitlinkDirOnDisk (vfs : VfsNode) (rootParts : List ByteArray) (p : ByteArray) : Bool :=
  match lookupNodeAtParts vfs (rootParts ++ splitByteSlash p) with
  | some (.dir _ _ _) => true
  | _ => false

private def bulkRemoveEntriesChecked (vfs : VfsNode) (rootParts : List ByteArray)
    (deletions : List (ByteArray × Bool)) : VfsNode × Bool :=
  match lookupNodeAtParts vfs rootParts with
  | some (wtNode@(.dir _ _ _)) =>
    if deletions.length > 8 && vfsDepthWithin 64 wtNode &&
        deletions.all (fun (p, _) => (splitByteSlash p).length <= 64) then
      let fast0 := toFastArena wtNode
      let (fast1, hadErr) := deletions.foldl (fun (a, errAcc) (relPath, keepDir) =>
        let (a', e') := arenaRemoveAndPruneChecked a (splitByteSlash relPath) keepDir
        (a', errAcc || e')) (fast0, false)
      (updateNodeAtParts vfs rootParts (fun _ => fromFastArena fast1), hadErr)
    else
      deletions.foldl (fun (v, hadErr) (relPath, keepDir) =>
        let (v', e') := removeEntryAndPruneVfsChecked v rootParts (splitByteSlash relPath) keepDir
        (v', hadErr || e')) (vfs, false)
  | _ =>
    deletions.foldl (fun (v, hadErr) (relPath, keepDir) =>
      let (v', e') := removeEntryAndPruneVfsChecked v rootParts (splitByteSlash relPath) keepDir
      (v', hadErr || e')) (vfs, false)

private def checkNonForcePathCollision (vfs : VfsNode) (repos : List RepoInstance)
    (rootParts : List ByteArray) (relPath : ByteArray)
    (allowDirLeaf skipExistingLeafFile : Bool) : Except GitError Unit :=
  let fullSegs := splitByteSlash relPath
  let rec go (pref : List ByteArray) : List ByteArray → Except GitError Unit
    | [] => .ok ()
    | [leaf] =>
      let cur := pref ++ [leaf]
      match lookupNodeAtParts vfs (rootParts ++ cur) with
      | none => .ok ()
      | some (.file _ _) | some (.symlink _) =>
        if skipExistingLeafFile then .ok ()
        else .error { kind := .dirtyWorktree, message := "untracked working tree file would be overwritten" }
      | some (d@(.dir _ _ _)) =>
        if allowDirLeaf then .ok ()
        else if hasAnyDirContentLoop repos rootParts (vfsNodeCount d + 1) [(cur.reverse, d)] then
          .error { kind := .dirtyWorktree, message := "untracked working tree files would be overwritten" }
        else if !dirTreeCanBeRemovedChecked vfs rootParts cur then
          .error { kind := .commandFailed, message := "cannot opendir: permission denied" }
        else .ok ()
    | seg :: rest =>
      let cur := pref ++ [seg]
      match lookupNodeAtParts vfs (rootParts ++ cur) with
      | none => .ok ()
      | some (.dir searchable _ _) =>
        if !searchable then .error { kind := .commandFailed, message := "cannot opendir: permission denied" }
        else go cur rest
      | some (.file _ _) | some (.symlink _) =>
        .error { kind := .dirtyWorktree, message := "untracked working tree file would be overwritten" }
  go [] fullSegs

private def recordNonForcePreflight (res : Except GitError Unit) (permErr? : Option GitError) :
    Except GitError (Option GitError) :=
  match res with
  | .ok () => .ok permErr?
  | .error e =>
    if e.kind == .commandFailed then
      .ok (match permErr? with | some prev => some prev | none => some e)
    else
      .error e

/-- Perform a two-tree worktree/index checkout transition from `oldTree` to `newTree`, also reporting permission errors. -/
def applyTwoTreeCheckoutWithPerm (vfs : VfsNode) (wt : WorktreeSlot)
    (oldTree newTree : List (ByteArray × GitTreeEntry)) (force : Bool)
    (repos : List RepoInstance := []) :
    Except GitError (VfsNode × IndexState × Bool) := do
  let rootParts := splitByteSlash wt.rootPath
  let wtNode := (lookupNodeAtParts vfs rootParts).getD VfsNode.emptyDir
  if force then
    let allRemovable := dirSubtreeRemovableLoop [wtNode]
    let preflightOk :=
      allRemovable ||
      newTree.all fun (relPath, entry) =>
        entry.kind == .gitlink || dirTreeCanBeRemovedChecked vfs rootParts (splitByteSlash relPath)
    if !preflightOk then
      .error { kind := .commandFailed, message := "cannot opendir: permission denied" }
    let newMap := buildEntryMap newTree
    let oldMap := buildEntryMap oldTree
    let idxMap := buildEntryMap wt.index.entries
    let allPaths :=
      dedupSortedByteArraysLoop []
        (sortByBytes id (oldTree.map (·.1) ++ wt.index.entries.map (·.1) ++ newTree.map (·.1)))
    let deletions : List (ByteArray × Bool) :=
      allPaths.filterMap fun p =>
        match newMap.get? p with
        | some _ => none
        | none =>
          let keepDir :=
            match oldMap.get? p, idxMap.get? p with
            | some oE, _ => oE.kind == .gitlink
            | none, some iE => iE.kind == .gitlink
            | none, none => false
          some (p, keepDir)
    let (v1, _errDel) := bulkRemoveEntriesChecked vfs rootParts deletions
    let wtNode1 := (lookupNodeAtParts v1 rootParts).getD VfsNode.emptyDir
    let useFastDisk1 := allRemovable && noSpecialDirsUnderNode wtNode1 &&
      (match wtNode1 with | .dir true true _ => true | _ => false)
    let diskMap1 : Std.TreeMap ByteArray GitTreeEntry cmpBytes :=
      if useFastDisk1 then buildEntryMap (collectVfsFilesUnder v1 rootParts) else {}
    let entriesToWrite :=
      newTree.filter fun (relPath, entry) =>
        if idxMap.get? relPath != some entry then true
        else
          let dOpt :=
            if useFastDisk1 then diskMap1.get? relPath
            else
              match lookupVfsRelEntryChecked v1 rootParts relPath with
              | .ok opt => opt
              | .error _ => none
          dOpt != some entry
    let (v2, errWr) := writeTreeToVfsChecked v1 rootParts entriesToWrite
    let idx' : IndexState :=
      { entries := sortByBytes (·.1) newTree, conflicts := [], hasMergeHead := false, mergeParents := [] }
    .ok (v2, idx', errWr)
  else if oldTree.length + newTree.length <= 8 then
    let diffPaths :=
      (oldTree.map (·.1) ++ newTree.map (·.1)).filter fun p =>
        lookupTreeEntry oldTree p != lookupTreeEntry newTree p
    let mut permErr? : Option GitError := none
    for p in diffPaths do
      let old? := lookupTreeEntry oldTree p
      let new? := lookupTreeEntry newTree p
      let idx? := lookupTreeEntry wt.index.entries p
      let diskRes := lookupVfsRelEntryChecked vfs rootParts p
      let disk? := match diskRes with | .ok opt => opt | .error _ => none
      let stepRes : Except GitError Unit :=
        match old?, idx?, new? with
        | _, some iE, some nE =>
          if iE == nE then .ok ()
          else
            match old? with
            | none =>
              .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
            | some oE =>
              if iE != oE then
                .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
              else if oE.kind == .gitlink then
                if disk?.isSome then
                  .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
                else .ok ()
              else
                match diskRes with
                | .error .eacces =>
                  .error { kind := .commandFailed, message := "cannot stat path: permission denied" }
                | .ok (some dE) =>
                  if dE != iE then
                    .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
                  else .ok ()
                | _ =>
                  if existsVfsRelDir vfs rootParts p then
                    .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
                  else .ok ()
        | some oE, none, none =>
          if !(oE.kind == .gitlink && isGitlinkDirOnDisk vfs rootParts p) then
            checkNonForcePathCollision vfs repos rootParts p (oE.kind == .gitlink) false
          else .ok ()
        | none, none, some _ => .ok ()
        | some oE, some iE, none =>
          if iE != oE then
            .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
          else if oE.kind == .gitlink then
            if disk?.isSome then
              .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
            else .ok ()
          else
            match diskRes with
            | .error .eacces =>
              .error { kind := .commandFailed, message := "cannot stat path: permission denied" }
            | .ok (some dE) =>
              if dE != iE then
                .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
              else .ok ()
            | _ =>
              if existsVfsRelDir vfs rootParts p then
                .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
              else .ok ()
        | some _, none, some _ =>
          .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
        | none, some _, none => .ok ()
        | none, none, none => .ok ()
      permErr? ← recordNonForcePreflight stepRes permErr?
    let (v1, _errDel) := diffPaths.foldl (fun (v, hadErr) p =>
      let idx? := lookupTreeEntry wt.index.entries p
      match lookupTreeEntry oldTree p, lookupTreeEntry newTree p with
      | some oE, none =>
        if idx?.isSome then
          let (v', e') := removeEntryAndPruneVfsChecked v rootParts (splitByteSlash p) (oE.kind == .gitlink)
          (v', hadErr || e')
        else (v, hadErr)
      | _, _ => (v, hadErr)) (vfs, false)
    for p in diffPaths do
      let old? := lookupTreeEntry oldTree p
      let idx? := lookupTreeEntry wt.index.entries p
      let stepRes2 : Except GitError Unit :=
        match lookupTreeEntry newTree p with
        | none => .ok ()
        | some nE =>
          if idx? == some nE then .ok ()
          else
            match old? with
            | none =>
              checkNonForcePathCollision v1 repos rootParts p (nE.kind == .gitlink) false
            | some oE =>
              if oE.kind == .gitlink && nE.kind != .gitlink then
                if !dirTreeCanBeRemovedChecked v1 rootParts (splitByteSlash p) then
                  .error { kind := .commandFailed, message := "cannot opendir: permission denied" }
                else .ok ()
              else
                let hadDiskFile := (lookupVfsRelEntry v1 rootParts p).isSome
                checkNonForcePathCollision v1 repos rootParts p (nE.kind == .gitlink) hadDiskFile
      permErr? ← recordNonForcePreflight stepRes2 permErr?
    match permErr? with
    | some e => .error e
    | none => pure ()
    let (v2, errWr) := diffPaths.foldl (fun (v, hadErr) p =>
      let idx? := lookupTreeEntry wt.index.entries p
      match lookupTreeEntry newTree p with
      | some entry =>
        if idx? == some entry then (v, hadErr)
        else
          let (v', e') := ensureParentsAndWriteEntryChecked v rootParts (splitByteSlash p) entry
          (v', hadErr || e')
      | none => (v, hadErr)) (v1, false)
    let idxEntries := diffPaths.foldl (fun entries p =>
      match lookupTreeEntry newTree p with
      | some entry => upsertTreeEntry entries p entry
      | none => eraseTreeEntry entries p) wt.index.entries
    .ok (v2, { wt.index with entries := idxEntries, conflicts := [], hasMergeHead := false, mergeParents := [] }, errWr)
  else
    let oldMap := buildEntryMap oldTree
    let newMap := buildEntryMap newTree
    let idxMap := buildEntryMap wt.index.entries
    let candPaths :=
      dedupSortedByteArraysLoop [] (sortByBytes id (oldTree.map (·.1) ++ newTree.map (·.1)))
    let diffPaths := candPaths.filter (fun p => oldMap.get? p != newMap.get? p)
    let useFastVfs :=
      (match lookupNodeAtParts vfs rootParts with | some (.dir _ _ _) => true | _ => false) &&
      vfsDepthWithin 64 wtNode &&
      diffPaths.all (fun p => (splitByteSlash p).length <= 64)
    let fast0 : VfsFastArena :=
      if useFastVfs then toFastArena wtNode else emptyFastArena
    let wtRootAbs := joinAbsByteParts rootParts
    let wtDotGitAbs := joinAbsByteParts (rootParts ++ [".git".toUTF8])
    let noNestedRepos :=
      repos.all (fun r => r.commonDir == wtDotGitAbs || !isPathPrefixBytes wtRootAbs r.commonDir)
    let mut permErr? : Option GitError := none
    for p in diffPaths do
      let relParts := splitByteSlash p
      let old? := oldMap.get? p
      let new? := newMap.get? p
      let idx? := idxMap.get? p
      let diskRes :=
        if useFastVfs then arenaLookupRelEntryChecked fast0 relParts
        else lookupVfsRelEntryChecked vfs rootParts p
      let disk? := match diskRes with | .ok opt => opt | .error _ => none
      let hasDiskDir :=
        if useFastVfs then arenaExistsRelDir fast0 relParts
        else existsVfsRelDir vfs rootParts p
      let stepRes : Except GitError Unit :=
        match old?, idx?, new? with
        | _, some iE, some nE =>
          if iE == nE then .ok ()
          else
            match old? with
            | none =>
              .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
            | some oE =>
              if iE != oE then
                .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
              else if oE.kind == .gitlink then
                if disk?.isSome then
                  .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
                else .ok ()
              else
                match diskRes with
                | .error .eacces =>
                  .error { kind := .commandFailed, message := "cannot stat path: permission denied" }
                | .ok (some dE) =>
                  if dE != iE then
                    .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
                  else .ok ()
                | _ =>
                  if hasDiskDir then
                    .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
                  else .ok ()
        | some oE, none, none =>
          let isGitlinkDir :=
            if useFastVfs then
              match arenaLookupAt fast0 relParts with | some (.dir _) => true | _ => false
            else isGitlinkDirOnDisk vfs rootParts p
          if !(oE.kind == .gitlink && isGitlinkDir) then
            if useFastVfs && noNestedRepos then
              arenaCheckCollisionNoIgnore fast0 relParts (oE.kind == .gitlink) false
            else
              checkNonForcePathCollision vfs repos rootParts p (oE.kind == .gitlink) false
          else .ok ()
        | none, none, some _ => .ok ()
        | some oE, some iE, none =>
          if iE != oE then
            .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
          else if oE.kind == .gitlink then
            if disk?.isSome then
              .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
            else .ok ()
          else
            match diskRes with
            | .error .eacces =>
              .error { kind := .commandFailed, message := "cannot stat path: permission denied" }
            | .ok (some dE) =>
              if dE != iE then
                .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
              else .ok ()
            | _ =>
              if hasDiskDir then
                .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
              else .ok ()
        | some _, none, some _ =>
          .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }
        | none, some _, none => .ok ()
        | none, none, none => .ok ()
      permErr? ← recordNonForcePreflight stepRes permErr?
    let deletions : List (ByteArray × Bool) :=
      diffPaths.filterMap fun p =>
        match oldMap.get? p, newMap.get? p with
        | some oE, none =>
          if (idxMap.get? p).isSome then some (p, oE.kind == .gitlink) else none
        | _, _ => none
    let (fast1, v1) : VfsFastArena × VfsNode :=
      if useFastVfs then
        let (f1, _) := deletions.foldl (fun (a, errAcc) (relPath, keepDir) =>
          let (a', e') := arenaRemoveAndPruneChecked a (splitByteSlash relPath) keepDir
          (a', errAcc || e')) (fast0, false)
        let v1Lazy :=
          if noNestedRepos then vfs
          else updateNodeAtParts vfs rootParts (fun _ => fromFastArena f1)
        (f1, v1Lazy)
      else
        let (v1Seq, _) := bulkRemoveEntriesChecked vfs rootParts deletions
        (fast0, v1Seq)
    for p in diffPaths do
      let relParts := splitByteSlash p
      let old? := oldMap.get? p
      let idx? := idxMap.get? p
      let stepRes2 : Except GitError Unit :=
        match newMap.get? p with
        | none => .ok ()
        | some nE =>
          if idx? == some nE then .ok ()
          else
            match old? with
            | none =>
              if useFastVfs && noNestedRepos then
                arenaCheckCollisionNoIgnore fast1 relParts (nE.kind == .gitlink) false
              else
                checkNonForcePathCollision v1 repos rootParts p (nE.kind == .gitlink) false
            | some oE =>
              if oE.kind == .gitlink && nE.kind != .gitlink then
                let canRm :=
                  if useFastVfs then
                    match arenaLookupAt fast1 relParts with
                    | some (.dir cid) => arenaDirSubtreeRemovable fast1.dirs 66 (.dir cid)
                    | _ => true
                  else dirTreeCanBeRemovedChecked v1 rootParts relParts
                if !canRm then
                  .error { kind := .commandFailed, message := "cannot opendir: permission denied" }
                else .ok ()
              else
                let hadDiskFile :=
                  if useFastVfs then
                    match arenaLookupRelEntryChecked fast1 relParts with
                    | .ok (some _) => true
                    | _ => false
                  else (lookupVfsRelEntry v1 rootParts p).isSome
                if useFastVfs && noNestedRepos then
                  arenaCheckCollisionNoIgnore fast1 relParts (nE.kind == .gitlink) hadDiskFile
                else
                  checkNonForcePathCollision v1 repos rootParts p (nE.kind == .gitlink) hadDiskFile
      permErr? ← recordNonForcePreflight stepRes2 permErr?
    match permErr? with
    | some e => .error e
    | none => pure ()
    let (v2, errWr) : VfsNode × Bool :=
      if useFastVfs then
        let (fast2, hadWrErr) := diffPaths.foldl (fun (a, errAcc) p =>
          match newMap.get? p with
          | some entry =>
            if idxMap.get? p == some entry then (a, errAcc)
            else
              let relParts := splitByteSlash p
              let (a', e') := arenaWriteEntryChecked a relParts entry
              (a', errAcc || e')
          | none => (a, errAcc)) (fast1, false)
        (updateNodeAtParts vfs rootParts (fun _ => fromFastArena fast2), hadWrErr)
      else
        diffPaths.foldl (fun (v, hadErr) p =>
          match newMap.get? p with
          | some entry =>
            if idxMap.get? p == some entry then (v, hadErr)
            else
              let (v', e') := ensureParentsAndWriteEntryChecked v rootParts (splitByteSlash p) entry
              (v', hadErr || e')
          | none => (v, hadErr)) (v1, false)
    let idxMap' := diffPaths.foldl (fun m p =>
      match newMap.get? p with
      | some entry => m.insert p entry
      | none => m.erase p) idxMap
    let idxEntries := sortByBytes (·.1) (idxMap'.foldl (fun acc k v => (k, v) :: acc) [] |>.reverse)
    .ok (v2, { wt.index with entries := idxEntries, conflicts := [], hasMergeHead := false, mergeParents := [] }, errWr)

/-- Lexically normalize `.` and `..` segments appended to canonical `base` path parts. -/
def normalizeDotDotParts (base rel : List ByteArray) : List ByteArray :=
  rel.foldl (fun acc seg =>
    if seg == ".".toUTF8 then acc
    else if seg == "..".toUTF8 then acc.dropLast
    else acc ++ [seg]) base

private def asciiLowerStrModel (s : String) : String :=
  String.ofList (s.toList.map fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c)

private def isLocalFileSource? (source : String) : Option (Bool × String) :=
  let low := asciiLowerStrModel source
  if low.startsWith "file://localhost/" then
    some (true, String.ofList (source.toList.drop 16))
  else if low.startsWith "file:///" then
    some (true, String.ofList (source.toList.drop 7))
  else if low.startsWith "file://" then
    none
  else if hasSubstrChars [':', '/', '/'] source.toList then
    none
  else
    let beforeSlash := source.toList.takeWhile (· != '/')
    if beforeSlash.contains ':' then none
    else some (false, source)

private def truncateCommitsDepth (commits : List CommitNode) (tips : List CommitId) (depth : Nat) :
    List CommitNode :=
  if depth == 0 then []
  else
    let commitMap : Std.TreeMap String CommitNode compare :=
      commits.foldl (fun mp c => if mp.contains c.id.hex then mp else mp.insert c.id.hex c) {}
    let rec dedupIdsLoop (seen : Std.TreeSet String compare) (acc : List CommitId) :
        List CommitId → List CommitId × Std.TreeSet String compare
      | [] => (acc.reverse, seen)
      | x :: xs =>
        if !commitMap.contains x.hex || seen.contains x.hex then dedupIdsLoop seen acc xs
        else dedupIdsLoop (seen.insert x.hex) (x :: acc) xs
    let (initTips, initVis) := dedupIdsLoop {} [] tips
    let rec bfs (frontier : List CommitId) (vis : Std.TreeSet String compare) (rem : Nat) :
        Std.TreeSet String compare × Std.TreeSet String compare :=
      match rem with
      | 0 =>
        let bnd := frontier.foldl (fun st c => st.insert c.hex) ({} : Std.TreeSet String compare)
        (vis, bnd)
      | n + 1 =>
        let (nextRev, vis') := frontier.foldl
          (fun (acc, vs) cid =>
            let ps := match commitMap.get? cid.hex with | some node => node.parents | none => []
            ps.foldl
              (fun (a2, vs2) p =>
                if commitMap.contains p.hex && !vs2.contains p.hex then
                  (p :: a2, vs2.insert p.hex)
                else
                  (a2, vs2))
              (acc, vs))
          ([], vis)
        if nextRev.isEmpty then (vis', {})
        else bfs nextRev.reverse vis' n
    let (keptSet, boundarySet) := bfs initTips initVis (depth - 1)
    (commits.filter (fun c => keptSet.contains c.id.hex)).map fun c =>
      if boundarySet.contains c.id.hex then
        { c with parents := [] }
      else
        { c with parents := c.parents.filter (fun p => keptSet.contains p.hex) }

private def findExactSourceRepoFrom (s : GitRepoState) (baseParts : List ByteArray) (srcPath : String) :
    Except GitError (RepoInstance × Option WorktreeSlot × ByteArray) := do
  let sBytes := srcPath.toUTF8
  let cwdParts := if startsWithSlashByte sBytes then [] else baseParts
  match resolveVfsFuel 41 s.vfs cwdParts (splitByteSlash sBytes) true with
  | .ok (.file _ _ _) =>
    .error { kind := .commandFailed, message := s!"invalid gitfile format: '{srcPath}'" }
  | .ok (.dir canonParts searchable _ _) =>
    if !searchable then
      .error { kind := .notFound, message := s!"repository '{srcPath}' does not exist" }
    else
      let canonBytes := joinAbsByteParts canonParts
      let found? := s.repos.findSome? fun r =>
        if r.commonDir == canonBytes then
          some (r, r.worktrees.head?, r.commonDir)
        else
          match r.worktrees.find? (fun w => w.rootPath == canonBytes) with
          | some wt =>
            let isMainWt := !r.isBare && match r.worktrees.head? with
              | some mw => mw.rootPath == wt.rootPath
              | none => false
            if isMainWt || hasLinkedGitFileAtParts s.vfs canonParts then
              some (r, some wt, wt.rootPath)
            else
              none
          | none => none
      match found? with
      | some res => .ok res
      | none => .error { kind := .notFound, message := s!"repository '{srcPath}' does not exist" }
  | .ok (.symlink _ _) =>
    .error { kind := .notFound, message := s!"repository '{srcPath}' does not exist" }
  | .error e =>
    .error { kind := .notFound, message := s!"repository '{srcPath}' does not exist: {repr e}" }

private def findExactSourceRepo (s : GitRepoState) (srcPath : String) :
    Except GitError (RepoInstance × Option WorktreeSlot × ByteArray) :=
  findExactSourceRepoFrom s (splitByteSlash s.processCwd) srcPath

private def resolveBareDanglingDest :
    Nat → VfsNode → List ByteArray → List ByteArray → Except GitError (VfsNode × List ByteArray)
  | 0, _, _, _ => .error { kind := .invalidInput, message := "too many levels of symbolic links" }
  | fuel' + 1, vfs, cur, segs =>
    if segs.isEmpty then
      .error { kind := .commandFailed, message := "invalid bare clone target" }
    else
      match resolveVfsFuel 41 vfs cur segs.dropLast true with
      | .ok (.dir parentParts searchable writable cs) =>
        if !searchable then
          .error { kind := .commandFailed, message := "permission denied" }
        else
          let lastSeg := segs.getLast!
          if lastSeg == ".".toUTF8 then
            .ok (vfs, parentParts)
          else if lastSeg == "..".toUTF8 then
            .ok (vfs, parentParts.dropLast)
          else
            match lookupDirChild lastSeg cs with
            | none =>
              if !writable then
                .error { kind := .commandFailed, message := "permission denied" }
              else
                let v' := addChildAtParts vfs parentParts lastSeg (.dir true true [])
                .ok (v', parentParts ++ [lastSeg])
            | some (.symlink rawTarget) =>
              let tParts := splitByteSlash rawTarget
              let baseCur := if startsWithSlashByte rawTarget then [] else parentParts
              resolveBareDanglingDest fuel' vfs baseCur tParts
            | some (.dir s _ dcs) =>
              if !s then .error { kind := .commandFailed, message := "permission denied" }
              else if !dcs.isEmpty then
                .error { kind := .alreadyExists, message := "destination already exists" }
              else .ok (vfs, parentParts ++ [lastSeg])
            | some (.file _ _) =>
              .error { kind := .alreadyExists, message := "destination already exists" }
      | .error .eloop => .error { kind := .invalidInput, message := "too many levels of symbolic links" }
      | _ => .error { kind := .commandFailed, message := "invalid bare clone path" }

private def checkCloneTargetDest (s : GitRepoState) (target : String) (isBare : Bool := false) :
    Except GitError (VfsNode × List ByteArray) := do
  let tBytes := target.toUTF8
  let cwdParts := if startsWithSlashByte tBytes then [] else splitByteSlash s.processCwd
  match resolveVfsFuel 41 s.vfs cwdParts (splitByteSlash tBytes) true with
  | .ok (.dir canonParts searchable _ cs) =>
    if !searchable then
      .error { kind := .commandFailed, message := "permission denied" }
    else if !cs.isEmpty then
      .error { kind := .alreadyExists, message := s!"destination path '{target}' already exists and is not an empty directory" }
    else
      .ok (s.vfs, canonParts)
  | .ok (.file _ _ _) | .ok (.symlink _ _) =>
    .error { kind := .alreadyExists, message := s!"destination path '{target}' already exists and is not an empty directory" }
  | .error .enoent =>
    let segs := splitByteSlash tBytes
    let vLead :=
      match mkdirPVfsFuel 41 s.vfs cwdParts segs.dropLast with
      | .ok (vp, _) => vp
      | .error _ => s.vfs
    if isBare then
      match resolveVfsFuel 41 vLead cwdParts segs false with
      | .ok (.symlink symParts rawTarget) =>
        let baseCur := if startsWithSlashByte rawTarget then [] else symParts.dropLast
        resolveBareDanglingDest 40 vLead baseCur (splitByteSlash rawTarget)
      | _ =>
        match mkdirPVfsFuel 41 s.vfs cwdParts segs with
        | .ok (_, canonParts) => .ok (vLead, canonParts)
        | .error e => .error e
    else
      match mkdirPVfsFuel 41 s.vfs cwdParts segs with
      | .ok (_, canonParts) => .ok (vLead, canonParts)
      | .error e => .error e
  | .error _ => .error { kind := .commandFailed, message := s!"cannot create clone target '{target}'" }

private def copyReachableCommitNodes (dstCommits srcCommits : List CommitNode)
    (roots : List CommitId) : List CommitNode :=
  let dstSet : Std.TreeSet String compare :=
    dstCommits.foldl (fun st c => st.insert c.id.hex) {}
  let srcMap : Std.TreeMap String CommitNode compare :=
    srcCommits.foldl (fun mp c => mp.insert c.id.hex c) {}
  let initQueue := roots.foldl (fun (q, vis) r =>
    if dstSet.contains r.hex || vis.contains r.hex || !srcMap.contains r.hex then (q, vis)
    else (r.hex :: q, vis.insert r.hex)) ([], ({} : Std.TreeSet String compare))
  let rec bfs : Nat → List String → Std.TreeSet String compare → Std.TreeSet String compare
    | 0, _, vis => vis
    | _ + 1, [], vis => vis
    | fuel + 1, curHex :: rest, vis =>
      let parents :=
        match srcMap.get? curHex with
        | some node => node.parents
        | none => []
      let (rest', vis') := parents.foldl (fun (q, v) p =>
        if dstSet.contains p.hex || v.contains p.hex || !srcMap.contains p.hex then (q, v)
        else (p.hex :: q, v.insert p.hex)) (rest, vis)
      bfs fuel rest' vis'
  let wanted := bfs (srcCommits.length + 1) initQueue.1.reverse initQueue.2
  let missing := srcCommits.filter (fun c => wanted.contains c.id.hex)
  dstCommits ++ missing

/-- Pure `isRepo` model step. -/
def stepIsRepo (s : GitRepoState) (repoPath : String) : Except GitError Bool × GitRepoState :=
  match validateFsPathArg repoPath with
  | .error e => (.error e, s)
  | .ok () =>
    match resolveDirInVfs s repoPath with
    | .error e => (.error e, s)
    | .ok canonParts => (.ok (discoverRepoAtParts s canonParts).isSome, s)

/-- Pure `repoRoot` model step. -/
def stepRepoRoot (s : GitRepoState) (repoPath : String) : Except GitError String × GitRepoState :=
  match resolveCwdAndDiscover s repoPath with
  | .error e => (.error e, s)
  | .ok (_, wt?, _, _) =>
    match wt? with
    | none => (.error { kind := .notARepo, message := "this operation must be run in a work tree" }, s)
    | some wt =>
      match String.fromUTF8? wt.rootPath with
      | some str => (.ok str, s)
      | none => (.error { kind := .parseError, message := "invalid UTF-8 in repoRoot" }, s)

/-- Pure `commonDir` model step. -/
def stepCommonDir (s : GitRepoState) (repoPath : String) : Except GitError String × GitRepoState :=
  match resolveCwdAndDiscover s repoPath with
  | .error e => (.error e, s)
  | .ok (repo, _, _, _) =>
    match String.fromUTF8? repo.commonDir with
    | some str => (.ok str, s)
    | none => (.error { kind := .parseError, message := "invalid UTF-8 in commonDir" }, s)

/-- Pure `headCommit?` model step. -/
def stepHeadCommit (s : GitRepoState) (repoPath : String) :
    Except GitError (Option CommitId) × GitRepoState :=
  match resolveCwdAndDiscover s repoPath with
  | .error e => (.error e, s)
  | .ok (repo, wt?, _, _) =>
    match activeHeadSlot repo wt? with
    | some sl => (.ok (headCommitOfSymbolic repo sl.head), s)
    | none => (.error { kind := .notARepo, message := "missing worktree slot" }, s)

/-- Pure `headBranch?` model step. -/
def stepHeadBranch (s : GitRepoState) (repoPath : String) :
    Except GitError (Option RefName) × GitRepoState :=
  match resolveCwdAndDiscover s repoPath with
  | .error e => (.error e, s)
  | .ok (repo, wt?, _, _) =>
    match activeHeadSlot repo wt? with
    | some sl =>
      match sl.head with
      | .symbolic b => (.ok (some b), s)
      | .detached _ => (.ok none, s)
    | none => (.error { kind := .notARepo, message := "missing worktree slot" }, s)

/-- Pure `headState` model step. -/
def stepHeadState (s : GitRepoState) (repoPath : String) :
    Except GitError HeadState × GitRepoState :=
  match resolveCwdAndDiscover s repoPath with
  | .error e => (.error e, s)
  | .ok (repo, wt?, _, _) =>
    match activeHeadSlot repo wt? with
    | some sl => (.ok (toPublicHeadState repo sl.head), s)
    | none => (.error { kind := .notARepo, message := "missing worktree slot" }, s)

/-- Pure `revParseCommit` model step. -/
def stepRevParseCommit (s : GitRepoState) (repoPath rev : String) :
    Except GitError CommitId × GitRepoState :=
  match validateFsPathArg repoPath with
  | .error e => (.error e, s)
  | .ok () =>
    match parseSupportedRevSpec rev with
    | none => (.error { kind := .invalidInput, message := s!"invalid revision specification: '{rev}'" }, s)
    | some parsed =>
      match resolveCwdAndDiscover s repoPath with
      | .error e => (.error e, s)
      | .ok (repo, wt?, _, _) =>
        match activeHeadSlot repo wt? with
        | some sl => (resolveParsedRevInRepo repo sl parsed, s)
        | none => (.error { kind := .notARepo, message := "missing worktree slot" }, s)

/-- Pure `isAncestor` model step. -/
def stepIsAncestor (s : GitRepoState) (repoPath : String) (ancestor descendant : CommitId) :
    Except GitError Bool × GitRepoState :=
  match validateFsPathArg repoPath with
  | .error e => (.error e, s)
  | .ok () =>
    if !isValidCommitIdStr ancestor.hex || !isValidCommitIdStr descendant.hex then
      (.error { kind := .invalidRef, message := "invalid commit ID argument" }, s)
    else
      match resolveCwdAndDiscover s repoPath with
      | .error e => (.error e, s)
      | .ok (repo, _, _, _) =>
        match resolveCommitIdArg? repo ancestor, resolveCommitIdArg? repo descendant with
        | some ancCid, some descCid => (.ok (isAncestor repo ancCid descCid), s)
        | _, _ => (.error { kind := .invalidRef, message := "unknown commit in isAncestor" }, s)

/-- Pure `mergeBase?` model step. -/
def stepMergeBase (s : GitRepoState) (repoPath : String) (a b : CommitId) :
    Except GitError (Option CommitId) × GitRepoState :=
  match validateFsPathArg repoPath with
  | .error e => (.error e, s)
  | .ok () =>
    if !isValidCommitIdStr a.hex || !isValidCommitIdStr b.hex then
      (.error { kind := .invalidRef, message := "invalid commit ID argument" }, s)
    else
      match resolveCwdAndDiscover s repoPath with
      | .error e => (.error e, s)
      | .ok (repo, _, _, _) =>
        match resolveCommitIdArg? repo a, resolveCommitIdArg? repo b with
        | some cidA, some cidB => (.ok (mergeBase? repo cidA cidB), s)
        | _, _ => (.error { kind := .invalidRef, message := "unknown commit in mergeBase?" }, s)

/-- Pure `status` model step. -/
def stepStatus (s : GitRepoState) (repoPath : String) :
    Except GitError (Array StatusEntry) × GitRepoState :=
  match resolveCwdAndDiscover s repoPath with
  | .error e => (.error e, s)
  | .ok (repo, wt?, _, _) =>
    match wt? with
    | none => (.error { kind := .notARepo, message := "this operation must be run in a work tree" }, s)
    | some wt => (computeStatusEntries s repo wt, s)

/-- Pure `diffNameStatus` model step. -/
def stepDiffNameStatus (s : GitRepoState) (repoPath revA : String) (revB? : Option String)
    (paths : Array String) : Except GitError (Array DiffEntry) × GitRepoState :=
  match validateFsPathArg repoPath with
  | .error e => (.error e, s)
  | .ok () =>
    match parseSupportedRevSpec revA with
    | none => (.error { kind := .invalidInput, message := s!"invalid revision: '{revA}'" }, s)
    | some parsedA =>
      let parsedBRes : Except GitError (Option ParsedRev) :=
        match revB? with
        | none => .ok none
        | some rb =>
          match parseSupportedRevSpec rb with
          | some pb => .ok (some pb)
          | none => .error { kind := .invalidInput, message := s!"invalid revision: '{rb}'" }
      match parsedBRes with
      | .error e => (.error e, s)
      | .ok parsedB? =>
        if !paths.all isValidPathArg then
          (.error { kind := .invalidPath, message := "invalid diff path argument" }, s)
        else
          match resolveCwdAndDiscover s repoPath with
          | .error e =>
            if e.kind == .notARepo && (revB?.isSome || !paths.isEmpty) then
              (.error { kind := .commandFailed, message := e.message }, s)
            else
              (.error e, s)
          | .ok (repo, wt?, cwdRel?, _) =>
            (computeDiffEntries s repo wt? cwdRel? parsedA parsedB? paths, s)

/-- Pure `listWorktrees` model step. -/
def stepListWorktrees (s : GitRepoState) (repoPath : String) :
    Except GitError (Array WorktreeInfo) × GitRepoState :=
  match resolveCwdAndDiscover s repoPath with
  | .error e => (.error e, s)
  | .ok (repo, _, _, _) =>
    let res : Except GitError (Array WorktreeInfo) := do
      let mut out : Array WorktreeInfo := #[]
      for h : i in [0 : repo.worktrees.length] do
        let w := repo.worktrees[i]
        let pStr ←
          match String.fromUTF8? w.rootPath with
          | some str => .ok str
          | none => .error { kind := .parseError, message := "invalid UTF-8 in worktree path" }
        if repo.isBare && i == 0 then
          out := out.push { path := pStr, head? := none, branch? := none, isBare := true }
        else
          let wtParts := splitByteSlash w.rootPath
          let missingDir := i > 0 && !w.isLocked &&
            (!isSearchableDirAtParts s.vfs wtParts || (lookupNodeAtParts s.vfs (wtParts ++ [".git".toUTF8])).isNone)
          let (isPrun, pruneRsn) :=
            if w.isPrunable then (true, w.pruneReason)
            else if missingDir then (true, some "gitdir file points to non-existent location")
            else (false, none)
          match w.head with
          | .symbolic b =>
            out := out.push
              { path := pStr
                head? := findBranchCommit? repo b
                branch? := some b
                isBare := false
                isDetached := false
                isLocked := w.isLocked
                lockReason := w.lockReason
                isPrunable := isPrun
                pruneReason := pruneRsn }
          | .detached cid =>
            out := out.push
              { path := pStr
                head? := some cid
                branch? := none
                isBare := false
                isDetached := true
                isLocked := w.isLocked
                lockReason := w.lockReason
                isPrunable := isPrun
                pruneReason := pruneRsn }
      return out
    (res, s)

/-- Pure `showFile?` model step. -/
def stepShowFile (s : GitRepoState) (repoPath rev relPath : String) :
    Except GitError (Option ByteArray) × GitRepoState :=
  match validateFsPathArg repoPath with
  | .error e => (.error e, s)
  | .ok () =>
    match parseSupportedRevSpec rev with
    | none => (.error { kind := .invalidInput, message := s!"invalid revision: '{rev}'" }, s)
    | some parsed =>
      match validateRelRepoPath relPath with
      | .error e => (.error e, s)
      | .ok () =>
        match resolveCwdAndDiscover s repoPath with
        | .error e => (.error e, s)
        | .ok (repo, wt?, _, _) =>
          match activeHeadSlot repo wt? with
          | none => (.error { kind := .notARepo, message := "missing worktree slot" }, s)
          | some sl =>
            match resolveParsedRevInRepo repo sl parsed with
            | .error e => (.error e, s)
            | .ok cid =>
              let tree := treeOfCommit repo cid
              match lookupTreeEntry tree relPath.toUTF8 with
              | some entry =>
                match entry.kind with
                | .gitlink => (.ok none, s)
                | _ =>
                  if entry.bytes.size > 16777216 then
                    (.error { kind := .commandFailed, message := "process 'git' exceeded output byte limit" }, s)
                  else
                    (.ok (some entry.bytes), s)
              | none => (.ok none, s)

/-- Pure `init` model step. -/
def stepInit (s : GitRepoState) (path : String) (bare : Bool) (initialBranch? : Option RefName) :
    Except GitError Unit × GitRepoState :=
  match validateFsPathArg path with
  | .error e => (.error e, s)
  | .ok () =>
    let branchOk : Except GitError RefName :=
      match initialBranch? with
      | none => .ok s.defaultInitBranch
      | some b =>
        if isValidRefNameStr b.raw then .ok b
        else .error { kind := .invalidRef, message := s!"invalid initial branch name: '{b.raw}'" }
    match branchOk with
    | .error e => (.error e, s)
    | .ok initBr =>
      let pBytes := path.toUTF8
        let cwdParts := if startsWithSlashByte pBytes then [] else splitByteSlash s.processCwd
        let segs := splitByteSlash pBytes
        let targetDirRes : Except (GitError × VfsNode) (VfsNode × List ByteArray) :=
          match resolveVfsFuel 41 s.vfs cwdParts segs true with
          | .ok (.dir canonParts searchable _ _) =>
            if searchable then .ok (s.vfs, canonParts)
            else .error ({ kind := .commandFailed, message := "permission denied" }, s.vfs)
          | .ok _ => .error ({ kind := .commandFailed, message := "file exists" }, s.vfs)
          | .error .eloop => .error ({ kind := .commandFailed, message := "file exists" }, s.vfs)
          | .error .eacces => .error ({ kind := .commandFailed, message := "permission denied" }, s.vfs)
          | .error .enotdir => .error ({ kind := .commandFailed, message := "not a directory" }, s.vfs)
          | .error .enoent =>
            if segs.getLast? == some "..".toUTF8 || segs.getLast? == some ".".toUTF8 then
              let vPartial :=
                match mkdirPVfsFuel 41 s.vfs cwdParts segs.dropLast with
                | .ok (v', _) => v'
                | .error _ => s.vfs
              .error ({ kind := .commandFailed, message := s!"cannot mkdir {path}: File exists" }, vPartial)
            else
              match mkdirPVfsFuel 41 s.vfs cwdParts segs with
              | .ok (vNew, canonParts) =>
                if (lookupNodeAtParts s.vfs canonParts).isSome then
                  .error ({ kind := .commandFailed, message := s!"cannot mkdir {path}: File exists" }, vNew)
                else
                  .ok (vNew, canonParts)
              | .error e => .error (e, s.vfs)
        match targetDirRes with
        | .error (e, vErr) => (.error e, { s with vfs := vErr })
        | .ok (vfs1, canonParts) =>
          let canonPath := joinAbsByteParts canonParts
          let alreadyInit :=
            if bare then
              s.repos.any (fun r => r.commonDir == canonPath || (!r.isBare && match r.worktrees.head? with | some w => w.rootPath == canonPath | none => false))
            else
              s.repos.any (fun r => !r.isBare && (r.commonDir == joinPathsBytes canonPath ".git".toUTF8 || match r.worktrees.head? with | some w => w.rootPath == canonPath | none => false))
          if alreadyInit then
            (.ok (), s)
          else
            let (vfs2, commonDirBytes) :=
              if bare then
                match mkdirPVfsFuel 41 vfs1 canonParts ["refs".toUTF8] with
                | .ok (v, _) => (v, canonPath)
                | .error _ => (vfs1, canonPath)
              else
                match mkdirPVfsFuel 41 vfs1 canonParts [".git".toUTF8, "refs".toUTF8] with
                | .ok (v, _) => (v, joinPathsBytes canonPath ".git".toUTF8)
                | .error _ => (vfs1, joinPathsBytes canonPath ".git".toUTF8)
            let repo : RepoInstance :=
              { commonDir := commonDirBytes
                isBare := bare
                commits := []
                refs := []
                symRefs := []
                remotes := []
                worktrees := [{ rootPath := canonPath, head := .symbolic initBr }] }
            let repos' :=
              if s.repos.any (fun r => r.isBare && r.commonDir == canonPath) then repo :: s.repos
              else s.repos ++ [repo]
            (.ok (), { s with vfs := vfs2, repos := repos' })

private def resolveSourceHeadBranch? (srcRepo : RepoInstance) (activeSrcWt? : Option WorktreeSlot)
    (defaultInitBranch : RefName) (guessAll : Bool := true) : Option String :=
  let srcHeads := srcRepo.refs.filter (fun p => p.1.startsWith "refs/heads/")
  match activeSrcWt? with
  | some w =>
    match headCommitOfSymbolic srcRepo w.head with
    | some cid =>
      match w.head with
      | .symbolic b => some b.raw
      | .detached _ =>
        let sortedHeads := sortByBytes (·.1.toUTF8) srcHeads
        let matching := sortedHeads.filter (fun p => p.2 == cid)
        let matchHead? :=
          if guessAll then
            (matching.find? (fun p => p.1 == "refs/heads/" ++ defaultInitBranch.raw)) <|>
            (matching.find? (fun p => p.1 == "refs/heads/master")) <|>
            matching.head?
          else
            match matching with
            | [single] => some single
            | _ => none
        matchHead?.map (fun (rn, _) => String.ofList (rn.toList.drop 11))
    | none => none
  | none => none

/-- Pure `clone` model step. -/
def stepClone (s : GitRepoState) (source target : String) (opts : CloneOptions) :
    Except GitError Unit × GitRepoState :=
  match validateCloneEndpoint source, validateCloneEndpoint target with
  | .error e, _ => (.error e, s)
  | _, .error e => (.error e, s)
  | .ok (), .ok () =>
    if opts.depth? == some 0 then
      (.error { kind := .invalidInput, message := "clone depth must be positive" }, s)
    else
      let branchCheck : Except GitError Unit :=
        match opts.branch? with
        | none => .ok ()
        | some b =>
          if isValidRefNameStr b then .ok ()
          else .error { kind := .invalidRef, message := s!"invalid clone branch: '{b}'" }
      match branchCheck with
      | .error e => (.error e, s)
      | .ok () =>
        let finishClone (srcRepo : RepoInstance) (srcWt? : Option WorktreeSlot) (srcCanonBytes : ByteArray)
              (vParent : VfsNode) (dstParts : List ByteArray) (isFileUrl : Bool) :
              Except GitError Unit × GitRepoState :=
            let dstCanon := joinAbsByteParts dstParts
            let dstCommon := if opts.bare then dstCanon else joinPathsBytes dstCanon ".git".toUTF8
            let srcHeads := srcRepo.refs.filter (fun p => p.1.startsWith "refs/heads/")
            let srcTags := srcRepo.refs.filter (fun p => p.1.startsWith "refs/tags/")
            let activeSrcWt? := srcWt? <|> srcRepo.worktrees.head?
            let primarySrcBranch : RefName :=
              match activeSrcWt? with
              | some w =>
                match w.head with
                | .symbolic b => b
                | .detached _ => s.defaultInitBranch
              | none => s.defaultInitBranch
            let targetBranchChoice : Except GitError (Option (String × CommitId) × RefName × Bool) :=
              match opts.branch? with
              | some b =>
                match lookupFullRef srcRepo ("refs/heads/" ++ b) with
                | some cid => .ok (some ("refs/heads/" ++ b, cid), { raw := b }, false)
                | none =>
                  match lookupFullRef srcRepo ("refs/tags/" ++ b) with
                  | some cid => .ok (some ("refs/tags/" ++ b, cid), { raw := b }, true)
                  | none => .error { kind := .notFound, message := s!"remote branch '{b}' not found" }
              | none =>
                match activeSrcWt? with
                | some w =>
                  match headCommitOfSymbolic srcRepo w.head with
                  | some cid =>
                    match w.head with
                    | .symbolic b => .ok (some ("refs/heads/" ++ b.raw, cid), b, false)
                    | .detached _ =>
                      match resolveSourceHeadBranch? srcRepo activeSrcWt? s.defaultInitBranch true with
                      | some brName =>
                        .ok (some ("refs/heads/" ++ brName, cid), { raw := brName }, false)
                      | none =>
                        .ok (some ("HEAD", cid), primarySrcBranch, true)
                  | none => .ok (none, primarySrcBranch, false)
                | none => .ok (none, primarySrcBranch, false)
            match targetBranchChoice with
            | .error e => (.error e, { s with vfs := vParent })
            | .ok (checkedRef?, coBranch, isTagOrDetached) =>
              let effectiveSingleBranch := opts.singleBranch || opts.depth?.isSome
              let originHeadBranch? := resolveSourceHeadBranch? srcRepo activeSrcWt? s.defaultInitBranch true
              let rawCommits :=
                if isFileUrl then
                  match opts.depth? with
                  | some d =>
                    let extraTips :=
                      match checkedRef? with
                      | some (_, cid) => [cid]
                      | none => []
                    let tips :=
                      if effectiveSingleBranch then extraTips
                      else extraTips ++ (srcHeads ++ srcTags).map (·.2)
                    truncateCommitsDepth srcRepo.commits tips d
                  | none => srcRepo.commits
                else
                  srcRepo.commits
              let keptTags :=
                if isFileUrl && opts.depth?.isSome then
                  let rawSet : Std.TreeSet String compare :=
                    rawCommits.foldl (fun st c => st.insert c.id.hex) {}
                  srcTags.filter fun p => rawSet.contains p.2.hex
                else if isFileUrl && effectiveSingleBranch then
                  let branchReachRoots :=
                    match checkedRef? with
                    | some (_, cid) => [cid]
                    | none => []
                  let branchReachSet :=
                    reachableCommitHexSet { srcRepo with commits := rawCommits } branchReachRoots
                  srcTags.filter fun p => branchReachSet.contains p.2.hex
                else
                  srcTags
              let remoteUrlStr :=
                match String.fromUTF8? srcCanonBytes with
                | some u => u
                | none => source
              if opts.bare then
                let bareRefs :=
                  if effectiveSingleBranch then
                    if isTagOrDetached then keptTags
                    else
                      match checkedRef? with
                      | some (rn, cid) => [(rn, cid)] ++ keptTags
                      | none => keptTags
                  else
                    srcHeads ++ keptTags
                let commits :=
                  if isFileUrl then
                    let reachRoots :=
                      (match checkedRef? with | some (_, cid) => [cid] | none => []) ++ bareRefs.map (·.2)
                    let reachSet := reachableCommitHexSet { srcRepo with commits := rawCommits } reachRoots
                    rawCommits.filter (fun c => reachSet.contains c.id.hex)
                  else
                    rawCommits
                let vfs2 :=
                  match mkdirPVfsFuel 41 vParent [] (dstParts ++ ["refs".toUTF8]) with
                  | .ok (v, _) => v
                  | .error _ => vParent
                let bareHead : SymbolicHead :=
                  match checkedRef? with
                  | some (_, coCid) => if isTagOrDetached then .detached coCid else .symbolic coBranch
                  | none => .symbolic coBranch
                let newRepo : RepoInstance :=
                  { commonDir := dstCommon
                    isBare := true
                    commits := commits
                    refs := bareRefs
                    remotes := [{ name := "origin", url := remoteUrlStr, fetchSpecs := [] }]
                    worktrees := [{ rootPath := dstCanon, head := bareHead }] }
                (.ok (), { s with vfs := vfs2, repos := s.repos ++ [newRepo] })
              else
                let vfsGit :=
                  match mkdirPVfsFuel 41 vParent [] (dstParts ++ [".git".toUTF8, "refs".toUTF8]) with
                  | .ok (v, _) => v
                  | .error _ => vParent
                match checkedRef? with
                | none =>
                  let remoteHeads :=
                    if effectiveSingleBranch then []
                    else
                      srcHeads.map fun (rn, cid) =>
                        ("refs/remotes/origin/" ++ String.ofList (rn.toList.drop 11), cid)
                  let allRefs := keptTags ++ remoteHeads
                  let commits :=
                    if isFileUrl then
                      let reachSet := reachableCommitHexSet { srcRepo with commits := rawCommits } (allRefs.map (·.2))
                      rawCommits.filter (fun c => reachSet.contains c.id.hex)
                    else
                      rawCommits
                  let newRepo : RepoInstance :=
                    { commonDir := dstCommon
                      isBare := false
                      commits := commits
                      refs := allRefs
                      remotes := [{ name := "origin", url := remoteUrlStr, fetchSpecs := if effectiveSingleBranch then [] else ["+refs/heads/*:refs/remotes/origin/*"] }]
                      worktrees := [{ rootPath := dstCanon, head := .symbolic coBranch }]
                      branchRemotes := [(coBranch.raw, "origin", "refs/heads/" ++ coBranch.raw)] }
                  (.ok (), { s with vfs := vfsGit, repos := s.repos ++ [newRepo] })
                | some (_, coCid) =>
                  let remoteHeads :=
                    if effectiveSingleBranch && !isTagOrDetached then
                      [("refs/remotes/origin/" ++ coBranch.raw, coCid)]
                    else if effectiveSingleBranch && isTagOrDetached then
                      []
                    else
                      srcHeads.map fun (rn, cid) =>
                        ("refs/remotes/origin/" ++ String.ofList (rn.toList.drop 11), cid)
                  let localRefs :=
                    if isTagOrDetached then keptTags
                    else [("refs/heads/" ++ coBranch.raw, coCid)] ++ keptTags
                  let allRefs := localRefs ++ remoteHeads
                  let originTarget? := originHeadBranch?
                  let symRefs :=
                    match originTarget? with
                    | some tb =>
                      let originRef := "refs/remotes/origin/" ++ tb
                      if remoteHeads.any (fun p => p.1 == originRef) then
                        [("refs/remotes/origin/HEAD", originRef)]
                      else []
                    | none => []
                  let upstreams :=
                    if isTagOrDetached then []
                    else [(coBranch.raw, "refs/remotes/origin/" ++ coBranch.raw)]
                  let commits :=
                    if isFileUrl then
                      let reachSet := reachableCommitHexSet { srcRepo with commits := rawCommits } (coCid :: allRefs.map (·.2))
                      rawCommits.filter (fun c => reachSet.contains c.id.hex)
                    else
                      rawCommits
                  let coTree := treeOfCommit srcRepo coCid
                  let vfsOut := writeTreeToVfs vfsGit dstParts coTree
                  let headVal : SymbolicHead := if isTagOrDetached then .detached coCid else .symbolic coBranch
                  let fetchSpecs :=
                    if effectiveSingleBranch then
                      match checkedRef? with
                      | some (rn, _) =>
                        if rn.startsWith "refs/tags/" then [s!"+{rn}:{rn}"]
                        else if isTagOrDetached then []
                        else [s!"+refs/heads/{coBranch.raw}:refs/remotes/origin/{coBranch.raw}"]
                      | none => []
                    else ["+refs/heads/*:refs/remotes/origin/*"]
                  let newRepo : RepoInstance :=
                    { commonDir := dstCommon
                      isBare := false
                      commits := commits
                      refs := allRefs
                      symRefs := symRefs
                      remotes := [{ name := "origin", url := remoteUrlStr, fetchSpecs := fetchSpecs }]
                      worktrees := [{ rootPath := dstCanon, head := headVal, index := { entries := sortByBytes (·.1) coTree } }]
                      branchUpstreams := upstreams
                      branchRemotes := if isTagOrDetached then [] else [(coBranch.raw, "origin", "refs/heads/" ++ coBranch.raw)] }
                  (.ok (), { s with vfs := vfsOut, repos := s.repos ++ [newRepo] })
          match isLocalFileSource? source with
          | none =>
            match checkCloneTargetDest s target opts.bare with
            | .error e => (.error e, s)
            | .ok (vParent, _) => (.error { kind := .commandFailed, message := s!"transport not allowed for '{source}'" }, { s with vfs := vParent })
          | some (false, localSrc) =>
            match findExactSourceRepo s localSrc with
            | .error e =>
              if e.kind == .commandFailed then
                match checkCloneTargetDest s target opts.bare with
                | .error ce => (.error ce, s)
                | .ok (vParent, _) => (.error e, { s with vfs := vParent })
              else
                (.error e, s)
            | .ok (srcRepo, srcWt?, srcCanonBytes) =>
              match checkCloneTargetDest s target opts.bare with
              | .error e => (.error e, s)
              | .ok (vParent, dstParts) => finishClone srcRepo srcWt? srcCanonBytes vParent dstParts false
          | some (true, fileSrc) =>
            match checkCloneTargetDest s target opts.bare with
            | .error e => (.error e, s)
            | .ok (vParent, dstParts) =>
              if fileSrc.isEmpty then
                (.error { kind := .commandFailed, message := "no path specified" }, { s with vfs := vParent })
              else
                match findExactSourceRepo s fileSrc with
                | .ok (srcRepo, srcWt?, srcCanonBytes) => finishClone srcRepo srcWt? srcCanonBytes vParent dstParts true
                | .error e =>
                  let fBytes := fileSrc.toUTF8
                  let fCwd := if startsWithSlashByte fBytes then [] else splitByteSlash s.processCwd
                  let fNorm := normalizeDotDotParts fCwd (splitByteSlash fBytes)
                  let isSelfTarget := fNorm == dstParts || (!opts.bare && fNorm == dstParts ++ [".git".toUTF8])
                  if isSelfTarget then
                    let selfCanon := joinAbsByteParts dstParts
                    let selfCommon := if opts.bare then selfCanon else joinPathsBytes selfCanon ".git".toUTF8
                    let selfRepo : RepoInstance :=
                      { commonDir := selfCommon
                        isBare := opts.bare
                        worktrees := [{ rootPath := selfCanon, head := .symbolic s.defaultInitBranch }] }
                    finishClone selfRepo selfRepo.worktrees.head? (joinAbsByteParts fNorm) vParent dstParts true
                  else
                    (.error { kind := .commandFailed, message := e.message }, { s with vfs := vParent })

/-- Pure `add` model step. -/
def stepAdd (s : GitRepoState) (repoPath : String) (paths : Array String) (all : Bool) :
    Except GitError Unit × GitRepoState :=
  match validateFsPathArg repoPath with
  | .error e => (.error e, s)
  | .ok () =>
    if !all && paths.isEmpty then
      (.error { kind := .invalidInput, message := "add requires non-empty paths or all = true" }, s)
    else if !paths.all isValidPathArg then
      (.error { kind := .invalidPath, message := "invalid path passed to git add" }, s)
    else
      match resolveCwdAndDiscover s repoPath with
      | .error e => (.error e, s)
      | .ok (repo, wt?, cwdRel?, _) =>
        match wt? with
        | none => (.error { kind := .notARepo, message := "this operation must be run in a work tree" }, s)
        | some wt =>
          let rootParts := splitByteSlash wt.rootPath
          let wtNode := (lookupNodeAtParts s.vfs rootParts).getD VfsNode.emptyDir
          let fastDisk := noSpecialDirsUnderNode wtNode
          let diskEntriesAll := collectVfsFilesUnder s.vfs rootParts
          let preservedGitlinks := wt.index.entries.filter fun (p, e) =>
            e.kind == .gitlink && existsVfsRelDir s.vfs rootParts p
          let isPreservedGitlinkPath (p : ByteArray) : Bool :=
            !preservedGitlinks.isEmpty && preservedGitlinks.any fun (gp, _) => p == gp || isPathPrefixBytes gp p
          let isProtectedByEacces (p : ByteArray) : Bool :=
            if fastDisk then false
            else
              match lookupVfsRelEntryChecked s.vfs rootParts p with
              | .error .eacces => true
              | _ => false
          if all && paths.isEmpty then
            let keptEacces :=
              if fastDisk then [] else wt.index.entries.filter fun e => isProtectedByEacces e.1
            let keptEaccesSet := buildByteSet (keptEacces.map (·.1))
            let diskFiltered := diskEntriesAll.filter fun (p, _) =>
              !keptEaccesSet.contains p && !isPreservedGitlinkPath p
            let merged := sortByBytes (·.1) (keptEacces ++ diskFiltered ++ preservedGitlinks)
            let keptConflicts :=
              if fastDisk then [] else wt.index.conflicts.filter fun c => isProtectedByEacces c.path
            let idx' : IndexState :=
              { entries := merged
                conflicts := keptConflicts
                hasMergeHead := wt.index.hasMergeHead
                mergeParents := wt.index.mergeParents }
            let repo' := updateWorktreeInRepo repo wt.rootPath fun slot => { slot with index := idx' }
            (.ok (), { s with repos := updateRepoInList s.repos repo.commonDir (fun _ => repo') })
          else
            let normPairs? :=
              match String.fromUTF8? wt.rootPath with
              | some wtRootStr => normalizeCliPathspecs? wtRootStr cwdRel? paths
              | none => none
            match normPairs? with
            | none =>
              (.error { kind := .commandFailed, message := "unsupported or outside-repository pathspec" }, s)
            | some pairs =>
              let filters := pairs.map Prod.snd
              let isInsideTrackedGitlink (q : ByteArray) : Bool :=
                wt.index.entries.any fun (gp, ge) => ge.kind == .gitlink && q != gp && isPathPrefixBytes gp q
              let badFilter? := pairs.find? fun (_, f) =>
                match f with
                | .allWorktree => false
                | .exactOrDir q _ => hasSymlinkAncestorInVfs s.vfs rootParts (splitByteSlash q) || isInsideTrackedGitlink q
              match badFilter? with
              | some (badRaw, _) =>
                (.error { kind := .commandFailed, message := s!"invalid pathspec '{badRaw}' (beyond symlink or in submodule)" }, s)
              | none =>
                let unmatched? := pairs.find? fun (_, f) =>
                  match f with
                  | .allWorktree => false
                  | .exactOrDir q false =>
                    !existsVfsRelAny s.vfs rootParts q &&
                    !wt.index.entries.any (fun p => isPathPrefixBytes q p.1) &&
                    !wt.index.conflicts.any (fun c => isPathPrefixBytes q c.path)
                  | .exactOrDir q true =>
                    !existsVfsRelDir s.vfs rootParts q &&
                    !wt.index.entries.any (fun p => (stripPathPrefixBytes q p.1).isSome) &&
                    !wt.index.conflicts.any (fun c => (stripPathPrefixBytes q c.path).isSome)
                match unmatched? with
                | some (missingRaw, _) =>
                  (.error { kind := .notFound, message := s!"pathspec '{missingRaw}' did not match any files" }, s)
                | none =>
                  let matchesFilter (p : ByteArray) : Bool :=
                    matchesAnyNormPathFilter filters p
                  let matchesDirFilter (p : ByteArray) : Bool :=
                    matchesAnyNormDirFilter filters p
                  let preservedMatching := preservedGitlinks.filter fun (gp, _) => matchesDirFilter gp
                  let addedFromDisk := diskEntriesAll.filter fun (p, _) =>
                    matchesFilter p && !isPreservedGitlinkPath p
                  let stagedNew := addedFromDisk ++ preservedMatching
                  let stagedPaths := stagedNew.map (·.1)
                  let stagedPrefixSet := buildTrackedPrefixSet stagedPaths
                  let stagedExactSet := buildByteSet stagedPaths
                  let collidesDF (p : ByteArray) : Bool :=
                    stagedExactSet.contains p ||
                    stagedPrefixSet.contains p ||
                    (let rec anyStrictPref (rev : List ByteArray) : List ByteArray → Bool
                      | [] | [_] => false
                      | seg :: rest =>
                        let rev' := seg :: rev
                        stagedExactSet.contains (joinRelByteParts rev'.reverse) || anyStrictPref rev' rest
                     anyStrictPref [] (splitByteSlash p))
                  let keptIdx := wt.index.entries.filter fun p =>
                    if isProtectedByEacces p.1 then true
                    else
                      let matched := if p.2.kind == .gitlink then matchesDirFilter p.1 else matchesFilter p.1
                      !matched && !collidesDF p.1
                  let keptIdxSet := buildByteSet (keptIdx.map (·.1))
                  let stagedNoDup := stagedNew.filter fun e => !keptIdxSet.contains e.1
                  let newEntries := sortByBytes (·.1) (keptIdx ++ stagedNoDup)
                  let newConflicts := wt.index.conflicts.filter fun c =>
                    if isProtectedByEacces c.path then true
                    else !matchesFilter c.path && !collidesDF c.path
                  let idx' : IndexState :=
                    { entries := newEntries
                      conflicts := newConflicts
                      hasMergeHead := wt.index.hasMergeHead
                      mergeParents := wt.index.mergeParents }
                  let repo' := updateWorktreeInRepo repo wt.rootPath fun slot => { slot with index := idx' }
                  (.ok (), { s with repos := updateRepoInList s.repos repo.commonDir (fun _ => repo') })

private def trimRightWsChars (cs : List Char) : List Char :=
  (cs.reverse.dropWhile (fun c => c == ' ' || c == '\t' || c == '\r')).reverse

/-- Normalize commit message lines matching Git's default `-m` (`--cleanup=whitespace`) behavior. -/
def cleanCommitMessageWhitespace (msg : String) : String :=
  let rawLines := (msg.splitOn "\n").map (fun ln => String.ofList (trimRightWsChars ln.toList))
  let trimmedLead := rawLines.dropWhile (·.isEmpty)
  let trimmedBoth := (trimmedLead.reverse.dropWhile (·.isEmpty)).reverse
  let collapsed := trimmedBoth.foldl
    (fun (acc : List String) ln =>
      if ln.isEmpty && acc.getLast? == some "" then acc else acc ++ [ln])
    []
  if collapsed.isEmpty then ""
  else "\n".intercalate collapsed ++ "\n"

/-- Return `true` iff `c` is a lowercase ASCII hex digit. -/
def isHexDigitLower (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- Return `true` iff `s` is an abbreviated 4..39-char lowercase hex commit prefix. -/
def isShortHexSha (s : String) : Bool :=
  let cs := s.toList
  cs.length ≥ 4 && cs.length < 40 && cs.all isHexDigitLower

/-- Return `true` iff `s` is a transient Git pseudo-ref (`ORIG_HEAD`, `FETCH_HEAD`, `MERGE_HEAD`, `CHERRY_PICK_HEAD`). -/
def isSpecialGitPseudoRef (s : String) : Bool :=
  s == "ORIG_HEAD" || s == "FETCH_HEAD" || s == "MERGE_HEAD" || s == "CHERRY_PICK_HEAD"

/-- Return `true` iff `rev` uses an extended revision form whose resolution is modeled relationally. -/
def isExtendedRevSpec (rev : String) : Bool :=
  match parseSupportedRevSpec rev with
  | none => true
  | some parsed =>
    match parsed.base with
    | .head | .commitId _ => false
    | .ref name => isShortHexSha name || isSpecialGitPseudoRef name

/-- Find all remote-tracking refs matching `refs/remotes/<remote>/<branch>` in `repo.refs`. -/
def findRemoteDwimMatches (repo : RepoInstance) (branch : String) :
    List (String × String × CommitId) :=
  let knownMatches := repo.remotes.filterMap fun rm =>
    let fullRef := s!"refs/remotes/{rm.name}/{branch}"
    (lookupFullRef repo fullRef).map (rm.name, fullRef, ·)
  let extraMatches := repo.refs.filterMap fun (fullRef, cid) =>
    if fullRef.startsWith "refs/remotes/" && fullRef.endsWith ("/" ++ branch) then
      let body := String.ofList (fullRef.toList.drop 13)
      let sufLen := branch.toList.length + 1
      if body.toList.length > sufLen then
        let remName := String.ofList (body.toList.take (body.toList.length - sufLen))
        if !remName.contains '/' && !knownMatches.any (fun p => p.2.1 == fullRef) then
          some (remName, fullRef, cid)
        else none
      else none
    else none
  knownMatches ++ extraMatches

/-- Pure `commit` model step given an explicit `newId` witness (supplied by real `git` in differential fuzzing). -/
def stepCommitWithId (s : GitRepoState) (repoPath : String) (opts : CommitOptions)
    (newId? : Option CommitId := none) : Except GitError CommitId × GitRepoState :=
  match validateFsPathArg repoPath with
  | .error e => (.error e, s)
  | .ok () =>
    match validateCommitOptions opts with
    | .error e => (.error e, s)
    | .ok () =>
      match resolveCwdAndDiscover s repoPath with
      | .error e => (.error e, s)
      | .ok (repo, wt?, _, _) =>
        match wt? with
        | none => (.error { kind := .notARepo, message := "this operation must be run in a work tree" }, s)
        | some wt =>
            if !wt.index.conflicts.isEmpty then
              (.error { kind := .conflict, message := "unmerged files prevent commit" }, s)
            else
              let headCid? := headCommitOfSymbolic repo wt.head
              let headTree :=
                match headCid? with
                | some cid => treeOfCommit repo cid
                | none => []
              let sortedIdx := sortByBytes (·.1) wt.index.entries
              if sortedIdx == sortByBytes (·.1) headTree && !opts.allowEmpty && !wt.index.hasMergeHead then
                (.error { kind := .nothingToCommit, message := "nothing to commit, working tree clean" }, s)
              else
                let cleanedMsg := cleanCommitMessageWhitespace opts.message
                if cleanedMsg.isEmpty then
                  (.error { kind := .commandFailed, message := "Aborting commit due to empty commit message." }, s)
                else
                  let cid := newId?.getD (freshSyntheticCommitId repo)
                  let extraParents :=
                    if wt.index.hasMergeHead then
                      wt.index.mergeParents.filter (fun p => headCid? != some p)
                    else []
                  let parents :=
                    match headCid? with
                    | some p => p :: extraParents
                    | none => extraParents
                  let commits' :=
                    if hasCommit repo cid then repo.commits
                    else repo.commits ++ [{ id := cid, parents := parents, tree := sortedIdx, message := cleanedMsg }]
                  let (refs', head') :=
                    match wt.head with
                    | .symbolic b => (setRefInList repo.refs ("refs/heads/" ++ b.raw) cid, .symbolic b)
                    | .detached _ => (repo.refs, .detached cid)
                  let repo1 := { repo with commits := commits', refs := refs' }
                  let repo2 := updateWorktreeInRepo repo1 wt.rootPath fun slot =>
                    { slot with head := head', index := { slot.index with hasMergeHead := false, mergeParents := [] } }
                  (.ok cid, { s with repos := updateRepoInList s.repos repo.commonDir (fun _ => repo2) })

private def matchConfiguredRemoteTracking? (repo : RepoInstance) (resolvedFull : String) :
    Option (String × String × String) :=
  if !resolvedFull.startsWith "refs/remotes/" then none
  else
    repo.remotes.findSome? fun rm =>
      (rm.fetchSpecs.filterMap parseFetchRefspec?).findSome? fun sp =>
        if sp.isGlob then
          let dstPfx := sp.dst?.getD sp.src
          match matchSingleGlob? dstPfx sp.dstSuffix resolvedFull with
          | some sfx =>
            let srcRef := sp.src ++ sfx ++ sp.srcSuffix
            if srcRef.startsWith "refs/heads/" then some (resolvedFull, rm.name, srcRef) else none
          | none => none
        else
          match sp.dst? with
          | some dstRaw =>
            let dstFull := qualifyFetchDstRef dstRaw
            if dstFull == resolvedFull && sp.src.startsWith "refs/heads/" then
              some (resolvedFull, rm.name, sp.src)
            else none
          | none => none

private def autoUpstreamOfParsedRef (repo : RepoInstance) (parsed : ParsedRev) :
    Option (String × String × String) :=
  let bareName? : Option String :=
    match parsed with
    | { base := .ref rName, steps := [] } => some rName
    | { base := .commitId cid, steps := [] } => some cid.hex
    | _ => none
  match bareName? with
  | none => none
  | some rName =>
    let hits := dedupStringsLoop [] ((dwimRefCandidates rName).filter fun full =>
      full.startsWith "refs/" && (lookupFullRef repo full).isSome)
    match hits with
    | [full] =>
      let resolvedFull :=
        match repo.symRefs.find? (fun p => p.1 == full) with
        | some (_, tgt) => tgt
        | none => full
      matchConfiguredRemoteTracking? repo resolvedFull
    | _ => none

private def setBranchUpstream (ups : List (String × String)) (br : String) (upRef : String) :
    List (String × String) :=
  let rest := ups.filter (fun p => p.1 != br)
  rest ++ [(br, upRef)]

private def setBranchRemote (rems : List (String × String × String)) (br remName mergeRef : String) :
    List (String × String × String) :=
  let rest := rems.filter (fun p => p.1 != br)
  rest ++ [(br, remName, mergeRef)]

/-- Pure `createBranch` model step. -/
def stepCreateBranch (s : GitRepoState) (repoPath : String) (branch : RefName)
    (startPoint? : Option String) (force : Bool) : Except GitError Unit × GitRepoState :=
  match validateFsPathArg repoPath with
  | .error e => (.error e, s)
  | .ok () =>
    if !isValidRefNameStr branch.raw then
      (.error { kind := .invalidRef, message := s!"invalid branch name: '{branch.raw}'" }, s)
    else
      let spRes : Except GitError ParsedRev :=
        match startPoint? with
        | none => .ok { base := .head, steps := [] }
        | some sp =>
          match parseSupportedRevSpec sp with
          | some pr => .ok pr
          | none => .error { kind := .invalidInput, message := s!"invalid startPoint: '{sp}'" }
      match spRes with
      | .error e => (.error e, s)
      | .ok parsedSp =>
        match resolveCwdAndDiscover s repoPath with
        | .error e => (.error e, s)
        | .ok (repo, wt?, _, _) =>
          match activeHeadSlot repo wt? with
          | none => (.error { kind := .notARepo, message := "missing worktree slot" }, s)
          | some sl =>
            let fullRef := "refs/heads/" ++ branch.raw
            let existsPreCheck : Except GitError Unit :=
              if (lookupFullRef repo fullRef).isSome then
                if !force then
                  .error { kind := .alreadyExists, message := s!"a branch named '{branch.raw}' already exists" }
                else if isBranchCheckedOutAnywhere repo branch then
                  .error { kind := .branchInUse, message := s!"cannot force update the branch '{branch.raw}' used by worktree" }
                else
                  .ok ()
              else .ok ()
            match existsPreCheck with
            | .error e => (.error e, s)
            | .ok () =>
                let implicitHeadAmbiguous :=
                  match startPoint?, sl.head with
                  | none, .symbolic curBr =>
                    isAmbiguousBareRef repo { base := .ref curBr.raw, steps := [] }
                  | _, _ => false
                if (startPoint?.isSome && isAmbiguousBareRef repo parsedSp true) || implicitHeadAmbiguous then
                  (.error { kind := .invalidRef, message := s!"ambiguous object name: '{startPoint?.getD ""}'" }, s)
                else
                  let resolvedSp : Except GitError CommitId :=
                    match parsedSp with
                    | { base := .commitId cid, steps := [] } =>
                      match resolveDwimRefCommit? repo cid.hex with
                      | some c => .ok c
                      | none => resolveParsedRevInRepo repo sl parsedSp
                    | _ => resolveParsedRevInRepo repo sl parsedSp
                  match resolvedSp with
                  | .error e => (.error e, s)
                  | .ok targetCid =>
                    if hasRefDFConflict repo fullRef then
                      (.error { kind := .commandFailed, message := s!"cannot lock ref '{fullRef}': D/F conflict" }, s)
                    else
                      let (ups', rems') :=
                        match autoUpstreamOfParsedRef repo parsedSp with
                        | some (upRef, remName, mergeRef) =>
                          (setBranchUpstream repo.branchUpstreams branch.raw upRef,
                           setBranchRemote repo.branchRemotes branch.raw remName mergeRef)
                        | none => (repo.branchUpstreams, repo.branchRemotes)
                      let repo' :=
                        { repo with
                          refs := setRefInList repo.refs fullRef targetCid
                          branchUpstreams := ups'
                          branchRemotes := rems' }
                      (.ok (), { s with repos := updateRepoInList s.repos repo.commonDir (fun _ => repo') })

/-- Pure `deleteBranch` model step. -/
def stepDeleteBranch (s : GitRepoState) (repoPath : String) (branch : RefName) (force : Bool) :
    Except GitError Unit × GitRepoState :=
  match validateFsPathArg repoPath with
  | .error e => (.error e, s)
  | .ok () =>
    if !isValidRefNameStr branch.raw then
      (.error { kind := .invalidRef, message := s!"invalid branch name: '{branch.raw}'" }, s)
    else
      match resolveCwdAndDiscover s repoPath with
      | .error e => (.error e, s)
      | .ok (repo, wt?, _, _) =>
        if isBranchCheckedOutAnywhere repo branch then
          (.error { kind := .branchInUse, message := s!"cannot delete branch '{branch.raw}' used by worktree" }, s)
        else
          let fullRef := "refs/heads/" ++ branch.raw
          match lookupFullRef repo fullRef with
          | none => (.error { kind := .notFound, message := s!"branch '{branch.raw}' not found" }, s)
          | some branchCid =>
            let upCid? : Option CommitId :=
              match repo.branchUpstreams.find? (fun p => p.1 == branch.raw) with
              | some (_, upRef) => lookupFullRef repo upRef
              | none => none
            let merged :=
              match upCid? with
              | some uc => isAncestor repo branchCid uc
              | none =>
                match activeHeadSlot repo wt? with
                | some sl =>
                  match headCommitOfSymbolic repo sl.head with
                  | some hc => isAncestor repo branchCid hc
                  | none => false
                | none => false
            if !force && !merged then
              (.error { kind := .commandFailed, message := s!"the branch '{branch.raw}' is not fully merged" }, s)
            else
              let ups' := repo.branchUpstreams.filter (fun p => p.1 != branch.raw)
              let rems' := repo.branchRemotes.filter (fun p => p.1 != branch.raw)
              let repo' := { repo with refs := eraseRefInList repo.refs fullRef, branchUpstreams := ups', branchRemotes := rems' }
              (.ok (), { s with repos := updateRepoInList s.repos repo.commonDir (fun _ => repo') })

/-- Pure `checkout` model step. -/
def stepCheckout (s : GitRepoState) (repoPath : String) (target : CheckoutTarget) (force : Bool) :
    Except GitError Unit × GitRepoState :=
  match validateFsPathArg repoPath with
  | .error e => (.error e, s)
  | .ok () =>
    let argCheck : Except GitError Unit :=
      match target with
      | .branch b =>
        if isValidRefNameStr b.raw then .ok ()
        else .error { kind := .invalidRef, message := s!"invalid branch name: '{b.raw}'" }
      | .commit cid =>
        if isValidCommitIdStr cid.hex then .ok ()
        else .error { kind := .invalidRef, message := s!"invalid commit ID: '{cid.hex}'" }
      | .ref spec =>
        if (parseSupportedRevSpec spec).isSome then .ok ()
        else .error { kind := .invalidInput, message := s!"invalid revision: '{spec}'" }
    match argCheck with
    | .error e => (.error e, s)
    | .ok () =>
      match resolveCwdAndDiscover s repoPath with
      | .error e => (.error e, s)
      | .ok (repo, wt?, _, _) =>
        match wt? with
        | none => (.error { kind := .notARepo, message := "this operation must be run in a work tree" }, s)
        | some wt =>
          let targetRes : Except GitError (SymbolicHead × CommitId × Option (String × CommitId × String × String)) :=
            match target with
            | .branch b =>
              match findBranchCommit? repo b with
              | some cid =>
                if isBranchInUseElsewhere repo wt.rootPath b && wt.head != .symbolic b then
                  .error { kind := .branchInUse, message := s!"'{b.raw}' is already used by worktree" }
                else
                  .ok (.symbolic b, cid, none)
              | none =>
                match findRemoteDwimMatches repo b.raw with
                | [(remName, upRef, cid)] =>
                  .ok (.symbolic b, cid, some ("refs/heads/" ++ b.raw, cid, remName, upRef))
                | _ :: _ :: _ =>
                  .error { kind := .invalidRef, message := s!"'{b.raw}' matched multiple remote tracking branches" }
                | [] =>
                  match resolveDwimRefCommit? repo b.raw with
                  | some cid => .ok (.detached cid, cid, none)
                  | none => .error { kind := .invalidRef, message := s!"invalid reference: {b.raw}" }
            | .commit cid =>
              match findBranchCommit? repo { raw := cid.hex } with
              | some bCid => .ok (.detached bCid, bCid, none)
              | none =>
                match resolveCommitIdArg? repo cid with
                | some rCid => .ok (.detached rCid, rCid, none)
                | none => .error { kind := .invalidRef, message := s!"unknown commit '{cid.hex}'" }
            | .ref spec =>
              match parseSupportedRevSpec spec with
              | none => .error { kind := .invalidInput, message := s!"invalid revision: '{spec}'" }
              | some parsed =>
                if spec == "HEAD" || spec == "@" then
                  match resolveParsedRevInRepo repo wt parsed with
                  | .error e => .error e
                  | .ok cid => .ok (wt.head, cid, none)
                else if isValidRefNameStr spec then
                  let br : RefName := { raw := spec }
                  match findBranchCommit? repo br with
                  | some bCid =>
                    if isBranchInUseElsewhere repo wt.rootPath br && wt.head != .symbolic br then
                      .error { kind := .branchInUse, message := s!"'{spec}' is already used by worktree" }
                    else
                      .ok (.symbolic br, bCid, none)
                  | none =>
                    match findRemoteDwimMatches repo spec with
                    | [(remName, upRef, cid)] =>
                      .ok (.symbolic br, cid, some ("refs/heads/" ++ spec, cid, remName, upRef))
                    | _ :: _ :: _ =>
                      .error { kind := .invalidRef, message := s!"'{spec}' matched multiple remote tracking branches" }
                    | [] =>
                      match resolveParsedRevInRepo repo wt parsed with
                      | .error e => .error e
                      | .ok cid => .ok (.detached cid, cid, none)
                else
                  match resolveParsedRevInRepo repo wt parsed with
                  | .error e => .error e
                  | .ok cid => .ok (.detached cid, cid, none)
          match targetRes with
          | .error e => (.error e, s)
          | .ok (newHead, newCid, dwimCreate?) =>
            if !force && !wt.index.conflicts.isEmpty then
              (.error { kind := .conflict, message := "you need to resolve your current index first" }, s)
            else
              let oldTree :=
                match headCommitOfSymbolic repo wt.head with
                | some cid => treeOfCommit repo cid
                | none => []
              let newTree := treeOfCommit repo newCid
              match applyTwoTreeCheckoutWithPerm s.vfs wt oldTree newTree force s.repos with
              | .error e => (.error e, s)
              | .ok (vfs', idx', hadPermErr) =>
                let repo0 :=
                  match dwimCreate? with
                  | none => repo
                  | some (fullRef, cid, remName, upRef) =>
                    let brName := match newHead with | .symbolic b => b.raw | .detached _ => ""
                    { repo with
                      refs := setRefInList repo.refs fullRef cid
                      branchUpstreams := setBranchUpstream repo.branchUpstreams brName upRef
                      branchRemotes := setBranchRemote repo.branchRemotes brName remName ("refs/heads/" ++ brName) }
                let repo' := updateWorktreeInRepo repo0 wt.rootPath fun slot =>
                  { slot with head := newHead, index := idx' }
                let overwritten := collectOverwrittenDirPaths s.vfs (splitByteSlash wt.rootPath) newTree
                let repos1 := pruneReposUnderPaths repo.commonDir overwritten s.repos
                let s' := { s with vfs := vfs', repos := updateRepoInList repos1 repo.commonDir (fun _ => repo') }
                if hadPermErr then
                  (.error { kind := .commandFailed, message := "unable to update working tree: permission denied" }, s')
                else
                  (.ok (), s')

/-- Pure `switch` model step. -/
def stepSwitch (s : GitRepoState) (repoPath : String) (branch : RefName)
    (create : Bool) (startPoint? : Option String) (force : Bool) :
    Except GitError Unit × GitRepoState :=
  match validateFsPathArg repoPath with
  | .error e => (.error e, s)
  | .ok () =>
    if !isValidRefNameStr branch.raw then
      (.error { kind := .invalidRef, message := s!"invalid branch name: '{branch.raw}'" }, s)
    else if !create && startPoint?.isSome then
      (.error { kind := .invalidInput, message := "switch startPoint requires create = true" }, s)
    else
      let spRes : Except GitError (Option ParsedRev) :=
        match startPoint? with
        | none => .ok none
        | some sp =>
          match parseSupportedRevSpec sp with
          | some pr => .ok (some pr)
          | none => .error { kind := .invalidInput, message := s!"invalid startPoint: '{sp}'" }
      match spRes with
      | .error e => (.error e, s)
      | .ok parsedSp? =>
        match resolveCwdAndDiscover s repoPath with
        | .error e => (.error e, s)
        | .ok (repo, wt?, _, _) =>
          match wt? with
          | none => (.error { kind := .notARepo, message := "this operation must be run in a work tree" }, s)
          | some wt =>
            if !create then
              let swTargetRes : Except GitError (CommitId × Option (String × CommitId × String × String)) :=
                match findBranchCommit? repo branch with
                | some c => .ok (c, none)
                | none =>
                  match findRemoteDwimMatches repo branch.raw with
                  | [(remName, upRef, cid)] =>
                    .ok (cid, some ("refs/heads/" ++ branch.raw, cid, remName, upRef))
                  | _ :: _ :: _ =>
                    .error { kind := .invalidRef, message := s!"'{branch.raw}' matched multiple remote tracking branches" }
                  | [] => .error { kind := .invalidRef, message := s!"invalid reference: {branch.raw}" }
              match swTargetRes with
              | .error e => (.error e, s)
              | .ok (newCid, dwimCreate?) =>
                if wt.index.hasMergeHead then
                  (.error { kind := .commandFailed, message := "cannot switch branch while merging" }, s)
                else if isBranchInUseElsewhere repo wt.rootPath branch && wt.head != .symbolic branch then
                  (.error { kind := .branchInUse, message := s!"'{branch.raw}' is already used by worktree" }, s)
                else if !force && !wt.index.conflicts.isEmpty then
                  (.error { kind := .conflict, message := "you need to resolve your current index first" }, s)
                else
                  let oldTree :=
                    match headCommitOfSymbolic repo wt.head with
                    | some cid => treeOfCommit repo cid
                    | none => []
                  let newTree := treeOfCommit repo newCid
                  match applyTwoTreeCheckoutWithPerm s.vfs wt oldTree newTree force s.repos with
                  | .error e => (.error e, s)
                  | .ok (vfs', idx', hadPermErr) =>
                    let repo0 :=
                      match dwimCreate? with
                      | none => repo
                      | some (fullRef, cid, remName, upRef) =>
                        { repo with
                          refs := setRefInList repo.refs fullRef cid
                          branchUpstreams := setBranchUpstream repo.branchUpstreams branch.raw upRef
                          branchRemotes := setBranchRemote repo.branchRemotes branch.raw remName ("refs/heads/" ++ branch.raw) }
                    let repo' := updateWorktreeInRepo repo0 wt.rootPath fun slot =>
                      { slot with head := .symbolic branch, index := idx' }
                    let overwritten := collectOverwrittenDirPaths s.vfs (splitByteSlash wt.rootPath) newTree
                    let repos1 := pruneReposUnderPaths repo.commonDir overwritten s.repos
                    let s' := { s with vfs := vfs', repos := updateRepoInList repos1 repo.commonDir (fun _ => repo') }
                    if hadPermErr then
                      (.error { kind := .commandFailed, message := "unable to update working tree: permission denied" }, s')
                    else
                      (.ok (), s')
            else
              let oldCid? := headCommitOfSymbolic repo wt.head
              let resolvedTargetRes : Except GitError (Option CommitId) :=
                match parsedSp? with
                | some sp =>
                  match sp with
                  | { base := .commitId cid, steps := [] } =>
                    match findBranchCommit? repo { raw := cid.hex } with
                    | some bCid => .ok (some bCid)
                    | none => (resolveParsedRevInRepo repo wt sp).map some
                  | _ =>
                    (resolveParsedRevInRepo repo wt sp).map some
                | none => .ok oldCid?
              match resolvedTargetRes with
              | .error e => (.error e, s)
              | .ok targetCid? =>
                let fullRef := "refs/heads/" ++ branch.raw
                if (lookupFullRef repo fullRef).isSome && !force then
                  (.error { kind := .alreadyExists, message := s!"a branch named '{branch.raw}' already exists" }, s)
                else if force && isBranchInUseElsewhere repo wt.rootPath branch && wt.head != .symbolic branch then
                  (.error { kind := .branchInUse, message := s!"'{branch.raw}' is already used by worktree" }, s)
                else if parsedSp?.any (fun sp => isAmbiguousBareRef repo sp true) then
                  (.error { kind := .invalidRef, message := s!"ambiguous object name: '{startPoint?.getD ""}'" }, s)
                else if hasRefDFConflict repo fullRef then
                  (.error { kind := .commandFailed, message := s!"cannot lock ref '{fullRef}': D/F conflict" }, s)
                else if wt.index.hasMergeHead then
                  (.error { kind := .commandFailed, message := "cannot switch branch while merging" }, s)
                else
                  let (ups', rems') :=
                    match parsedSp? with
                    | some sp =>
                      match autoUpstreamOfParsedRef repo sp with
                      | some (upRef, remName, mergeRef) =>
                        (setBranchUpstream repo.branchUpstreams branch.raw upRef,
                         setBranchRemote repo.branchRemotes branch.raw remName mergeRef)
                      | none => (repo.branchUpstreams, repo.branchRemotes)
                    | none => (repo.branchUpstreams, repo.branchRemotes)
                  match parsedSp?, targetCid? with
                  | none, none =>
                    let repo' := updateWorktreeInRepo repo wt.rootPath fun slot =>
                      { slot with head := .symbolic branch }
                    (.ok (), { s with repos := updateRepoInList s.repos repo.commonDir (fun _ => repo') })
                  | none, some targetCid =>
                    let repo1 := { repo with refs := setRefInList repo.refs fullRef targetCid }
                    let repo2 := updateWorktreeInRepo repo1 wt.rootPath fun slot =>
                      { slot with head := .symbolic branch }
                    (.ok (), { s with repos := updateRepoInList s.repos repo.commonDir (fun _ => repo2) })
                  | some _, none =>
                    (.error { kind := .invalidRef, message := "unborn HEAD" }, s)
                  | some sp, some targetCid =>
                    if !force && !wt.index.conflicts.isEmpty then
                      (.error { kind := .conflict, message := "you need to resolve your current index first" }, s)
                    else
                      let branchRefCid :=
                        match sp with
                        | { base := .commitId cid, steps := [] } =>
                          (resolveDwimRefCommit? repo cid.hex).getD targetCid
                        | _ => targetCid
                      let oldTree :=
                        match oldCid? with
                        | some cid => treeOfCommit repo cid
                        | none => []
                      let newTree := treeOfCommit repo targetCid
                      match applyTwoTreeCheckoutWithPerm s.vfs wt oldTree newTree force s.repos with
                      | .error e => (.error e, s)
                      | .ok (vfs', idx', hadPermErr) =>
                        let repo1 :=
                          { repo with
                            refs := setRefInList repo.refs fullRef branchRefCid
                            branchUpstreams := ups'
                            branchRemotes := rems' }
                        let repo2 := updateWorktreeInRepo repo1 wt.rootPath fun slot =>
                          { slot with head := .symbolic branch, index := idx' }
                        let overwritten := collectOverwrittenDirPaths s.vfs (splitByteSlash wt.rootPath) newTree
                        let repos1 := pruneReposUnderPaths repo.commonDir overwritten s.repos
                        let s' := { s with vfs := vfs', repos := updateRepoInList repos1 repo.commonDir (fun _ => repo2) }
                        if hadPermErr then
                          (.error { kind := .commandFailed, message := "unable to update working tree: permission denied" }, s')
                        else
                          (.ok (), s')

/-- Pure `reset` model step. -/
def stepReset (s : GitRepoState) (repoPath : String) (mode : ResetMode) (rev : String) :
    Except GitError Unit × GitRepoState :=
  match validateFsPathArg repoPath with
  | .error e => (.error e, s)
  | .ok () =>
    match parseSupportedRevSpec rev with
    | none => (.error { kind := .invalidInput, message := s!"invalid revision: '{rev}'" }, s)
    | some parsed =>
      match resolveCwdAndDiscover s repoPath with
      | .error e => (.error e, s)
      | .ok (repo, wt?, _, _) =>
        match activeHeadSlot repo wt? with
        | none => (.error { kind := .notARepo, message := "missing worktree slot" }, s)
        | some sl =>
          let curCid? := headCommitOfSymbolic repo sl.head
          let targetCidOptRes : Except GitError (Option CommitId) :=
            if (rev == "HEAD" || rev == "@") && curCid?.isNone then
              .ok none
            else
              (resolveParsedRevInRepo repo sl parsed).map some
          match targetCidOptRes with
          | .error e => (.error e, s)
          | .ok targetCid? =>
            if mode == .hard && wt?.isNone then
              (.error { kind := .notARepo, message := "this operation must be run in a work tree" }, s)
            else if mode == .mixed && repo.isBare && wt?.isNone then
              (.error { kind := .notARepo, message := "mixed reset is not allowed in a bare repository" }, s)
            else if mode == .soft && (sl.index.hasMergeHead || !sl.index.conflicts.isEmpty) then
              (.error { kind := .commandFailed, message := "Cannot do a soft reset in the middle of a merge." }, s)
            else
              match targetCid? with
              | none =>
                match mode with
                | .soft => (.ok (), s)
                | .mixed =>
                  let repo' := updateWorktreeInRepo repo sl.rootPath fun slot =>
                    { slot with index := { entries := [], conflicts := [], hasMergeHead := false, mergeParents := [] } }
                  (.ok (), { s with repos := updateRepoInList s.repos repo.commonDir (fun _ => repo') })
                | .hard =>
                  let rootParts := splitByteSlash sl.rootPath
                  let pathsToDrop := sl.index.entries.map (·.1) ++ sl.index.conflicts.map (·.path)
                  let vfs' := pathsToDrop.foldl (fun v p =>
                    let keepDir :=
                      match lookupTreeEntry sl.index.entries p with
                      | some iE => iE.kind == .gitlink
                      | none => false
                    (removeEntryAndPruneVfsChecked v rootParts (splitByteSlash p) keepDir).1) s.vfs
                  let repo' := updateWorktreeInRepo repo sl.rootPath fun slot =>
                    { slot with index := { entries := [], conflicts := [], hasMergeHead := false, mergeParents := [] } }
                  (.ok (), { s with vfs := vfs', repos := updateRepoInList s.repos repo.commonDir (fun _ => repo') })
              | some targetCid =>
                let (refs', head') : List (String × CommitId) × SymbolicHead :=
                  match sl.head with
                  | .symbolic b => (setRefInList repo.refs ("refs/heads/" ++ b.raw) targetCid, SymbolicHead.symbolic b)
                  | .detached _ => (repo.refs, SymbolicHead.detached targetCid)
                let newTree := treeOfCommit repo targetCid
                match mode with
                | .soft =>
                  let repo1 := { repo with refs := refs' }
                  let repo2 := updateWorktreeInRepo repo1 sl.rootPath fun slot =>
                    { slot with head := head' }
                  (.ok (), { s with repos := updateRepoInList s.repos repo.commonDir (fun _ => repo2) })
                | .mixed =>
                  let repo1 := { repo with refs := refs' }
                  let repo2 := updateWorktreeInRepo repo1 sl.rootPath fun slot =>
                    { slot with head := head', index := { entries := sortByBytes (·.1) newTree, conflicts := [], hasMergeHead := false, mergeParents := [] } }
                  (.ok (), { s with repos := updateRepoInList s.repos repo.commonDir (fun _ => repo2) })
                | .hard =>
                  let rootParts := splitByteSlash sl.rootPath
                  let wtNode := (lookupNodeAtParts s.vfs rootParts).getD VfsNode.emptyDir
                  let allRemovable := dirSubtreeRemovableLoop [wtNode]
                  let preflightOk :=
                    allRemovable ||
                    newTree.all fun (relPath, entry) =>
                      entry.kind == .gitlink || dirTreeCanBeRemovedChecked s.vfs rootParts (splitByteSlash relPath)
                  if !preflightOk then
                    (.error { kind := .commandFailed, message := "cannot opendir: permission denied" }, s)
                  else
                    let oldTree :=
                      match curCid? with
                      | some cid => treeOfCommit repo cid
                      | none => []
                    let newMap := buildEntryMap newTree
                    let oldMap := buildEntryMap oldTree
                    let idxMap := buildEntryMap sl.index.entries
                    let allPaths : List ByteArray :=
                      dedupSortedByteArraysLoop []
                        (sortByBytes id
                          ((oldTree.map Prod.fst) ++ (sl.index.entries.map Prod.fst) ++
                           (sl.index.conflicts.map ConflictEntry.path) ++ (newTree.map Prod.fst)))
                    let deletions : List (ByteArray × Bool) :=
                      allPaths.filterMap fun p =>
                        match newMap.get? p with
                        | some _ => none
                        | none =>
                          let keepDir :=
                            match oldMap.get? p, idxMap.get? p with
                            | some oE, _ => oE.kind == .gitlink
                            | none, some iE => iE.kind == .gitlink
                            | none, none => false
                          some (p, keepDir)
                    let (v1, _errDel) := bulkRemoveEntriesChecked s.vfs rootParts deletions
                    let wtNode1 := (lookupNodeAtParts v1 rootParts).getD VfsNode.emptyDir
                    let fastWrite := allRemovable && noSpecialDirsUnderNode wtNode1 &&
                      (match wtNode1 with | .dir true true _ => true | _ => false)
                    let diskMap1 : Std.TreeMap ByteArray GitTreeEntry cmpBytes :=
                      if fastWrite then buildEntryMap (collectVfsFilesUnder v1 rootParts) else {}
                    let entriesToWrite :=
                      newTree.filter fun (relPath, entry) =>
                        let dOpt :=
                          if fastWrite then diskMap1.get? relPath
                          else
                            match lookupVfsRelEntryChecked v1 rootParts relPath with
                            | .ok opt => opt
                            | .error _ => none
                        if idxMap.get? relPath == some entry then
                          dOpt != some entry
                        else if fastWrite then
                          dOpt != some entry
                        else
                          true
                    let (v2, errWr) :=
                      if fastWrite && entriesToWrite.length <= 8 then
                        entriesToWrite.foldl (fun (v, hadErr) (relPath, entry) =>
                          let (v', err') := ensureParentsAndWriteEntryChecked v rootParts (splitByteSlash relPath) entry
                          (v', hadErr || err')) (v1, false)
                      else
                        writeTreeToVfsChecked v1 rootParts entriesToWrite
                    let idx' : IndexState :=
                      { entries := sortByBytes (·.1) newTree, conflicts := [], hasMergeHead := false, mergeParents := [] }
                    if errWr then
                      (.error { kind := .commandFailed, message := "could not reset index file: permission denied" },
                        { s with vfs := v2 })
                    else
                      let repo1 := { repo with refs := refs' }
                      let repo2 := updateWorktreeInRepo repo1 sl.rootPath fun slot =>
                        { slot with head := head', index := idx' }
                      let repos1 :=
                        if s.repos.all (fun r => r.commonDir == repo.commonDir) then s.repos
                        else
                          let overwritten := collectOverwrittenDirPaths s.vfs rootParts newTree
                          pruneReposUnderPaths repo.commonDir overwritten s.repos
                      (.ok (), { s with vfs := v2, repos := updateRepoInList repos1 repo.commonDir (fun _ => repo2) })

/-- Pure `fetch` model step. -/
def stepFetch (s : GitRepoState) (repoPath remote : String) (refspec? : Option String)
    (prune : Bool) : Except GitError Unit × GitRepoState :=
  match validateFsPathArg repoPath with
  | .error e => (.error e, s)
  | .ok () =>
    if !isValidRemoteOrRefspec remote then
      (.error { kind := .invalidInput, message := s!"invalid remote name: '{remote}'" }, s)
    else if !(refspec?.all isValidRemoteOrRefspec) then
      (.error { kind := .invalidInput, message := s!"invalid refspec: '{refspec?.getD ""}'" }, s)
    else
      match resolveCwdAndDiscover s repoPath with
      | .error e => (.error e, s)
      | .ok (repo, wt?, _, canonRepoParts) =>
        let parsedSpecRes : Except GitError (Option ParsedFetchRefspec) :=
          match refspec? with
          | none => .ok none
          | some r =>
            match parseFetchRefspec? r with
            | some pf => .ok (some pf)
            | none => .error { kind := .commandFailed, message := s!"invalid refspec '{r}'" }
        match parsedSpecRes with
        | .error e => (.error e, s)
        | .ok parsedSpec? =>
          let fetchBaseParts :=
            match wt? with
            | some wt => splitByteSlash wt.rootPath
            | none => canonRepoParts
          let (hasConfiguredRemote, rawUrl, defaultSpecs) :=
            match repo.remotes.find? (fun r => r.name == remote) with
            | some rm => (true, rm.url, rm.fetchSpecs)
            | none => (false, remote, [])
          match isLocalFileSource? rawUrl with
          | none =>
            (.error { kind := .commandFailed, message := s!"transport not allowed for '{rawUrl}'" }, s)
          | some (isFileUrl, srcPath) =>
            if isFileUrl && srcPath.isEmpty then
              (.error { kind := .commandFailed, message := "no path specified" }, s)
            else
              match findExactSourceRepoFrom s fetchBaseParts srcPath with
              | .error _ =>
                (.error { kind := .commandFailed, message := s!"'{srcPath}' does not appear to be a git repository" }, s)
              | .ok (srcRepo, srcWt?, _) =>
                let activeMergeRef? : Option String :=
                  if !hasConfiguredRemote then none
                  else
                    match activeHeadSlot repo wt? with
                    | some sl =>
                      match sl.head with
                      | .symbolic curBr =>
                        (repo.branchRemotes.find? (fun p => p.1 == curBr.raw && p.2.1 == remote)).map (·.2.2)
                      | .detached _ => none
                    | none => none
                let specsToRun : List ParsedFetchRefspec :=
                  match parsedSpec? with
                  | some pf => [pf]
                  | none =>
                    if defaultSpecs.isEmpty then
                      match activeMergeRef? with
                      | some mr => [{ force := false, src := mr, dst? := none, isGlob := false, ignoreMissing := true }]
                      | none => [{ force := false, src := "HEAD", dst? := none, isGlob := false }]
                    else
                      defaultSpecs.filterMap parseFetchRefspec?
                let effectiveDstRef (dRef : String) : String :=
                  match repo.symRefs.find? (fun p => p.1 == dRef) with
                  | some (_, tgt) => tgt
                  | none => dRef
                let applyOneRefUpdate
                    (tempRepo : RepoInstance)
                    (refsAcc : List (String × CommitId))
                    (updatedRefCids : List CommitId)
                    (firstReject? : Option GitError)
                    (dRef : String) (sCid : CommitId) (force : Bool) :
                    List (String × CommitId) × List CommitId × Option GitError :=
                  match (refsAcc.find? (fun p => p.1 == dRef)).map (·.2) with
                  | none =>
                    if hasRefDFConflict { tempRepo with refs := refsAcc } dRef then
                      let rej :=
                        if firstReject?.isNone then
                          some { kind := .commandFailed, message := s!"D/F ref conflict on '{dRef}'" }
                        else firstReject?
                      (refsAcc, updatedRefCids, rej)
                    else
                      (setRefInList refsAcc dRef sCid, sCid :: updatedRefCids, firstReject?)
                  | some oldCid =>
                    let canUpdate :=
                      if dRef.startsWith "refs/tags/" then oldCid == sCid || force
                      else oldCid == sCid || force || isAncestor tempRepo oldCid sCid
                    if canUpdate then
                      (setRefInList refsAcc dRef sCid, sCid :: updatedRefCids, firstReject?)
                    else
                      let rej :=
                        if firstReject?.isNone then
                          some { kind := .commandFailed, message := s!"rejected non-fast-forward fetch to '{dRef}'" }
                        else firstReject?
                      (refsAcc, updatedRefCids, rej)
                let globMatchesOf (sp : ParsedFetchRefspec) : List (String × String × CommitId) :=
                  let headCand : List (String × CommitId) :=
                    match (srcWt? <|> srcRepo.worktrees.head?).bind (fun w => headCommitOfSymbolic srcRepo w.head) with
                    | some hc => [("HEAD", hc)]
                    | none => []
                  let allSrc := headCand ++ srcRepo.refs
                  allSrc.filterMap fun (sRef, sCid) =>
                    (matchSingleGlob? sp.src sp.srcSuffix sRef).map fun stem => (sRef, stem, sCid)
                let applySpecs : Except GitError (List (String × CommitId) × List CommitId × Option GitError) := do
                  for sp in specsToRun do
                    if sp.isGlob then
                      let dstPfx := sp.dst?.getD sp.src
                      let matched := globMatchesOf sp
                      for (_, stem, _) in matched do
                        let rawTarget := dstPfx ++ stem ++ sp.dstSuffix
                        if rawTarget.startsWith "refs/" && isValidRefNameStr rawTarget then
                          let dRef := effectiveDstRef rawTarget
                          if dRef.startsWith "refs/heads/" &&
                              isBranchCheckedOutAnywhere repo { raw := String.ofList (dRef.toList.drop 11) } then
                            .error { kind := .commandFailed, message := s!"refusing to fetch into branch '{dRef}' checked out at worktree" }
                    else
                      let srcInfoRes : Except GitError (Option (CommitId × Option String)) :=
                        if sp.src == "HEAD" then
                          let hc? := (srcWt? <|> srcRepo.worktrees.head?).bind (fun w => headCommitOfSymbolic srcRepo w.head)
                          match hc? with
                          | some c => .ok (some (c, none))
                          | none =>
                            if sp.ignoreMissing then .ok none
                            else .error { kind := .notFound, message := s!"couldn't find remote ref {sp.src}" }
                        else if isValidCommitIdStr sp.src then
                          let cid : CommitId := { hex := sp.src }
                          if hasCommit srcRepo cid then
                            .ok (some (cid, none))
                          else if sp.src.length == 40 then
                            if sp.ignoreMissing then .ok none
                            else .error { kind := .commandFailed, message := s!"git upload-pack: not our ref {sp.src}" }
                          else
                            match resolveDwimRefEntry? srcRepo sp.src with
                            | some (full, c) => .ok (some (c, some full))
                            | none =>
                              if sp.ignoreMissing then .ok none
                              else .error { kind := .notFound, message := s!"couldn't find remote ref {sp.src}" }
                        else
                          match resolveDwimRefEntry? srcRepo sp.src with
                          | some (full, c) => .ok (some (c, some full))
                          | none =>
                            if sp.ignoreMissing then .ok none
                            else .error { kind := .notFound, message := s!"couldn't find remote ref {sp.src}" }
                      let srcInfo? ← srcInfoRes
                      if srcInfo?.isSome then
                        if let some dstRaw := sp.dst? then
                          let rawDst := qualifyFetchDstRef dstRaw
                          let dRef := effectiveDstRef rawDst
                          if dRef.startsWith "refs/heads/" &&
                              isBranchCheckedOutAnywhere repo { raw := String.ofList (dRef.toList.drop 11) } then
                            .error { kind := .commandFailed, message := s!"refusing to fetch into branch '{dRef}' checked out at worktree" }
                  let mut refsAcc := repo.refs
                  let mut pulledRoots : List CommitId := []
                  let mut updatedRefCids : List CommitId := []
                  let mut fetchedSourceRefs : List (String × CommitId) := []
                  let mut explicitDstRefs : List String := []
                  let mut firstReject? : Option GitError := none
                  let tempRepo : RepoInstance := { repo with commits := copyReachableCommitNodes repo.commits srcRepo.commits (srcRepo.refs.map (·.2)) }
                  for sp in specsToRun do
                    if sp.isGlob then
                      let dstPfx := sp.dst?.getD sp.src
                      let matched := globMatchesOf sp
                      if prune then
                        refsAcc := refsAcc.filter fun (rName, _) =>
                          match matchSingleGlob? dstPfx sp.dstSuffix rName with
                          | some stem =>
                            matched.any (fun (sRef, _, _) => sRef == sp.src ++ stem ++ sp.srcSuffix)
                          | none => true
                      for (sRef, stem, sCid) in matched do
                        let rawTarget := dstPfx ++ stem ++ sp.dstSuffix
                        if rawTarget.startsWith "refs/" && isValidRefNameStr rawTarget then
                          let dRef := effectiveDstRef rawTarget
                          pulledRoots := sCid :: pulledRoots
                          fetchedSourceRefs := (sRef, sCid) :: fetchedSourceRefs
                          explicitDstRefs := dRef :: explicitDstRefs
                          let (r1, u1, rej1) := applyOneRefUpdate tempRepo refsAcc updatedRefCids firstReject? dRef sCid sp.force
                          refsAcc := r1
                          updatedRefCids := u1
                          firstReject? := rej1
                    else
                      let srcInfo? : Option (CommitId × Option String) :=
                        if sp.src == "HEAD" then
                          ((srcWt? <|> srcRepo.worktrees.head?).bind (fun w => headCommitOfSymbolic srcRepo w.head)).map (·, none)
                        else if isValidCommitIdStr sp.src then
                          let cid : CommitId := { hex := sp.src }
                          if hasCommit srcRepo cid then some (cid, none)
                          else if sp.src.length == 64 then
                            (resolveDwimRefEntry? srcRepo sp.src).map (fun (full, c) => (c, some full))
                          else none
                        else
                          (resolveDwimRefEntry? srcRepo sp.src).map (fun (full, c) => (c, some full))
                      if let some (sCid, sFullRef?) := srcInfo? then
                        pulledRoots := sCid :: pulledRoots
                        if let some sRef := sFullRef? then
                          fetchedSourceRefs := (sRef, sCid) :: fetchedSourceRefs
                        if let some dstRaw := sp.dst? then
                          let rawDst := qualifyFetchDstRef dstRaw
                          let dRef := effectiveDstRef rawDst
                          explicitDstRefs := dRef :: explicitDstRefs
                          let (r1, u1, rej1) := applyOneRefUpdate tempRepo refsAcc updatedRefCids firstReject? dRef sCid sp.force
                          refsAcc := r1
                          updatedRefCids := u1
                          firstReject? := rej1
                  if hasConfiguredRemote && parsedSpec?.isSome then
                    for cfgSp in defaultSpecs.filterMap parseFetchRefspec? do
                      if cfgSp.isGlob then
                        let dstPfx := cfgSp.dst?.getD cfgSp.src
                        for (sRef, sCid) in fetchedSourceRefs.reverse do
                          match matchSingleGlob? cfgSp.src cfgSp.srcSuffix sRef with
                          | some stem =>
                            let rawTarget := dstPfx ++ stem ++ cfgSp.dstSuffix
                            if rawTarget.startsWith "refs/" && isValidRefNameStr rawTarget then
                              let dRef := effectiveDstRef rawTarget
                              let checkedOut :=
                                dRef.startsWith "refs/heads/" &&
                                isBranchCheckedOutAnywhere repo { raw := String.ofList (dRef.toList.drop 11) }
                              if !explicitDstRefs.contains dRef && !checkedOut then
                                let (r1, u1, rej1) := applyOneRefUpdate tempRepo refsAcc updatedRefCids firstReject? dRef sCid cfgSp.force
                                refsAcc := r1
                                updatedRefCids := u1
                                firstReject? := rej1
                          | none => pure ()
                      else if let some dstRaw := cfgSp.dst? then
                        let cfgSrcFull? : Option String :=
                          if cfgSp.src.startsWith "refs/" then some cfgSp.src
                          else (resolveDwimRefEntry? srcRepo cfgSp.src).map (·.1)
                        if let some cfgSrcFull := cfgSrcFull? then
                          for (sRef, sCid) in fetchedSourceRefs.reverse do
                            if sRef == cfgSrcFull then
                              let rawDst := qualifyFetchDstRef dstRaw
                              let dRef := effectiveDstRef rawDst
                              let checkedOut :=
                                dRef.startsWith "refs/heads/" &&
                                isBranchCheckedOutAnywhere repo { raw := String.ofList (dRef.toList.drop 11) }
                              if !explicitDstRefs.contains dRef && !checkedOut then
                                let (r1, u1, rej1) := applyOneRefUpdate tempRepo refsAcc updatedRefCids firstReject? dRef sCid cfgSp.force
                                refsAcc := r1
                                updatedRefCids := u1
                                firstReject? := rej1
                  let wantsAutoTags := specsToRun.any (fun sp => sp.dst?.isSome)
                  if wantsAutoTags then
                    let repoSet : Std.TreeSet.Raw String compare :=
                      repo.commits.foldl (fun st c => st.insert c.id.hex) .empty
                    let reachAllSet := reachableCommitHexSet tempRepo updatedRefCids
                    for (tRef, tCid) in srcRepo.refs do
                      if tRef.startsWith "refs/tags/" &&
                          (repoSet.contains tCid.hex || reachAllSet.contains tCid.hex) then
                        if (refsAcc.find? (fun p => p.1 == tRef)).isNone &&
                            !hasRefDFConflict { tempRepo with refs := refsAcc } tRef then
                          refsAcc := setRefInList refsAcc tRef tCid
                          pulledRoots := tCid :: pulledRoots
                  return (refsAcc, pulledRoots, firstReject?)
                match applySpecs with
                | .error e => (.error e, s)
                | .ok (refs', pulledRoots, reject?) =>
                  let commits' := copyReachableCommitNodes repo.commits srcRepo.commits pulledRoots
                  let symRefName := s!"refs/remotes/{remote}/HEAD"
                  let symRefs' :=
                    if parsedSpec?.isSome || (repo.remotes.find? (fun r => r.name == remote)).isNone then
                      repo.symRefs
                    else if repo.symRefs.any (fun p => p.1 == symRefName) then
                      repo.symRefs
                    else if !specsToRun.any (fun sp =>
                        sp.isGlob && sp.src == "refs/heads/" && sp.srcSuffix == "" &&
                        sp.dst? == some s!"refs/remotes/{remote}/" && sp.dstSuffix == "") then
                      repo.symRefs
                    else
                      match resolveSourceHeadBranch? srcRepo (srcWt? <|> srcRepo.worktrees.head?) s.defaultInitBranch false with
                      | none => repo.symRefs
                      | some brName =>
                        let targetRemoteRef := s!"refs/remotes/{remote}/{brName}"
                        if refs'.any (fun p => p.1 == targetRemoteRef) &&
                            !(refs'.any (fun p => p.1 == symRefName)) then
                          repo.symRefs ++ [(symRefName, targetRemoteRef)]
                        else
                          repo.symRefs
                  let repo' := { repo with commits := commits', refs := refs', symRefs := symRefs' }
                  let s' := { s with repos := updateRepoInList s.repos repo.commonDir (fun _ => repo') }
                  match reject? with
                  | some e => (.error e, s')
                  | none => (.ok (), s')

private def upsertWorktreeSlot (wts : List WorktreeSlot) (slot : WorktreeSlot) : List WorktreeSlot :=
  if wts.any (fun w => w.rootPath == slot.rootPath) then
    wts.map (fun w => if w.rootPath == slot.rootPath then slot else w)
  else
    wts ++ [slot]

/-- Extract the trailing path component after stripping trailing `'/'` for default `git worktree add <path>`. -/
def basenameForDefaultWorktreeBranch (p : String) : String :=
  let trimmed := stripTrailingSlashes p
  let rev := trimmed.toList.reverse.takeWhile (· != '/')
  String.ofList rev.reverse

/-- Pure `worktreeAdd` model step. -/
def stepWorktreeAdd (s : GitRepoState) (repoPath : String) (opts : WorktreeAddOptions) :
    Except GitError Unit × GitRepoState :=
  match validateFsPathArg repoPath, validateFsPathArg opts.path with
  | .error e, _ => (.error e, s)
  | _, .error e => (.error e, s)
  | .ok (), .ok () =>
    if opts.detach && opts.newBranch?.isSome then
      (.error { kind := .invalidInput, message := "worktreeAdd cannot combine detach and newBranch" }, s)
    else
      let isDefaultMode := !opts.detach && opts.newBranch?.isNone && opts.target?.isNone
      let defaultBr := basenameForDefaultWorktreeBranch opts.path
      let defaultBrCheck : Except GitError Unit :=
        if isDefaultMode && !isValidRefNameStr defaultBr then
          .error { kind := .invalidRef, message := s!"invalid branch name: '{defaultBr}'" }
        else .ok ()
      match defaultBrCheck with
      | .error e => (.error e, s)
      | .ok () =>
        let brCheck : Except GitError Unit :=
          match opts.newBranch? with
          | none => .ok ()
          | some b =>
            if isValidRefNameStr b.raw then .ok ()
            else .error { kind := .invalidRef, message := s!"invalid branch name: '{b.raw}'" }
        match brCheck with
        | .error e => (.error e, s)
        | .ok () =>
          let tgtCheck : Except GitError (Option ParsedRev) :=
            match opts.target? with
            | none => .ok none
            | some t =>
              match parseSupportedRevSpec t with
              | some pr => .ok (some pr)
              | none => .error { kind := .invalidInput, message := s!"invalid worktree target: '{t}'" }
          match tgtCheck with
          | .error e => (.error e, s)
          | .ok parsedTgt? =>
            match resolveCwdAndDiscover s repoPath with
              | .error e => (.error e, s)
              | .ok (repo, wt?, _, canonRepoParts) =>
                match activeHeadSlot repo wt? with
                | none => (.error { kind := .notARepo, message := "missing worktree slot" }, s)
                | some activeSl =>
                  let effNewBranch? : Option RefName :=
                    match opts.newBranch? with
                    | some nb => some nb
                    | none =>
                      if isDefaultMode then
                        let br : RefName := { raw := defaultBr }
                        if (findBranchCommit? repo br).isSome || !(findRemoteDwimMatches repo defaultBr).isEmpty then
                          none
                        else some br
                      else none
                  let effTarget? : Option String :=
                    if opts.target?.isSome then opts.target?
                    else if isDefaultMode && effNewBranch?.isNone then some defaultBr
                    else none
                  let effParsedTgt? : Option ParsedRev :=
                    if parsedTgt?.isSome then parsedTgt?
                    else if isDefaultMode && effNewBranch?.isNone then parseSupportedRevSpec defaultBr
                    else none
                  let planRes : Except GitError (SymbolicHead × Option CommitId × Option (String × CommitId) × Option RefName × Option (String × String × String × String)) :=
                    if opts.detach then
                      let parsedT := effParsedTgt?.getD { base := .head, steps := [] }
                      match resolveParsedRevInRepo repo activeSl parsedT with
                      | .error e => .error e
                      | .ok cid => .ok (.detached cid, some cid, none, none, none)
                    else
                      match effNewBranch? with
                      | some nb =>
                        let fullRef := "refs/heads/" ++ nb.raw
                        let resolvedCid? : Except GitError (Option CommitId) :=
                          match effParsedTgt? with
                          | none =>
                            match headCommitOfSymbolic repo activeSl.head with
                            | some hc => .ok (some hc)
                            | none =>
                              if repo.refs.any (fun p => p.1.startsWith "refs/heads/") then
                                .error { kind := .invalidRef, message := "invalid reference: HEAD" }
                              else
                                .ok none
                          | some parsedT =>
                            (resolveParsedRevInRepo repo activeSl parsedT).map some
                        match resolvedCid? with
                        | .error e => .error e
                        | .ok cid? =>
                          if (lookupFullRef repo fullRef).isSome then
                            .error { kind := .alreadyExists, message := s!"a branch named '{nb.raw}' already exists" }
                          else if effParsedTgt?.any (fun pt => isAmbiguousBareRef repo pt true) then
                            .error { kind := .invalidRef, message := s!"ambiguous object name: '{effTarget?.getD ""}'" }
                          else if hasRefDFConflict repo fullRef then
                            .error { kind := .commandFailed, message := s!"cannot lock ref '{fullRef}': D/F conflict" }
                          else
                            let up? :=
                              match effParsedTgt? with
                              | some pt =>
                                (autoUpstreamOfParsedRef repo pt).map fun (ur, rm, mr) => (nb.raw, ur, rm, mr)
                              | none => none
                            let branchCid? :=
                              match effParsedTgt?, cid? with
                              | some { base := .commitId cid, steps := [] }, some revCid =>
                                some ((resolveDwimRefCommit? repo cid.hex).getD revCid)
                              | _, other => other
                            match branchCid? with
                            | none => .ok (.symbolic nb, none, none, none, up?)
                            | some cid => .ok (.symbolic nb, some cid, some (fullRef, cid), none, up?)
                      | none =>
                        match effTarget?, effParsedTgt? with
                        | some tStr, some parsedT =>
                          let isHexObj := (tStr.length == 40 || tStr.length == 64) && isValidCommitIdStr tStr
                          let hasHexCommit := (resolveCommitIdArg? repo { hex := tStr }).isSome
                          let localBr? : Option (RefName × CommitId) :=
                            if isValidRefNameStr tStr && (!isHexObj || hasHexCommit) then
                              let br : RefName := { raw := tStr }
                              (findBranchCommit? repo br).map (br, ·)
                            else none
                          match localBr? with
                          | some (br, cid) => .ok (.symbolic br, some cid, none, some br, none)
                          | none =>
                            if isValidRefNameStr tStr && !isHexObj then
                              let dwim := findRemoteDwimMatches repo tStr
                              match dwim with
                              | [(remName, upRef, cid)] =>
                                let br : RefName := { raw := tStr }
                                .ok (.symbolic br, some cid, some ("refs/heads/" ++ tStr, cid), none, some (tStr, upRef, remName, "refs/heads/" ++ tStr))
                              | _ :: _ :: _ =>
                                .error { kind := .invalidRef, message := s!"'{tStr}' matched multiple remote tracking branches" }
                              | [] =>
                                match resolveParsedRevInRepo repo activeSl parsedT with
                                | .error e => .error e
                                | .ok cid => .ok (.detached cid, some cid, none, none, none)
                            else
                              match resolveParsedRevInRepo repo activeSl parsedT with
                              | .error e => .error e
                              | .ok cid => .ok (.detached cid, some cid, none, none, none)
                        | _, _ => .error { kind := .invalidInput, message := "missing branch target" }
                  match planRes with
                  | .error e => (.error e, s)
                  | .ok (newHead, cid?, newRef?, checkBrInUse?, newUp?) =>
                    let sAfterBranch :=
                      match newRef? with
                      | none => s
                      | some (rn, c) =>
                        let refs' := setRefInList repo.refs rn c
                        let (ups', rems') :=
                          match newUp? with
                          | some (br, ur, rm, mr) =>
                            (setBranchUpstream repo.branchUpstreams br ur,
                             setBranchRemote repo.branchRemotes br rm mr)
                          | none => (repo.branchUpstreams, repo.branchRemotes)
                        let repoB := { repo with refs := refs', branchUpstreams := ups', branchRemotes := rems' }
                        { s with repos := updateRepoInList s.repos repo.commonDir (fun _ => repoB) }
                    let wtBytes := opts.path.toUTF8
                    let cwdPartsForTarget := if startsWithSlashByte wtBytes then [] else canonRepoParts
                    let destCheck : Except GitError (VfsNode × List ByteArray) :=
                      match resolveVfsFuel 41 s.vfs cwdPartsForTarget (splitByteSlash wtBytes) true with
                      | .ok (.dir canonParts searchable _ cs) =>
                        if !searchable || !cs.isEmpty then
                          .error { kind := .alreadyExists, message := s!"'{opts.path}' already exists" }
                        else
                          let cb := joinAbsByteParts canonParts
                          if repo.worktrees.any (fun w => w.rootPath == cb && w.isLocked) then
                            .error { kind := .commandFailed, message := s!"'{opts.path}' is a missing but locked worktree" }
                          else if repo.worktrees.any (fun w => w.rootPath == cb) && !opts.force then
                            .error { kind := .alreadyExists, message := s!"worktree '{opts.path}' already exists" }
                          else
                            .ok (s.vfs, canonParts)
                      | .ok (.file _ _ _) | .ok (.symlink _ _) =>
                        .error { kind := .alreadyExists, message := s!"'{opts.path}' already exists" }
                      | .error .eloop =>
                        .error { kind := .invalidInput, message := s!"too many levels of symbolic links: '{opts.path}'" }
                      | .error .enotdir =>
                        .error { kind := .alreadyExists, message := s!"'{opts.path}' already exists" }
                      | .error .enoent =>
                        match resolveVfsFuel 41 s.vfs cwdPartsForTarget (splitByteSlash wtBytes) false with
                        | .ok (.symlink _ _) =>
                          .error { kind := .alreadyExists, message := s!"'{opts.path}' already exists" }
                        | _ =>
                          let normParts := normalizeDotDotParts cwdPartsForTarget (splitByteSlash wtBytes)
                          let normBytes := joinAbsByteParts normParts
                          if repo.worktrees.any (fun w => w.rootPath == normBytes) then
                            if repo.worktrees.any (fun w => w.rootPath == normBytes && w.isLocked) then
                              .error { kind := .commandFailed, message := s!"'{opts.path}' is a missing but locked worktree" }
                            else if !opts.force then
                              .error { kind := .alreadyExists, message := s!"'{opts.path}' is a missing but already registered worktree" }
                            else
                              mkdirPVfsFuel 41 s.vfs cwdPartsForTarget (splitByteSlash wtBytes)
                          else
                            mkdirPVfsFuel 41 s.vfs cwdPartsForTarget (splitByteSlash wtBytes)
                      | .error _ =>
                        .error { kind := .commandFailed, message := s!"cannot create worktree '{opts.path}'" }
                    match destCheck with
                    | .error e => (.error e, sAfterBranch)
                    | .ok (vfs1, wtCanonParts) =>
                      let wtCanonBytes := joinAbsByteParts wtCanonParts
                      if repo.worktrees.any (fun w => w.rootPath == wtCanonBytes) &&
                          repo.worktrees.any (fun w => w.rootPath == wtCanonBytes && w.isLocked) then
                        (.error { kind := .commandFailed, message := s!"'{opts.path}' is a missing but locked worktree" }, sAfterBranch)
                      else
                      let regCollision :=
                        repo.worktrees.any (fun w => w.rootPath == wtCanonBytes) &&
                        (hasLinkedGitFileAtParts s.vfs wtCanonParts || !opts.force)
                      if regCollision then
                        (.error { kind := .alreadyExists, message := s!"worktree '{opts.path}' already registered" }, sAfterBranch)
                      else
                        let vfsWt := addChildAtParts vfs1 wtCanonParts ".git".toUTF8 (.file false "gitdir: .git\n".toUTF8)
                        match checkBrInUse? with
                        | some br =>
                          if !opts.force && isBranchCheckedOutAnywhere repo br then
                            (.error { kind := .branchInUse, message := s!"'{br.raw}' is already used by worktree" }, s)
                          else
                            let tree := match cid? with | some c => treeOfCommit repo c | none => []
                            let vfs2 := writeTreeToVfs vfsWt wtCanonParts tree
                            let slot : WorktreeSlot :=
                              { rootPath := wtCanonBytes, head := newHead, index := { entries := sortByBytes (·.1) tree } }
                            let repo' := { repo with worktrees := upsertWorktreeSlot repo.worktrees slot }
                            (.ok (), { s with vfs := vfs2, repos := updateRepoInList s.repos repo.commonDir (fun _ => repo') })
                        | none =>
                          let refs' :=
                            match newRef? with
                            | some (rn, c) => setRefInList repo.refs rn c
                            | none => repo.refs
                          let (ups', rems') :=
                            match newUp? with
                            | some (br, ur, rm, mr) =>
                              (setBranchUpstream repo.branchUpstreams br ur,
                               setBranchRemote repo.branchRemotes br rm mr)
                            | none => (repo.branchUpstreams, repo.branchRemotes)
                          match cid? with
                          | none =>
                            let slot : WorktreeSlot := { rootPath := wtCanonBytes, head := newHead }
                            let repo' :=
                              { repo with
                                refs := refs'
                                worktrees := upsertWorktreeSlot repo.worktrees slot
                                branchUpstreams := ups'
                                branchRemotes := rems' }
                            (.ok (), { s with vfs := vfsWt, repos := updateRepoInList s.repos repo.commonDir (fun _ => repo') })
                          | some cid =>
                            let newBranchInUse :=
                              match effNewBranch? with
                              | some nb => !opts.force && isBranchCheckedOutAnywhere repo nb
                              | none => false
                            if newBranchInUse then
                              (.error { kind := .branchInUse, message := "branch is already used by worktree" }, sAfterBranch)
                            else
                              let tree := treeOfCommit repo cid
                              let vfs2 := writeTreeToVfs vfsWt wtCanonParts tree
                              let slot : WorktreeSlot :=
                                { rootPath := wtCanonBytes, head := newHead, index := { entries := sortByBytes (·.1) tree } }
                              let repo' :=
                                { repo with
                                  refs := refs'
                                  worktrees := upsertWorktreeSlot repo.worktrees slot
                                  branchUpstreams := ups'
                                  branchRemotes := rems' }
                              (.ok (), { s with vfs := vfs2, repos := updateRepoInList s.repos repo.commonDir (fun _ => repo') })

private def isWorktreeDirtyForRemove (s : GitRepoState) (repo : RepoInstance) (wt : WorktreeSlot) : Bool :=
  let rootParts := splitByteSlash wt.rootPath
  if !isLiveDirAtParts s.vfs rootParts then false
  else if !wt.index.conflicts.isEmpty then true
  else
    match computeStatusEntries s repo wt with
    | .ok es => !es.isEmpty
    | .error _ => true

private def realpathForgivingParts (vfs : VfsNode) (cur : List ByteArray) :
    List ByteArray → List ByteArray
  | [] => cur
  | seg :: rest =>
    if seg == ".".toUTF8 then
      realpathForgivingParts vfs cur rest
    else if seg == "..".toUTF8 then
      realpathForgivingParts vfs cur.dropLast rest
    else
      match resolveVfsFuel 41 vfs cur [seg] true with
      | .ok (.dir cp true _ _) => realpathForgivingParts vfs cp rest
      | _ => cur ++ seg :: rest

/-- Pure `worktreeRemove` model step. -/
def stepWorktreeRemove (s : GitRepoState) (repoPath wtPath : String) (force : Bool) :
    Except GitError Unit × GitRepoState :=
  match validateFsPathArg repoPath, validateFsPathArg wtPath with
  | .error e, _ => (.error e, s)
  | _, .error e => (.error e, s)
  | .ok (), .ok () =>
    match resolveCwdAndDiscover s repoPath with
    | .error e => (.error e, s)
    | .ok (repo, _, _, canonRepoParts) =>
      let wtBytes := wtPath.toUTF8
      let cwdParts := if startsWithSlashByte wtBytes then [] else canonRepoParts
      let wtCanon? : Option ByteArray :=
        match resolveVfsFuel 41 s.vfs cwdParts (splitByteSlash wtBytes) true with
        | .ok (.dir cp _ _ _) => some (joinAbsByteParts cp)
        | _ =>
          if wtPath.endsWith "/" then none
          else
            let rawJoined := joinAbsByteParts (realpathForgivingParts s.vfs cwdParts (splitByteSlash wtBytes))
            if repo.worktrees.any (fun w => w.rootPath == rawJoined) then some rawJoined else none
      match wtCanon? with
      | none => (.error { kind := .notFound, message := s!"'{wtPath}' is not a working tree" }, s)
      | some wtCanon =>
        match repo.worktrees.head? with
        | some mainWt =>
          if wtCanon == mainWt.rootPath then
            (.error { kind := .commandFailed, message := s!"'{wtPath}' is a main working tree" }, s)
          else
            match repo.worktrees.find? (fun w => w.rootPath == wtCanon) with
            | none => (.error { kind := .notFound, message := s!"'{wtPath}' is not a working tree" }, s)
            | some wt =>
              if wt.isLocked then
                (.error { kind := .commandFailed, message := s!"cannot remove locked working tree '{wtPath}'" }, s)
              else if isLiveDirAtParts s.vfs (splitByteSlash wt.rootPath) &&
                  (!isSearchableDirAtParts s.vfs (splitByteSlash wt.rootPath) ||
                   (lookupNodeAtParts s.vfs (splitByteSlash wt.rootPath ++ [".git".toUTF8])).isNone) then
                (.error { kind := .notFound, message := s!"validation failed, cannot remove working tree: '{wtPath}/.git' does not exist" }, s)
              else if isLiveDirAtParts s.vfs (splitByteSlash wt.rootPath) &&
                  !hasLinkedGitFileAtParts s.vfs (splitByteSlash wt.rootPath) then
                (.error { kind := .commandFailed, message := s!"validation failed, cannot remove working tree: '{wtPath}/.git' is not a .git file" }, s)
              else if !force && isWorktreeDirtyForRemove s repo wt then
                (.error { kind := .dirtyWorktree, message := s!"'{wtPath}' contains modified or untracked files" }, s)
              else
                let wtParts := splitByteSlash wt.rootPath
                let (hadPermErr, vfs') :=
                  match wtParts.reverse with
                  | [] => (false, s.vfs)
                  | leaf :: revParent =>
                    let parentParts := revParent.reverse
                    if !isVfsChainWritable s.vfs parentParts [] then
                      (true, s.vfs)
                    else
                      match lookupNodeAtParts s.vfs wtParts with
                      | some wtNode =>
                        let (err, rem?) := removeDirNodeChecked wtNode
                        match rem? with
                        | none => (err, removeChildAtParts s.vfs parentParts leaf)
                        | some remNode => (true, addChildAtParts s.vfs parentParts leaf remNode)
                      | none => (false, s.vfs)
                let repo' := { repo with worktrees := repo.worktrees.filter (fun w => w.rootPath != wt.rootPath) }
                let s' := { s with vfs := vfs', repos := updateRepoInList s.repos repo.commonDir (fun _ => repo') }
                if hadPermErr then
                  (.error { kind := .commandFailed, message := s!"failed to delete '{wtPath}': Directory not empty" }, s')
                else
                  (.ok (), s')
        | none => (.error { kind := .notFound, message := s!"'{wtPath}' is not a working tree" }, s)

private def sameErrKind {α β : Type} (expected : Except GitError α) (actual : Except GitError β) : Bool :=
  match expected, actual with
  | .error e1, .error e2 => e1.kind == e2.kind && !e2.message.isEmpty
  | _, _ => false

private def allowsExtendedMutErrKind (k : GitErrorKind) : Bool :=
  k == .invalidRef || k == .commandFailed || k == .dirtyWorktree ||
  k == .conflict || k == .alreadyExists || k == .notFound || k == .branchInUse

/-- Relational specification for `revParseCommit` permitting extended revspecs resolved to existing commits. -/
def allowsRevParseCommit (s : GitRepoState) (repoPath rev : String) (res : Except GitError CommitId) : Bool :=
  if !isExtendedRevSpec rev then
    match (stepRevParseCommit s repoPath rev).1, res with
    | .ok c1, .ok c2 => c1 == c2
    | .error e1, .error e2 => e1.kind == e2.kind && !e2.message.isEmpty
    | _, _ => false
  else
    match validateFsPathArg repoPath with
    | .error e => sameErrKind (.error e : Except GitError Unit) res
    | .ok () =>
      if !isValidRevSpec rev then
        match res with | .error e => e.kind == .invalidInput && !e.message.isEmpty | _ => false
      else
        match resolveCwdAndDiscover s repoPath with
        | .error e => sameErrKind (.error e : Except GitError Unit) res
        | .ok (repo, wt?, _, _) =>
          match activeHeadSlot repo wt? with
          | none => match res with | .error e => e.kind == .notARepo && !e.message.isEmpty | _ => false
          | some _ =>
            match res with
            | .ok cid => hasCommit repo cid
            | .error e => (e.kind == .invalidRef || e.kind == .commandFailed) && !e.message.isEmpty

private def statusKindRank : Option StatusKind → Nat
  | none => 0
  | some .modified => 1
  | some .added => 2
  | some .deleted => 3
  | some .renamed => 4
  | some .copied => 5
  | some .typeChanged => 6
  | some .unmerged => 7
  | some .untracked => 8
  | some .ignored => 9

private def isUntrackedStatusEntry (e : StatusEntry) : Bool :=
  e.indexStatus == some .untracked && e.worktreeStatus == some .untracked

private def statusBucketSortedStrict : List StatusEntry → Bool
  | [] => true
  | e :: rest =>
    let rec go (prev : ByteArray) : List StatusEntry → Bool
      | [] => true
      | x :: xs =>
        let cur := x.path.toUTF8
        if cmpBytes prev cur == .lt then go cur xs else false
    go e.path.toUTF8 rest

private def expandStatusTracked (es : List StatusEntry) :
    Option (List (ByteArray × Option StatusKind × Option StatusKind)) :=
  es.foldlM
    (fun acc e =>
      if e.path.isEmpty then
        none
      else if e.indexStatus == some .renamed then
        match e.origPath with
        | some src =>
          if src.isEmpty || src == e.path || e.worktreeStatus == some .renamed ||
              e.worktreeStatus == some .copied || e.worktreeStatus == some .untracked then
            none
          else
            some ((src.toUTF8, some .deleted, none) ::
              (e.path.toUTF8, some .added, e.worktreeStatus) :: acc)
        | none => none
      else if e.origPath.isSome then
        none
      else
        some ((e.path.toUTF8, e.indexStatus, e.worktreeStatus) :: acc))
    []

private def sortStatusAtoms (xs : List (ByteArray × Option StatusKind × Option StatusKind)) :
    List (ByteArray × Option StatusKind × Option StatusKind) :=
  xs.mergeSort fun a b =>
    match cmpBytes a.1 b.1 with
    | .lt => true
    | .gt => false
    | .eq =>
      let ra1 := statusKindRank a.2.1
      let rb1 := statusKindRank b.2.1
      if ra1 != rb1 then ra1 < rb1
      else statusKindRank a.2.2 <= statusKindRank b.2.2

/-- Return `true` iff `actual` matches `expected` `git status --porcelain=v1 -z` output up to Git's rename pairing (`D`+`A` <-> `R`). -/
def statusEntriesMatchUpToRenames (expected actual : Array StatusEntry) : Bool :=
  let expTracked := expected.toList.takeWhile (fun e => !isUntrackedStatusEntry e)
  let expUntracked := expected.toList.dropWhile (fun e => !isUntrackedStatusEntry e)
  let actTracked := actual.toList.takeWhile (fun e => !isUntrackedStatusEntry e)
  let actUntracked := actual.toList.dropWhile (fun e => !isUntrackedStatusEntry e)
  actUntracked.all (fun e => isUntrackedStatusEntry e && e.origPath.isNone) &&
  statusBucketSortedStrict actTracked &&
  statusBucketSortedStrict actUntracked &&
  actUntracked == expUntracked &&
  match expandStatusTracked expTracked, expandStatusTracked actTracked with
  | some expAtoms, some actAtoms =>
    sortStatusAtoms expAtoms == sortStatusAtoms actAtoms
  | _, _ => false

/-- Return `true` iff the worktree at `wt` contains `.gitignore`, `.gitattributes`, a nested `.git` entry/repo, or tracked `.gitlink` entries. On ordinary repos this is `false`, so exact differential semantics apply. -/
def worktreeHasSpecialMetadata (s : GitRepoState) (repo : RepoInstance) (wt : WorktreeSlot)
    (extraTrees : List (List (ByteArray × GitTreeEntry)) := []) : Bool :=
  let wtNode := (lookupNodeAtParts s.vfs (splitByteSlash wt.rootPath)).getD VfsNode.emptyDir
  let treeHasSpecial (es : List (ByteArray × GitTreeEntry)) : Bool :=
    es.any fun (p, e) =>
      e.kind == .gitlink ||
      basenameBytes p == ".gitignore".toUTF8 ||
      basenameBytes p == ".gitattributes".toUTF8
  let hasNestedRepo := s.repos.any fun r =>
    r.commonDir != repo.commonDir && isPathPrefixBytes wt.rootPath r.commonDir
  hasNamedFileUnderNode ".gitignore".toUTF8 wtNode ||
  hasNamedFileUnderNode ".gitattributes".toUTF8 wtNode ||
  hasNestedGitUnderNode wtNode ||
  hasNestedRepo ||
  treeHasSpecial wt.index.entries ||
  extraTrees.any treeHasSpecial

/-- Return `true` iff `repoPath` resolves to a worktree carrying `.gitignore`, `.gitattributes`, nested `.git` repos, or tracked `.gitlink` entries. -/
def pathHasSpecialMetadata (s : GitRepoState) (repoPath : String) : Bool :=
  match resolveCwdAndDiscover s repoPath with
  | .ok (repo, some wt, _, _) =>
    let headTree :=
      match headCommitOfSymbolic repo wt.head with
      | some cid => treeOfCommit repo cid
      | none => []
    worktreeHasSpecialMetadata s repo wt [headTree]
  | _ => false

/-- Return `true` iff `res` is a valid `mergeBase?` result for `a` and `b` in `repoPath`, accepting any lowest common ancestor returned by stock `git merge-base` on criss-cross merges. -/
def allowsMergeBase (s : GitRepoState) (repoPath : String) (a b : CommitId)
    (res : Except GitError (Option CommitId)) : Bool :=
  match validateFsPathArg repoPath with
  | .error e => sameErrKind (.error e : Except GitError Unit) res
  | .ok () =>
    if !isValidCommitIdStr a.hex || !isValidCommitIdStr b.hex then
      match res with | .error e => e.kind == .invalidRef && !e.message.isEmpty | _ => false
    else
      match resolveCwdAndDiscover s repoPath with
      | .error e => sameErrKind (.error e : Except GitError Unit) res
      | .ok (repo, _, _, _) =>
        match resolveCommitIdArg? repo a, resolveCommitIdArg? repo b with
        | some cidA, some cidB =>
          let lcas := lowestCommonAncestors repo cidA cidB
          match res with
          | .ok none => lcas.isEmpty
          | .ok (some c) => lcas.any (· == c)
          | .error _ => false
        | _, _ =>
          match res with | .error e => e.kind == .invalidRef && !e.message.isEmpty | _ => false

private def statusEntriesWellFormed (actual : Array StatusEntry) : Bool :=
  let list := actual.toList
  let tracked := list.filter (fun e => e.indexStatus != some .untracked)
  let untracked := list.filter (fun e => e.indexStatus == some .untracked)
  tracked ++ untracked == list &&
  statusBucketSortedStrict tracked &&
  statusBucketSortedStrict untracked &&
  list.all fun e =>
    !e.path.isEmpty &&
    (match e.origPath with | some o => !o.isEmpty && o != e.path | none => true)

/-- Relational specification for `status` permitting Git's default similarity-based rename pairing while preserving all non-renamed entries, untracked entries, sorting, and blob-class invariants. Relaxes output matching to structural well-formedness when the worktree carries `.gitignore`, `.gitattributes`, or nested `.git`/gitlink metadata. -/
def allowsStatus (s : GitRepoState) (repoPath : String)
    (res : Except GitError (Array StatusEntry)) : Bool :=
  match resolveCwdAndDiscover s repoPath with
  | .ok (repo, some wt, _, _) =>
    let headTree :=
      match headCommitOfSymbolic repo wt.head with
      | some cid => treeOfCommit repo cid
      | none => []
    if worktreeHasSpecialMetadata s repo wt [headTree] then
      match res with
      | .ok actual => statusEntriesWellFormed actual
      | .error e =>
        let hasBadUtf8 :=
          headTree.any (fun (p, _) => (String.fromUTF8? p).isNone) ||
          wt.index.entries.any (fun (p, _) => (String.fromUTF8? p).isNone) ||
          wt.index.conflicts.any (fun c => (String.fromUTF8? c.path).isNone) ||
          (collectVfsFilesUnder s.vfs (splitByteSlash wt.rootPath)).any (fun (p, _) => (String.fromUTF8? p).isNone)
        hasBadUtf8 && e.kind == .parseError && !e.message.isEmpty
    else
      match (stepStatus s repoPath).1, res with
      | .ok expected, .ok actual =>
        statusEntriesMatchUpToRenames expected actual &&
        actual.all fun e =>
          if e.indexStatus == some .renamed then
            match e.origPath with
            | some src =>
              match lookupTreeEntry headTree src.toUTF8, lookupTreeEntry wt.index.entries e.path.toUTF8 with
              | some hE, some iE => isSameBlobClass hE.kind iE.kind
              | _, _ => false
            | none => false
          else
            true
      | .error e1, .error e2 => e1.kind == e2.kind && !e2.message.isEmpty
      | _, _ => false
  | _ =>
    match (stepStatus s repoPath).1, res with
    | .ok expected, .ok actual => expected == actual
    | .error e1, .error e2 => e1.kind == e2.kind && !e2.message.isEmpty
    | _, _ => false

private def diffKindRank : DiffKind → Nat
  | .added => 0
  | .copied _ => 1
  | .deleted => 2
  | .modified => 3
  | .renamed _ => 4
  | .typeChanged => 5
  | .unmerged => 6

private def diffEntriesSortedStrict : List DiffEntry → Bool
  | [] => true
  | e :: rest =>
    let rec go (prev : ByteArray) : List DiffEntry → Bool
      | [] => true
      | x :: xs =>
        let cur := x.path.toUTF8
        if cmpBytes prev cur == .lt then go cur xs else false
    go e.path.toUTF8 rest

private def expandDiffEntries (es : List DiffEntry) : Option (List (ByteArray × DiffKind)) :=
  es.foldlM
    (fun acc e =>
      if e.path.isEmpty then
        none
      else
        match e.kind with
        | .renamed score =>
          match e.origPath with
          | some src =>
            if score <= 100 && !src.isEmpty && src != e.path then
              some ((src.toUTF8, .deleted) :: (e.path.toUTF8, .added) :: acc)
            else
              none
          | none => none
        | _ =>
          if e.origPath.isSome then none
          else some ((e.path.toUTF8, e.kind) :: acc))
    []

private def sortDiffAtoms (xs : List (ByteArray × DiffKind)) : List (ByteArray × DiffKind) :=
  xs.mergeSort fun a b =>
    match cmpBytes a.1 b.1 with
    | .lt => true
    | .gt => false
    | .eq => diffKindRank a.2 <= diffKindRank b.2

/-- Return `true` iff `actual` matches `expected` `git diff --name-status -z` output up to Git's rename pairing (`D`+`A` <-> `R<score>`). -/
def diffEntriesMatchUpToRenames (expected actual : Array DiffEntry) : Bool :=
  diffEntriesSortedStrict actual.toList &&
  match expandDiffEntries expected.toList, expandDiffEntries actual.toList with
  | some expAtoms, some actAtoms =>
    sortDiffAtoms expAtoms == sortDiffAtoms actAtoms
  | _, _ => false

/-- Relational specification for `diffNameStatus` under Git's default rename detection, extended revspecs, extended CLI pathspecs, and worktree `.gitignore`/`.gitattributes`/nested-gitlink metadata. -/
def allowsDiffNameStatus (s : GitRepoState) (repoPath revA : String) (revB? : Option String)
    (paths : Array String) (res : Except GitError (Array DiffEntry)) : Bool :=
  let hasExtRev := isExtendedRevSpec revA || (revB?.any isExtendedRevSpec)
  let hasExtPath := paths.any isExtendedPathspec
  let specialWtDiff := revB?.isNone && pathHasSpecialMetadata s repoPath
  if !hasExtRev && !hasExtPath && !specialWtDiff then
    match (stepDiffNameStatus s repoPath revA revB? paths).1, res with
    | .ok a, .ok b => diffEntriesMatchUpToRenames a b
    | .error e1, .error e2 => e1.kind == e2.kind && !e2.message.isEmpty
    | _, _ => false
  else
    match validateFsPathArg repoPath with
    | .error e => sameErrKind (.error e : Except GitError Unit) res
    | .ok () =>
      if !isValidStrictRevSpec revA || !(revB?.all isValidStrictRevSpec) then
        match res with | .error e => e.kind == .invalidInput && !e.message.isEmpty | _ => false
      else if !paths.all isValidPathArg then
        match res with | .error e => e.kind == .invalidPath && !e.message.isEmpty | _ => false
      else
        match resolveCwdAndDiscover s repoPath with
        | .error e =>
          if e.kind == .notARepo && (revB?.isSome || !paths.isEmpty) then
            match res with | .error err => err.kind == .commandFailed && !err.message.isEmpty | _ => false
          else
            sameErrKind (.error e : Except GitError Unit) res
        | .ok (repo, wt?, cwdRel?, _) =>
          match activeHeadSlot repo wt? with
          | none => match res with | .error e => e.kind == .notARepo && !e.message.isEmpty | _ => false
          | some _ =>
            if revB?.isNone && wt?.isNone then
              match res with | .error e => e.kind == .notARepo && !e.message.isEmpty | _ => false
            else if wt?.isNone && !paths.isEmpty then
              match res with | .error e => e.kind == .commandFailed && !e.message.isEmpty | _ => false
            else
              let allNorm :=
                paths.isEmpty ||
                match wt? with
                | some wt =>
                  match String.fromUTF8? wt.rootPath with
                  | some rootStr => (normalizeCliPathspecs? rootStr cwdRel? paths).isSome
                  | none => false
                | none => true
              if !hasExtRev && !specialWtDiff && allNorm then
                match (stepDiffNameStatus s repoPath revA revB? paths).1, res with
                | .ok a, .ok b => diffEntriesMatchUpToRenames a b
                | .error e1, .error e2 => e1.kind == e2.kind && !e2.message.isEmpty
                | _, _ => false
              else if specialWtDiff && !hasExtRev && allNorm then
                let allowParseErr :=
                  repo.commits.any (fun c => c.tree.any (fun (p, _) => (String.fromUTF8? p).isNone)) ||
                  match wt? with
                  | none => false
                  | some wt =>
                    wt.index.entries.any (fun (p, _) => (String.fromUTF8? p).isNone) ||
                    wt.index.conflicts.any (fun c => (String.fromUTF8? c.path).isNone) ||
                    (collectVfsFilesUnder s.vfs (splitByteSlash wt.rootPath)).any (fun (p, _) => (String.fromUTF8? p).isNone)
                match (stepDiffNameStatus s repoPath revA revB? paths).1, res with
                | .ok _, .ok entries =>
                  diffEntriesSortedStrict entries.toList && entries.all (fun de => !de.path.isEmpty)
                | .error e1, .error e2 =>
                  (e1.kind == e2.kind || (allowParseErr && e2.kind == .parseError)) && !e2.message.isEmpty
                | .error e1, .ok entries =>
                  allowParseErr && e1.kind == .parseError &&
                  diffEntriesSortedStrict entries.toList && entries.all (fun de => !de.path.isEmpty)
                | .ok _, .error e2 =>
                  allowParseErr && e2.kind == .parseError && !e2.message.isEmpty
              else
                let allowParseErr :=
                  repo.commits.any (fun c => c.tree.any (fun (p, _) => (String.fromUTF8? p).isNone)) ||
                  match wt? with
                  | none => false
                  | some wt =>
                    wt.index.entries.any (fun (p, _) => (String.fromUTF8? p).isNone) ||
                    wt.index.conflicts.any (fun c => (String.fromUTF8? c.path).isNone) ||
                    (collectVfsFilesUnder s.vfs (splitByteSlash wt.rootPath)).any (fun (p, _) => (String.fromUTF8? p).isNone)
                match res with
                | .ok entries => entries.all (fun de => !de.path.isEmpty)
                | .error e =>
                  (e.kind == .invalidRef || e.kind == .commandFailed || e.kind == .notFound ||
                    e.kind == .invalidInput || (allowParseErr && e.kind == .parseError)) && !e.message.isEmpty

/-- Return `true` iff `paths` normalizes against the worktree at `repoPath` without needing an index witness. -/
def canNormalizeAddPathspecs (s : GitRepoState) (repoPath : String) (paths : Array String)
    (all : Bool) : Bool :=
  match resolveCwdAndDiscover s repoPath with
  | .ok (repo, some wt, cwdRel?, _) =>
    let headTree :=
      match headCommitOfSymbolic repo wt.head with
      | some cid => treeOfCommit repo cid
      | none => []
    if worktreeHasSpecialMetadata s repo wt [headTree] then false
    else if all && paths.isEmpty then true
    else
      match String.fromUTF8? wt.rootPath with
      | some wtRootStr => (normalizeCliPathspecs? wtRootStr cwdRel? paths).isSome
      | none => false
  | _ => true

/-- Witness-guided `add` transition for extended CLI pathspecs or worktrees with `.gitignore`/`.gitattributes`/nested-gitlink metadata. -/
def stepAddWithWitness (s : GitRepoState) (repoPath : String) (paths : Array String) (all : Bool)
    (witnessIdx? : Option IndexState) : Except GitError Unit × GitRepoState :=
  match validateFsPathArg repoPath with
  | .error e => (.error e, s)
  | .ok () =>
    if !all && paths.isEmpty then
      (.error { kind := .invalidInput, message := "add requires non-empty paths or all = true" }, s)
    else if !paths.all isValidPathArg then
      (.error { kind := .invalidPath, message := "invalid path passed to git add" }, s)
    else
      match resolveCwdAndDiscover s repoPath with
      | .error e => (.error e, s)
      | .ok (repo, wt?, cwdRel?, _) =>
        match wt? with
        | none => (.error { kind := .notARepo, message := "this operation must be run in a work tree" }, s)
        | some wt =>
          let headTree :=
            match headCommitOfSymbolic repo wt.head with
            | some cid => treeOfCommit repo cid
            | none => []
          let hasSpecial := worktreeHasSpecialMetadata s repo wt [headTree]
          let normalizable :=
            !hasSpecial &&
            ((all && paths.isEmpty) ||
            match String.fromUTF8? wt.rootPath with
            | some wtRootStr => (normalizeCliPathspecs? wtRootStr cwdRel? paths).isSome
            | none => false)
          if normalizable then
            stepAdd s repoPath paths all
          else
            match witnessIdx? with
            | some idx' =>
              let repo' := updateWorktreeInRepo repo wt.rootPath fun slot => { slot with index := idx' }
              (.ok (), { s with repos := updateRepoInList s.repos repo.commonDir (fun _ => repo') })
            | none =>
              (.error { kind := .commandFailed, message := "unsupported or outside-repository pathspec" }, s)

/-- Relational outcome check for `add` under extended CLI pathspecs or `.gitignore`/`.gitattributes`/nested-gitlink worktrees. -/
def allowsAdd (s : GitRepoState) (repoPath : String) (paths : Array String) (all : Bool)
    (witnessIdx? : Option IndexState) (res : Except GitError Unit) : Bool × GitRepoState :=
  let normalizable := canNormalizeAddPathspecs s repoPath paths all
  if normalizable then
    let (exp, s') := stepAdd s repoPath paths all
    match exp, res with
    | .ok (), .ok () => (true, s')
    | .error e1, .error e2 => (e1.kind == e2.kind && !e2.message.isEmpty, if e1.kind == e2.kind then s' else s)
    | _, _ => (false, s)
  else
    let (exp, sWithWit) := stepAddWithWitness s repoPath paths all witnessIdx?
    match exp, res with
    | .ok (), .ok () => (true, sWithWit)
    | .ok (), .error e2 =>
      if pathHasSpecialMetadata s repoPath &&
          (e2.kind == .commandFailed || e2.kind == .notFound || e2.kind == .invalidInput) &&
          !e2.message.isEmpty then
        (true, sWithWit)
      else
        (false, s)
    | .error e1, .error e2 =>
      if witnessIdx?.isNone && e1.kind == .commandFailed &&
          (e2.kind == .commandFailed || e2.kind == .notFound || e2.kind == .invalidInput) &&
          !e2.message.isEmpty then
        (true, s)
      else
        (e1.kind == e2.kind && !e2.message.isEmpty, if e1.kind == e2.kind then sWithWit else s)
    | _, _ => (false, s)

/-- Witness-guided `showFile?` transition for extended revspecs, preserving exact semantics once resolved. -/
def stepShowFileWithWitness (s : GitRepoState) (repoPath rev relPath : String)
    (witnessCid? : Option CommitId) : Except GitError (Option ByteArray) × GitRepoState :=
  if !isExtendedRevSpec rev then
    stepShowFile s repoPath rev relPath
  else
    match witnessCid? with
    | some cid =>
      match resolveCwdAndDiscover s repoPath with
      | .ok (repo, _, _, _) =>
        if hasCommit repo cid then stepShowFile s repoPath cid.hex relPath
        else (.error { kind := .invalidRef, message := s!"unknown commit '{cid.hex}'" }, s)
      | .error e => (.error e, s)
    | none =>
      match validateFsPathArg repoPath with
      | .error e => (.error e, s)
      | .ok () =>
        if !isValidStrictRevSpec rev then
          (.error { kind := .invalidInput, message := s!"invalid revision: '{rev}'" }, s)
        else
          match validateRelRepoPath relPath with
          | .error e => (.error e, s)
          | .ok () =>
            match resolveCwdAndDiscover s repoPath with
            | .error e => (.error e, s)
            | .ok (repo, wt?, _, _) =>
              match activeHeadSlot repo wt? with
              | none => (.error { kind := .notARepo, message := "missing worktree slot" }, s)
              | some _ => (.error { kind := .invalidRef, message := s!"unknown revision: '{rev}'" }, s)

/-- Relational outcome check for `showFile?` under extended revspecs. -/
def allowsShowFile (s : GitRepoState) (repoPath rev relPath : String)
    (witnessCid? : Option CommitId) (res : Except GitError (Option ByteArray)) : Bool :=
  let exp := (stepShowFileWithWitness s repoPath rev relPath witnessCid?).1
  match exp, res with
  | .ok a, .ok b => a == b
  | .error e1, .error e2 =>
    if isExtendedRevSpec rev && witnessCid?.isNone && e1.kind == .invalidRef then
      (e2.kind == .invalidRef || e2.kind == .commandFailed) && !e2.message.isEmpty
    else
      e1.kind == e2.kind && !e2.message.isEmpty
  | _, _ => false

/-- Witness-guided `createBranch` transition for extended revspecs. -/
def stepCreateBranchWithWitness (s : GitRepoState) (repoPath : String) (branch : RefName)
    (startPoint? : Option String) (force : Bool) (witnessCid? : Option CommitId) :
    Except GitError Unit × GitRepoState :=
  let ext := startPoint?.any isExtendedRevSpec
  if !ext then
    stepCreateBranch s repoPath branch startPoint? force
  else
    match validateFsPathArg repoPath with
    | .error e => (.error e, s)
    | .ok () =>
      if !isValidRefNameStr branch.raw then
        (.error { kind := .invalidRef, message := s!"invalid branch name: '{branch.raw}'" }, s)
      else if !(startPoint?.all isValidStrictRevSpec) then
        (.error { kind := .invalidInput, message := "invalid startPoint" }, s)
      else
        match resolveCwdAndDiscover s repoPath with
        | .error e => (.error e, s)
        | .ok (repo, wt?, _, _) =>
          match activeHeadSlot repo wt? with
          | none => (.error { kind := .notARepo, message := "missing worktree slot" }, s)
          | some _ =>
            let fullRef := "refs/heads/" ++ branch.raw
            if (lookupFullRef repo fullRef).isSome && !force then
              (.error { kind := .alreadyExists, message := s!"a branch named '{branch.raw}' already exists" }, s)
            else if (lookupFullRef repo fullRef).isSome && force && isBranchCheckedOutAnywhere repo branch then
              (.error { kind := .branchInUse, message := s!"cannot force update the branch '{branch.raw}' used by worktree" }, s)
            else
              match witnessCid? with
              | some cid =>
                if hasCommit repo cid then stepCreateBranch s repoPath branch (some cid.hex) force
                else (.error { kind := .invalidRef, message := s!"unknown commit '{cid.hex}'" }, s)
              | none => (.error { kind := .invalidRef, message := "unknown startPoint" }, s)

/-- Relational outcome check for `createBranch` under extended revspecs. -/
def allowsCreateBranch (s : GitRepoState) (repoPath : String) (branch : RefName)
    (startPoint? : Option String) (force : Bool) (witnessCid? : Option CommitId)
    (res : Except GitError Unit) : Bool × GitRepoState :=
  let (exp, s') := stepCreateBranchWithWitness s repoPath branch startPoint? force witnessCid?
  let ext := startPoint?.any isExtendedRevSpec
  match exp, res with
  | .ok (), .ok () => (true, s')
  | .error e1, .error e2 =>
    if ext && witnessCid?.isNone && e1.kind == .invalidRef && allowsExtendedMutErrKind e2.kind && !e2.message.isEmpty then
      (true, s)
    else
      (e1.kind == e2.kind && !e2.message.isEmpty, if e1.kind == e2.kind then s' else s)
  | _, _ => (false, s)

private def isExtendedCheckoutTarget : CheckoutTarget → Bool
  | .ref spec => isExtendedRevSpec spec
  | _ => false

/-- Witness-guided `checkout` transition for extended revspecs. -/
def stepCheckoutWithWitness (s : GitRepoState) (repoPath : String) (target : CheckoutTarget)
    (force : Bool) (witnessCid? : Option CommitId) (witnessBr? : Option RefName := none) :
    Except GitError Unit × GitRepoState :=
  if !isExtendedCheckoutTarget target then
    stepCheckout s repoPath target force
  else
    match validateFsPathArg repoPath with
    | .error e => (.error e, s)
    | .ok () =>
      let specOk :=
        match target with
        | .ref spec => isValidStrictRevSpec spec
        | _ => true
      if !specOk then
        (.error { kind := .invalidInput, message := "invalid revision" }, s)
      else
        match resolveCwdAndDiscover s repoPath with
        | .error e => (.error e, s)
        | .ok (repo, wt?, _, _) =>
          match wt? with
          | none => (.error { kind := .notARepo, message := "this operation must be run in a work tree" }, s)
          | some _ =>
            match witnessCid? with
            | some cid =>
              if hasCommit repo cid then
                match witnessBr? with
                | some br =>
                  if findBranchCommit? repo br == some cid then
                    stepCheckout s repoPath (.branch br) force
                  else
                    stepCheckout s repoPath (.commit cid) force
                | none => stepCheckout s repoPath (.commit cid) force
              else (.error { kind := .invalidRef, message := s!"unknown commit '{cid.hex}'" }, s)
            | none => (.error { kind := .invalidRef, message := "unknown revision" }, s)

/-- Relational outcome check for `checkout` under extended revspecs. -/
def allowsCheckout (s : GitRepoState) (repoPath : String) (target : CheckoutTarget) (force : Bool)
    (witnessCid? : Option CommitId) (res : Except GitError Unit) (witnessBr? : Option RefName := none) :
    Bool × GitRepoState :=
  let (exp, s') := stepCheckoutWithWitness s repoPath target force witnessCid? witnessBr?
  let ext := isExtendedCheckoutTarget target
  match exp, res with
  | .ok (), .ok () => (true, s')
  | .error e1, .error e2 =>
    if ext && witnessCid?.isNone && e1.kind == .invalidRef && allowsExtendedMutErrKind e2.kind && !e2.message.isEmpty then
      (true, s)
    else
      (e1.kind == e2.kind && !e2.message.isEmpty, if e1.kind == e2.kind then s' else s)
  | _, _ => (false, s)

/-- Witness-guided `switch` transition for extended revspecs. -/
def stepSwitchWithWitness (s : GitRepoState) (repoPath : String) (branch : RefName)
    (create : Bool) (startPoint? : Option String) (force : Bool) (witnessCid? : Option CommitId) :
    Except GitError Unit × GitRepoState :=
  let ext := startPoint?.any isExtendedRevSpec
  if !ext then
    stepSwitch s repoPath branch create startPoint? force
  else
    match validateFsPathArg repoPath with
    | .error e => (.error e, s)
    | .ok () =>
      if !isValidRefNameStr branch.raw then
        (.error { kind := .invalidRef, message := s!"invalid branch name: '{branch.raw}'" }, s)
      else if !create && startPoint?.isSome then
        (.error { kind := .invalidInput, message := "switch startPoint requires create = true" }, s)
      else if !(startPoint?.all isValidStrictRevSpec) then
        (.error { kind := .invalidInput, message := "invalid startPoint" }, s)
      else
        match resolveCwdAndDiscover s repoPath with
        | .error e => (.error e, s)
        | .ok (repo, wt?, _, _) =>
          match wt? with
          | none => (.error { kind := .notARepo, message := "this operation must be run in a work tree" }, s)
          | some _ =>
            match witnessCid? with
            | some cid =>
              if hasCommit repo cid then stepSwitch s repoPath branch create (some cid.hex) force
              else (.error { kind := .invalidRef, message := s!"unknown commit '{cid.hex}'" }, s)
            | none => (.error { kind := .invalidRef, message := "unknown startPoint" }, s)

/-- Relational outcome check for `switch` under extended revspecs. -/
def allowsSwitch (s : GitRepoState) (repoPath : String) (branch : RefName)
    (create : Bool) (startPoint? : Option String) (force : Bool) (witnessCid? : Option CommitId)
    (res : Except GitError Unit) : Bool × GitRepoState :=
  let (exp, s') := stepSwitchWithWitness s repoPath branch create startPoint? force witnessCid?
  let ext := startPoint?.any isExtendedRevSpec
  match exp, res with
  | .ok (), .ok () => (true, s')
  | .error e1, .error e2 =>
    if ext && witnessCid?.isNone && e1.kind == .invalidRef && allowsExtendedMutErrKind e2.kind && !e2.message.isEmpty then
      (true, s)
    else
      (e1.kind == e2.kind && !e2.message.isEmpty, if e1.kind == e2.kind then s' else s)
  | _, _ => (false, s)

/-- Witness-guided `reset` transition for extended revspecs. -/
def stepResetWithWitness (s : GitRepoState) (repoPath : String) (mode : ResetMode) (rev : String)
    (witnessCid? : Option CommitId) : Except GitError Unit × GitRepoState :=
  if !isExtendedRevSpec rev then
    stepReset s repoPath mode rev
  else
    match validateFsPathArg repoPath with
    | .error e => (.error e, s)
    | .ok () =>
      if !isValidStrictRevSpec rev then
        (.error { kind := .invalidInput, message := s!"invalid revision: '{rev}'" }, s)
      else
        match resolveCwdAndDiscover s repoPath with
        | .error e => (.error e, s)
        | .ok (repo, wt?, _, _) =>
          match activeHeadSlot repo wt? with
          | none => (.error { kind := .notARepo, message := "missing worktree slot" }, s)
          | some _ =>
            match witnessCid? with
            | some cid =>
              if hasCommit repo cid then stepReset s repoPath mode cid.hex
              else (.error { kind := .invalidRef, message := s!"unknown commit '{cid.hex}'" }, s)
            | none => (.error { kind := .invalidRef, message := "unknown revision" }, s)

/-- Relational outcome check for `reset` under extended revspecs. -/
def allowsReset (s : GitRepoState) (repoPath : String) (mode : ResetMode) (rev : String)
    (witnessCid? : Option CommitId) (res : Except GitError Unit) : Bool × GitRepoState :=
  let (exp, s') := stepResetWithWitness s repoPath mode rev witnessCid?
  let ext := isExtendedRevSpec rev
  match exp, res with
  | .ok (), .ok () => (true, s')
  | .error e1, .error e2 =>
    if ext && witnessCid?.isNone && e1.kind == .invalidRef && allowsExtendedMutErrKind e2.kind && !e2.message.isEmpty then
      (true, s)
    else
      (e1.kind == e2.kind && !e2.message.isEmpty, if e1.kind == e2.kind then s' else s)
  | _, _ => (false, s)

/-- Witness-guided `worktreeAdd` transition for extended revspec targets. -/
def stepWorktreeAddWithWitness (s : GitRepoState) (repoPath : String) (opts : WorktreeAddOptions)
    (witnessCid? : Option CommitId) (witnessBr? : Option RefName := none) :
    Except GitError Unit × GitRepoState :=
  let ext := opts.target?.any isExtendedRevSpec
  if !ext then
    stepWorktreeAdd s repoPath opts
  else
    match validateFsPathArg repoPath, validateFsPathArg opts.path with
    | .error e, _ => (.error e, s)
    | _, .error e => (.error e, s)
    | .ok (), .ok () =>
      if opts.detach && opts.newBranch?.isSome then
        (.error { kind := .invalidInput, message := "worktreeAdd cannot combine detach and newBranch" }, s)
      else if opts.newBranch?.any (fun b => !isValidRefNameStr b.raw) then
        (.error { kind := .invalidRef, message := "invalid branch name" }, s)
      else if !(opts.target?.all isValidStrictRevSpec) then
        (.error { kind := .invalidInput, message := "invalid worktree target" }, s)
      else
        match resolveCwdAndDiscover s repoPath with
        | .error e => (.error e, s)
        | .ok (repo, wt?, _, _) =>
          match activeHeadSlot repo wt? with
          | none => (.error { kind := .notARepo, message := "missing worktree slot" }, s)
          | some _ =>
            match witnessCid? with
            | some cid =>
              if hasCommit repo cid then
                let tgtStr :=
                  match witnessBr? with
                  | some br =>
                    if opts.newBranch?.isNone && !opts.detach && findBranchCommit? repo br == some cid then
                      br.raw
                    else cid.hex
                  | none => cid.hex
                stepWorktreeAdd s repoPath { opts with target? := some tgtStr }
              else (.error { kind := .invalidRef, message := s!"unknown commit '{cid.hex}'" }, s)
            | none => (.error { kind := .invalidRef, message := "unknown worktree target" }, s)

/-- Return `true` iff `act` is a plausible CLI stderr classification (`GitErrorKind`) when untrusted quote/newline/control characters can affect English `git` stderr text. On clean inputs (`spoofable = false`), requires exact equality `exp == act`. -/
def isCliStderrErrorKind : GitErrorKind → Bool
  | .notARepo | .nothingToCommit | .branchInUse | .dirtyWorktree | .conflict
  | .alreadyExists | .invalidRef | .notFound | .commandFailed => true
  | _ => false

/-- Return `true` iff string `s` contains characters (quotes or line breaks) that can spoof line/quote-masked `git` CLI diagnostics. -/
def hasStderrSpoofChar (s : String) : Bool :=
  s.any fun c => c == '\'' || c == '"' || c == '\n' || c == '\r'

/-- Relational `GitErrorKind` comparison: exact on normal inputs, allowing alternative CLI error kinds only when `spoofable` is `true` and both errors are CLI stderr classifications (never weakening `.invalidPath`, `.invalidInput`, `.timeout`, or `.parseError`). -/
def allowsCliErrorKind (spoofable : Bool) (exp act : GitErrorKind) : Bool :=
  exp == act || (spoofable && isCliStderrErrorKind exp && isCliStderrErrorKind act)

/-- Return `true` iff `target?` is a 40-hex or 64-hex string that also names an existing local branch in `repo`. -/
def isAmbiguousHexBranchTarget (s : GitRepoState) (repoPath : String) (opts : WorktreeAddOptions) : Bool :=
  match opts.target? with
  | some t =>
    (t.length == 40 || t.length == 64) && isValidCommitIdStr t &&
    match resolveCwdAndDiscover s repoPath with
    | .ok (repo, _, _, _) => (findBranchCommit? repo { raw := t }).isSome
    | .error _ => false
  | none => false

/-- Relational outcome check for `worktreeAdd` under extended revspecs and ambiguous 40/64-hex local branch names. -/
def allowsWorktreeAdd (s : GitRepoState) (repoPath : String) (opts : WorktreeAddOptions)
    (witnessCid? : Option CommitId) (res : Except GitError Unit) (witnessBr? : Option RefName := none) :
    Bool × GitRepoState :=
  let (exp, s') := stepWorktreeAddWithWitness s repoPath opts witnessCid? witnessBr?
  let ext := opts.target?.any isExtendedRevSpec
  let ambHex := isAmbiguousHexBranchTarget s repoPath opts
  match exp, res with
  | .ok (), .ok () => (true, s')
  | .error e1, .error e2 =>
    if (ext && witnessCid?.isNone && e1.kind == .invalidRef && allowsExtendedMutErrKind e2.kind ||
        ambHex && (e2.kind == .invalidRef || e2.kind == .alreadyExists || e2.kind == .branchInUse || e2.kind == .commandFailed)) &&
        !e2.message.isEmpty then
      (true, s)
    else
      (e1.kind == e2.kind && !e2.message.isEmpty, if e1.kind == e2.kind then s' else s)
  | _, _ => (false, s)

/-- Pure `GitApiM (StateM GitRepoState)` behavior model covering all 26 operations of `LeanSwe.Git`. -/
def evalGitApi : GitApiM (StateM GitRepoState) :=
  { isRepo := fun path s => stepIsRepo s path
    repoRoot := fun path s => stepRepoRoot s path
    commonDir := fun path s => stepCommonDir s path
    headCommit? := fun path s => stepHeadCommit s path
    headBranch? := fun path s => stepHeadBranch s path
    headState := fun path s => stepHeadState s path
    revParseCommit := fun path rev s => stepRevParseCommit s path rev
    isAncestor := fun path a b s => stepIsAncestor s path a b
    mergeBase? := fun path a b s => stepMergeBase s path a b
    status := fun path s => stepStatus s path
    diffNameStatus := fun path revA revB? paths s => stepDiffNameStatus s path revA revB? paths
    listWorktrees := fun path s => stepListWorktrees s path
    showFile? := fun path rev relPath s => stepShowFile s path rev relPath
    init := fun path bare initBranch? s => stepInit s path bare initBranch?
    clone := fun source target opts s => stepClone s source target opts
    add := fun path paths all s => stepAdd s path paths all
    commit := fun path opts s => stepCommitWithId s path opts none
    createBranch := fun path branch startPoint? force s => stepCreateBranch s path branch startPoint? force
    deleteBranch := fun path branch force s => stepDeleteBranch s path branch force
    checkout := fun path target force s => stepCheckout s path target force
    switch := fun path branch create startPoint? force s => stepSwitch s path branch create startPoint? force
    reset := fun path mode rev s => stepReset s path mode rev
    fetch := fun path remote refspec? prune s => stepFetch s path remote refspec? prune
    worktreeAdd := fun path opts s => stepWorktreeAdd s path opts
    worktreeRemove := fun path wtPath force s => stepWorktreeRemove s path wtPath force
    withWorktree := fun repoPath opts action => do
      match ← (fun s => stepWorktreeAdd s repoPath opts) with
      | .error e => return .error e
      | .ok () =>
        let (actRes, cleanRes) ← MonadFinally.tryFinally' (action opts.path) fun _ =>
          fun s => stepWorktreeRemove s repoPath opts.path opts.force
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
