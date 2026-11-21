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
  String.ofList ((s.toList.foldl (fun acc c => asciiLowerChar c :: acc) []).reverse)

/-- Return `true` iff `needle` appears in `haystack` under ASCII case-insensitive matching. -/
def containsSubstrCI (needle haystack : String) : Bool :=
  hasSubstrChars (asciiLower needle).toList (asciiLower haystack).toList

private def decodeUtf8LossyLoop : Nat → ByteArray → Nat → List Char → List Char
  | 0, _, _, acc => acc.reverse
  | fuel + 1, bs, i, acc =>
    if i >= bs.size then acc.reverse
    else
      let b0 := bs[i]!
      if b0 < 0x80 then
        decodeUtf8LossyLoop fuel bs (i + 1) (Char.ofNat b0.toNat :: acc)
      else if b0 >= 0xC2 && b0 <= 0xDF && i + 1 < bs.size then
        let b1 := bs[i + 1]!
        if (b1 &&& 0xC0) == 0x80 then
          let cp := ((b0.toNat &&& 0x1F) <<< 6) ||| (b1.toNat &&& 0x3F)
          decodeUtf8LossyLoop fuel bs (i + 2) (Char.ofNat cp :: acc)
        else
          decodeUtf8LossyLoop fuel bs (i + 1) (Char.ofNat 0xFFFD :: acc)
      else if b0 >= 0xE0 && b0 <= 0xEF && i + 2 < bs.size then
        let b1 := bs[i + 1]!
        let b2 := bs[i + 2]!
        let okLead :=
          (b0 != 0xE0 || b1 >= 0xA0) &&
          (b0 != 0xED || b1 <= 0x9F) &&
          (b1 &&& 0xC0) == 0x80 && (b2 &&& 0xC0) == 0x80
        if okLead then
          let cp :=
            ((b0.toNat &&& 0x0F) <<< 12) ||| ((b1.toNat &&& 0x3F) <<< 6) ||| (b2.toNat &&& 0x3F)
          decodeUtf8LossyLoop fuel bs (i + 3) (Char.ofNat cp :: acc)
        else
          decodeUtf8LossyLoop fuel bs (i + 1) (Char.ofNat 0xFFFD :: acc)
      else if b0 >= 0xF0 && b0 <= 0xF4 && i + 3 < bs.size then
        let b1 := bs[i + 1]!
        let b2 := bs[i + 2]!
        let b3 := bs[i + 3]!
        let okLead :=
          (b0 != 0xF0 || b1 >= 0x90) &&
          (b0 != 0xF4 || b1 <= 0x8F) &&
          (b1 &&& 0xC0) == 0x80 && (b2 &&& 0xC0) == 0x80 && (b3 &&& 0xC0) == 0x80
        if okLead then
          let cp :=
            ((b0.toNat &&& 0x07) <<< 18) ||| ((b1.toNat &&& 0x3F) <<< 12) |||
            ((b2.toNat &&& 0x3F) <<< 6) ||| (b3.toNat &&& 0x3F)
          decodeUtf8LossyLoop fuel bs (i + 4) (Char.ofNat cp :: acc)
        else
          decodeUtf8LossyLoop fuel bs (i + 1) (Char.ofNat 0xFFFD :: acc)
      else
        decodeUtf8LossyLoop fuel bs (i + 1) (Char.ofNat 0xFFFD :: acc)

/-- Decode `ByteArray` as UTF-8, replacing invalid byte sequences with U+FFFD. -/
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
    match String.fromUTF8? (bs.extract 0 (bs.size - 1)) with
    | some trimmed => trimmed
    | none => s
  else
    s

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

private def splitLinesCharsAux : List Char → List Char → List (List Char) → List (List Char)
  | [], cur, acc => (cur.reverse :: acc).reverse
  | '\n' :: rest, cur, acc => splitLinesCharsAux rest [] (cur.reverse :: acc)
  | c :: rest, cur, acc => splitLinesCharsAux rest (c :: cur) acc

private def lastCharIdxAux (target : Char) (idx : Nat) (best : Option Nat) : List Char → Option Nat
  | [] => best
  | c :: cs => lastCharIdxAux target (idx + 1) (if c == target then some idx else best) cs

private def maskDblQuotedLineAux (lastDbl? : Option Nat) :
    Nat → List Char → Bool → List Char → List Char
  | _, [], _, acc => acc.reverse
  | idx, c :: rest, inDbl, acc =>
    if inDbl then
      if lastDbl? == some idx then
        maskDblQuotedLineAux lastDbl? (idx + 1) rest false ('"' :: acc)
      else
        maskDblQuotedLineAux lastDbl? (idx + 1) rest true acc
    else if c == '"' && (match lastDbl? with | some ld => idx < ld | none => false) then
      maskDblQuotedLineAux lastDbl? (idx + 1) rest true ('"' :: acc)
    else
      maskDblQuotedLineAux lastDbl? (idx + 1) rest false (c :: acc)

private def maskSingleQuotedAux (lastQ? : Option Nat) :
    Nat → List Char → Bool → Bool → List Char → List Char
  | _, [], _, _, acc => acc.reverse
  | idx, c :: rest, inQuote, prevAlnum, acc =>
    if inQuote then
      if lastQ? == some idx then
        maskSingleQuotedAux lastQ? (idx + 1) rest false false ('\'' :: acc)
      else
        maskSingleQuotedAux lastQ? (idx + 1) rest true false acc
    else if c == '\'' && !prevAlnum && (match lastQ? with | some lq => idx < lq | none => false) then
      maskSingleQuotedAux lastQ? (idx + 1) rest true false ('\'' :: acc)
    else
      maskSingleQuotedAux lastQ? (idx + 1) rest false (isAsciiAlnumChar c) (c :: acc)

private def firstQuoteIsDblLoop : List Char → Bool
  | [] => false
  | '"' :: _ => true
  | '\'' :: _ => false
  | _ :: rest => firstQuoteIsDblLoop rest

private def findFirstSubstrIdx (pat : List Char) (idx : Nat) : List Char → Option Nat
  | [] => none
  | c :: rest =>
    if startsWithChars pat (c :: rest) then some idx
    else findFirstSubstrIdx pat (idx + 1) rest

private def findLastSubstrIdxAfter (pat : List Char) (minIdx idx : Nat) (best : Option Nat) :
    List Char → Option Nat
  | [] => best
  | c :: rest =>
    let best' := if idx >= minIdx && startsWithChars pat (c :: rest) then some idx else best
    findLastSubstrIdxAfter pat minIdx (idx + 1) best' rest

private def spliceRangeChars (keepEnd exclEnd : Nat) (idx : Nat) (acc : List Char) :
    List Char → List Char
  | [] => acc.reverse
  | cs@(c :: rest) =>
    if idx >= exclEnd then
      acc.foldl (fun tail ch => ch :: tail) cs
    else if idx < keepEnd then
      spliceRangeChars keepEnd exclEnd (idx + 1) (c :: acc) rest
    else
      spliceRangeChars keepEnd exclEnd (idx + 1) acc rest

private def isIgnoredClassifyLine (ln : List Char) : Bool :=
  match ln with
  | '\t' :: _ => true
  | _ =>
    let trimmed := ln.dropWhile (fun c => c == ' ')
    startsWithChars ['h', 'i', 'n', 't', ':'] trimmed

private def isDiagnosticHeaderLine (ln : List Char) : Bool :=
  let trimmed := ln.dropWhile (fun c => c == ' ')
  startsWithChars ['f', 'a', 't', 'a', 'l', ':'] trimmed ||
  startsWithChars ['e', 'r', 'r', 'o', 'r', ':'] trimmed ||
  startsWithChars ['w', 'a', 'r', 'n', 'i', 'n', 'g', ':'] trimmed ||
  startsWithChars ['h', 'i', 'n', 't', ':'] trimmed

private def skipLineCharsIdx (idx : Nat) : List Char → Nat × List Char
  | [] => (idx, [])
  | '\n' :: rest => (idx + 1, rest)
  | _ :: rest => skipLineCharsIdx (idx + 1) rest

private def scanLineLastSfx (sfx : List Char) (idx : Nat) (best : Nat) :
    List Char → Nat × Bool × Nat × List Char
  | [] => (best, false, idx, [])
  | '\n' :: rest => (best, true, idx + 1, rest)
  | cs@(_ :: rest) =>
    let best' := if startsWithChars sfx cs then idx else best
    scanLineLastSfx sfx (idx + 1) best' rest

private def hasCharBeforeNl (target : Char) : List Char → Bool
  | [] | '\n' :: _ => false
  | c :: rest => if c == target then true else hasCharBeforeNl target rest

private def probeAfterQuoteDiag (sfx : List Char) :
    Nat → Bool → Bool → Nat → List Char → Bool × Nat × List Char
  | 0, _, _, idx, cs => (true, idx, cs)
  | _, _, _, idx, [] => (true, idx, [])
  | f + 1, atLineStart, inDiagLine, idx, cs@(c :: rest) =>
    if atLineStart && isIgnoredClassifyLine cs then
      let (idx', skipped) := skipLineCharsIdx idx cs
      probeAfterQuoteDiag sfx f true false idx' skipped
    else
      let diagNow := if atLineStart then isDiagnosticHeaderLine cs else inDiagLine
      if startsWithChars sfx cs then
        (false, idx, cs)
      else if c == '\'' && diagNow && hasCharBeforeNl '\'' rest then
        (true, idx, cs)
      else
        probeAfterQuoteDiag sfx f (c == '\n') (if c == '\n' then false else diagNow) (idx + 1) rest

private def countQuotesNonIgnoredUpToTwo : Nat → Bool → Nat → List Char → Nat
  | 0, _, seen, _ | _, _, seen, [] => seen
  | f + 1, atLineStart, seen, cs@(c :: rest) =>
    if atLineStart && isIgnoredClassifyLine cs then
      let (_, skipped) := skipLineCharsIdx 0 cs
      countQuotesNonIgnoredUpToTwo f true seen skipped
    else if c == '\'' then
      if seen + 1 >= 2 then 2
      else countQuotesNonIgnoredUpToTwo f false (seen + 1) rest
    else
      countQuotesNonIgnoredUpToTwo f (c == '\n') seen rest

private def findQuoteSpanEndAux (sfx : List Char) (minIdx : Nat) :
    Nat → Nat → Option Nat → List Char → Option Nat
  | 0, _, best, _ | _, _, best, [] => best
  | f + 1, idx, best, cs@(_ :: rest) =>
    if idx >= minIdx && startsWithChars sfx cs then
      let (lineLastIdx, hasNl, afterNlIdx, afterNl) := scanLineLastSfx sfx (idx + 1) idx rest
      if !hasNl then
        some lineLastIdx
      else if !isDiagnosticHeaderLine afterNl then
        findQuoteSpanEndAux sfx minIdx f afterNlIdx (some lineLastIdx) afterNl
      else if sfx == ['\''] then
        let qCount := countQuotesNonIgnoredUpToTwo f true 0 afterNl
        if qCount == 0 || qCount >= 2 then
          some lineLastIdx
        else
          findQuoteSpanEndAux sfx minIdx f afterNlIdx (some lineLastIdx) afterNl
      else
        let (shouldStop, resumeIdx, resumeCs) := probeAfterQuoteDiag sfx f true true afterNlIdx afterNl
        if shouldStop then
          some lineLastIdx
        else
          findQuoteSpanEndAux sfx minIdx f resumeIdx (some lineLastIdx) resumeCs
    else
      findQuoteSpanEndAux sfx minIdx f (idx + 1) best rest

private def findQuoteSpanEndWithFuel (maxFuel : Nat) (sfx : List Char) (minIdx : Nat) (cs : List Char) : Option Nat :=
  findQuoteSpanEndAux sfx minIdx maxFuel minIdx none (cs.drop minIdx)

private def ignoredHeaderChars : List Char :=
  "the following paths are ignored by one of your .gitignore files:".toList

private def containsCharLoop (target : Char) : List Char → Bool
  | [] => false
  | c :: cs => if c == target then true else containsCharLoop target cs

private def isBenignStderrBanner (ln : List Char) : Bool :=
  let trimmed := ln.dropWhile (fun c => c == ' ')
  startsWithChars "cloning into ".toList trimmed ||
  startsWithChars "preparing worktree ".toList trimmed ||
  startsWithChars "from ".toList trimmed ||
  startsWithChars "switched to ".toList trimmed ||
  startsWithChars "already on ".toList trimmed ||
  startsWithChars "head is now at ".toList trimmed ||
  startsWithChars "branch ".toList trimmed

private def isSpanStopLine (ln : List Char) : Bool :=
  isDiagnosticHeaderLine ln ||
  isIgnoredClassifyLine ln ||
  isBenignStderrBanner ln ||
  (containsCharLoop ':' ln && (findFirstSubstrIdx ignoredHeaderChars 0 ln).isSome)

private def findUnquotedSpanEndAux (sfx : List Char) (minIdx : Nat) :
    Nat → Nat → Option Nat → List Char → Option Nat
  | 0, _, best, _ | _, _, best, [] => best
  | f + 1, idx, best, cs@(_ :: rest) =>
    if idx >= minIdx && startsWithChars sfx cs then
      let (lineLastIdx, hasNl, afterNlIdx, afterNl) := scanLineLastSfx sfx (idx + 1) idx rest
      if !hasNl || isSpanStopLine afterNl then
        some lineLastIdx
      else
        findUnquotedSpanEndAux sfx minIdx f afterNlIdx (some lineLastIdx) afterNl
    else
      findUnquotedSpanEndAux sfx minIdx f (idx + 1) best rest

private def findUnquotedSpanEndWithFuel (maxFuel : Nat) (sfx : List Char) (minIdx : Nat) (cs : List Char) : Option Nat :=
  if containsCharLoop '\n' sfx then
    findLastSubstrIdxAfter sfx minIdx minIdx none (cs.drop minIdx)
  else
    findUnquotedSpanEndAux sfx minIdx maxFuel minIdx none (cs.drop minIdx)

private def stripSpanAtIdxWithFuel (maxFuel : Nat) (dropBoundaryQuotes : Bool)
    (pIdx : Nat) (pfx sfx : List Char) (cs : List Char) : List Char × Bool :=
  let contentStart := pIdx + pfx.length
  let endIdx? :=
    if dropBoundaryQuotes then findQuoteSpanEndWithFuel maxFuel sfx contentStart cs
    else findUnquotedSpanEndWithFuel maxFuel sfx contentStart cs
  match endIdx? with
  | none => (cs, false)
  | some sIdx =>
    let keepEnd :=
      if dropBoundaryQuotes && pfx.getLast? == some '\'' then contentStart - 1 else contentStart
    let exclEnd :=
      if dropBoundaryQuotes && sfx.head? == some '\'' then sIdx + 1 else sIdx
    if keepEnd < exclEnd then
      (spliceRangeChars keepEnd exclEnd 0 [] cs, true)
    else
      (cs, false)

private def stripUnquotedSpanLoop (maxFuel : Nat) : Nat → List Char → List Char → List Char → List Char
  | 0, _, _, cs => cs
  | n + 1, pfx, sfx, cs =>
    match findFirstSubstrIdx pfx 0 cs with
    | none => cs
    | some pIdx =>
      let (cs', changed) := stripSpanAtIdxWithFuel maxFuel false pIdx pfx sfx cs
      if changed then stripUnquotedSpanLoop maxFuel n pfx sfx cs' else cs'

private def stripAfterLowerPrefixLoop (pfx : List Char) (acc : List Char) : List Char → List Char
  | [] => acc.reverse
  | c :: rest =>
    if startsWithChars pfx (c :: rest) then
      (pfx.foldl (fun a ch => ch :: a) acc).reverse
    else
      stripAfterLowerPrefixLoop pfx (c :: acc) rest

private def joinLinesCharsLoop (acc : List Char) : List (List Char) → List Char
  | [] => acc.reverse
  | [ln] => (ln.foldl (fun a c => c :: a) acc).reverse
  | ln :: rest =>
    let acc1 := '\n' :: ln.foldl (fun a c => c :: a) acc
    joinLinesCharsLoop acc1 rest

private def classifyQuoteSpanPatterns : List (List Char × List Char) :=
  [ ("pathspec '".toList, "' did not match".toList)
  , ("destination path '".toList, "' already exists".toList)
  , ("a branch named '".toList, "' already exists".toList)
  , ("fatal: '".toList, "' is already used by worktree".toList)
  , ("error: '".toList, "' is already used by worktree".toList)
  , ("fatal: '".toList, "' is already checked out".toList)
  , ("error: '".toList, "' is already checked out".toList)
  , (" used by worktree at '".toList, "'".toList)
  , (" checked out at '".toList, "'".toList)
  , ("fatal: '".toList, "' is not a valid branch name".toList)
  , ("fatal: '".toList, "' is not a working tree".toList)
  , ("cannot remove working tree: '".toList, "' does not exist".toList)
  , ("error: branch '".toList, "' not found".toList)
  , ("error: the branch '".toList, "' is not fully merged".toList)
  , ("error: cannot delete branch '".toList, "' used by worktree at '".toList)
  , ("fatal: repository '".toList, "' does not exist".toList)
  , ("fatal: ambiguous argument '".toList, "':".toList)
  , ("fatal: '".toList, "' does not appear to be a git repository".toList)
  , ("fatal: '".toList, "' does not exist".toList)
  , ("fatal: cannot change to '".toList, "':".toList)
  , ("fatal: cannot create directory at '".toList, "':".toList)
  , ("fatal: cannot create '".toList, "':".toList)
  , ("fatal: bad revision '".toList, "'".toList)
  , ("fatal: could not parse object '".toList, "'".toList)
  , ("fatal: could not reset index file to revision '".toList, "'".toList)
  , ("fatal: pathspec '".toList, "' is beyond a symbolic link".toList)
  , ("error: unable to index file '".toList, "'".toList)
  , ("fatal: refusing to fetch into branch '".toList, "' checked out at '".toList)
  , ("fatal: path '".toList, "' does not exist in '".toList)
  , ("fatal: '".toList, "' already exists".toList)
  , ("fatal: '".toList, "' is a missing but already registered worktree".toList)
  , ("fatal: '".toList, "' is a missing but locked worktree".toList)
  , ("fatal: '".toList, "' contains modified or untracked files".toList)
  , ("fatal: '".toList, "' is a main working tree".toList)
  , ("error: failed to delete '".toList, "':".toList)
  , ("error: '".toList, "' does not have a commit checked out".toList)
  , ("fatal: cannot opendir '".toList, "':".toList)
  , ("error: cannot stat '".toList, "':".toList)
  , ("fatal: cannot stat '".toList, "':".toList)
  , ("error: cannot lstat '".toList, "':".toList)
  , ("fatal: cannot lstat '".toList, "':".toList)
  , ("warning: unable to unlink '".toList, "':".toList)
  , ("error: unable to unlink '".toList, "':".toList)
  , ("error: failed to open file '".toList, "':".toList)
  , ("error: unable to unlink old '".toList, "':".toList)
  , ("error: unable to create file '".toList, "':".toList)
  , ("error: unable to create symlink '".toList, "':".toList)
  , ("error: unable to create '".toList, "':".toList)
  , ("fatal: unable to create '".toList, "':".toList)
  , ("error: cannot open '".toList, "':".toList)
  , ("fatal: cannot open '".toList, "':".toList)
  , ("error: cannot readlink '".toList, "':".toList)
  , ("fatal: cannot readlink '".toList, "':".toList)
  , ("error: could not open '".toList, "':".toList)
  , ("fatal: could not open '".toList, "':".toList)
  , ("error: could not open directory '".toList, "':".toList)
  , ("fatal: could not open directory '".toList, "':".toList)
  , ("fatal: could not create work tree dir '".toList, "':".toList)
  , ("fatal: could not create leading directories of '".toList, "':".toList)
  , ("warning: could not open directory '".toList, "':".toList)
  , ("warning: unable to access '".toList, "':".toList)
  , ("warning: failed to remove '".toList, "':".toList)
  , ("warning: could not stat '".toList, "':".toList)
  , ("cloning into '".toList, "'...".toList)
  , ("error: '".toList, "' does not look like a v2 or v3 bundle file".toList)
  ]

private def classifyOtherSpanPatterns : List (List Char × List Char) :=
  [ ("remote branch ".toList, " not found".toList)
  , ("unable to create file ".toList, ": permission denied".toList)
  , ("error: open(\"".toList, "\"):".toList)
  , ("fatal: cannot mkdir ".toList, ":".toList)
  , ("cannot remove a locked working tree, lock reason: ".toList, "\nuse 'remove -f -f'".toList)
  , ("fatal: invalid gitfile format: ".toList, "\nfatal: could not read".toList)
  , ("would be overwritten by checkout:\n".toList, "\naborting".toList)
  , ("would be overwritten by merge:\n".toList, "\naborting".toList)
  , ("would be removed by ".toList, "\naborting".toList)
  , ("the following paths are ignored by one of your .gitignore files:\n".toList, "\nhint: use -f".toList)
  ]

private def isQuotePatternLeadChar (c : Char) : Bool :=
  c == 'p' || c == 'd' || c == 'a' || c == 'f' ||
  c == 'e' || c == ' ' || c == 'c' || c == 'w'

private def lookupCachedLastIdx? (sfx : List Char) :
    List (List Char × Option Nat) → Option (Option Nat)
  | [] => none
  | (k, v) :: rest => if k == sfx then some v else lookupCachedLastIdx? sfx rest

private def matchQuotePatternAt (idx : Nat) (csAtIdx : List Char)
    (sfxCache : List (List Char × Option Nat)) :
    List (List Char × List Char) →
      Option (List Char × List Char) × List (List Char × Option Nat)
  | [] => (none, sfxCache)
  | (pfx, sfx) :: rest =>
    if startsWithChars pfx csAtIdx then
      let contentStart := idx + pfx.length
      let (lastIdx?, cache') :=
        match lookupCachedLastIdx? sfx sfxCache with
        | some cached => (cached, sfxCache)
        | none =>
          let computed := findLastSubstrIdxAfter sfx contentStart contentStart none (csAtIdx.drop pfx.length)
          (computed, (sfx, computed) :: sfxCache)
      match lastIdx? with
      | some lIdx =>
        if contentStart <= lIdx then (some (pfx, sfx), cache')
        else matchQuotePatternAt idx csAtIdx cache' rest
      | none =>
        matchQuotePatternAt idx csAtIdx cache' rest
    else
      matchQuotePatternAt idx csAtIdx sfxCache rest

private def findEarliestQuoteSpanLoop (idx : Nat)
    (sfxCache : List (List Char × Option Nat)) :
    List Char → Option (Nat × List Char × List Char)
  | [] => none
  | cs@(c :: rest) =>
    if isQuotePatternLeadChar c then
      let (hit?, cache') := matchQuotePatternAt idx cs sfxCache classifyQuoteSpanPatterns
      match hit? with
      | some (pfx, sfx) => some (idx, pfx, sfx)
      | none => findEarliestQuoteSpanLoop (idx + 1) cache' rest
    else
      findEarliestQuoteSpanLoop (idx + 1) sfxCache rest

private def stripQuoteSpansAux (maxFuel : Nat) : Nat → List Char → List Char
  | 0, cs => cs
  | n + 1, cs =>
    if !containsCharLoop '\'' cs then cs
    else
      match findEarliestQuoteSpanLoop 0 [] cs with
      | none => cs
      | some (pIdx, pfx, sfx) =>
        let (cs', changed) := stripSpanAtIdxWithFuel maxFuel true pIdx pfx sfx cs
        if changed then stripQuoteSpansAux maxFuel n cs' else cs'

private def sanitizeClassifyLine (ln : List Char) : List Char :=
  let maskSgl (xs : List Char) : List Char :=
    if containsCharLoop '\'' xs then
      let lq := lastCharIdxAux '\'' 0 none xs
      maskSingleQuotedAux lq 0 xs false false []
    else xs
  let maskDbl (xs : List Char) : List Char :=
    if containsCharLoop '"' xs then
      let ld := lastCharIdxAux '"' 0 none xs
      maskDblQuotedLineAux ld 0 xs false []
    else xs
  let m :=
    if firstQuoteIsDblLoop ln then maskSgl (maskDbl ln) else maskDbl (maskSgl ln)
  let s1 :=
    if containsCharLoop ':' m then
      stripAfterLowerPrefixLoop "invalid reference: ".toList [] m
    else m
  let s2 :=
    if containsCharLoop '\'' s1 then
      stripAfterLowerPrefixLoop "couldn't find remote ref ".toList [] s1
    else s1
  let s3 :=
    if containsCharLoop ':' s2 then
      stripAfterLowerPrefixLoop "fatal: not a valid object name ".toList [] s2
    else s2
  let s4 :=
    if containsCharLoop ':' s3 then
      stripAfterLowerPrefixLoop "error: short read while indexing ".toList [] s3
    else s3
  if containsCharLoop ':' s4 then
    stripAfterLowerPrefixLoop "fatal: invalid gitfile format: ".toList [] s4
  else s4

private def permDeniedSuffix : List Char :=
  ": permission denied".toList

private def dropThroughPermDenied : Nat → List (List Char) → Option (List (List Char))
  | 0, _ | _, [] => none
  | f + 1, ln :: rest =>
    if endsWithChars permDeniedSuffix ln then some rest
    else dropThroughPermDenied f rest

private def collapseRawPerrorLinesLoop :
    Nat → List (List Char) → List (List Char) → List (List Char)
  | 0, acc, rest => acc.reverse ++ rest
  | _ + 1, acc, [] => acc.reverse
  | f + 1, acc, ln :: rest =>
    if ln.isEmpty || isDiagnosticHeaderLine ln || isIgnoredClassifyLine ln || isBenignStderrBanner ln then
      collapseRawPerrorLinesLoop f (ln :: acc) rest
    else if endsWithChars permDeniedSuffix ln then
      collapseRawPerrorLinesLoop f (permDeniedSuffix :: acc) rest
    else
      match dropThroughPermDenied 8 rest with
      | some after => collapseRawPerrorLinesLoop f (permDeniedSuffix :: acc) after
      | none => collapseRawPerrorLinesLoop f (ln :: acc) rest

private def filterClassifyLinesLoop (inIgnored : Bool) (acc : List (List Char)) :
    List (List Char) → List (List Char)
  | [] => acc.reverse
  | ln :: rest =>
    if isIgnoredClassifyLine ln then
      let trimmed := ln.dropWhile (fun c => c == ' ')
      let nextIgnored := if startsWithChars ['h', 'i', 'n', 't', ':'] trimmed then false else inIgnored
      filterClassifyLinesLoop nextIgnored acc rest
    else if isDiagnosticHeaderLine ln then
      filterClassifyLinesLoop false (sanitizeClassifyLine ln :: acc) rest
    else if inIgnored then
      filterClassifyLinesLoop true acc rest
    else if containsCharLoop ':' ln && (findFirstSubstrIdx ignoredHeaderChars 0 ln).isSome then
      filterClassifyLinesLoop true (ignoredHeaderChars :: acc) rest
    else
      filterClassifyLinesLoop false (sanitizeClassifyLine ln :: acc) rest

/-- Lowercase and sanitize `git` diagnostic output prior to error-kind substring matching. -/
def sanitizeLowerForClassify (s : String) : List Char :=
  let lower := (s.toList.foldl (fun acc c => asciiLowerChar c :: acc) []).reverse
  let maxFuel := lower.length + 1
  let noSpans :=
    if containsCharLoop ':' lower || containsCharLoop ' ' lower then
      classifyOtherSpanPatterns.foldl (fun cur (p, q) => stripUnquotedSpanLoop maxFuel 16 p q cur) lower
    else lower
  let noQuotes :=
    if containsCharLoop '\'' noSpans then
      stripQuoteSpansAux maxFuel 64 noSpans
    else noSpans
  let rawLines := splitLinesCharsAux noQuotes [] []
  let lines :=
    if hasSubstrChars permDeniedSuffix noQuotes then
      collapseRawPerrorLinesLoop rawLines.length [] rawLines
    else
      rawLines
  let kept := filterClassifyLinesLoop false [] lines
  joinLinesCharsLoop [] kept

private def hasLowerSubstr (needle : String) (hayLower : List Char) : Bool :=
  hasSubstrChars needle.toList hayLower

private def hasFatalOrErrorChars (lower : List Char) : Bool :=
  let lines := splitLinesCharsAux lower [] []
  lines.any fun ln =>
    let trimmed := ln.dropWhile (fun c => c == ' ')
    startsWithChars ['f', 'a', 't', 'a', 'l', ':'] trimmed ||
    startsWithChars ['e', 'r', 'r', 'o', 'r', ':'] trimmed

/-- Classify a non-zero `git` subprocess result using `stderr`, falling back to `stdout` when `stderr` is blank. -/
def classifyError (cmd : String) (out : GitRawOutput) : GitError :=
  let errText := decodeUtf8Lossy out.stderr
  let outText := decodeUtf8Lossy out.stdout
  let errBlank := (trimAsciiWhitespace errText).isEmpty
  let diagSource :=
    if errBlank then outText else errText
  let combinedLower := sanitizeLowerForClassify diagSource
  let commitNothingOut :=
    !errBlank && cmd == "commit" && !hasFatalOrErrorChars combinedLower &&
      let outLower := sanitizeLowerForClassify outText
      (hasLowerSubstr "nothing to commit" outLower ||
       hasLowerSubstr "no changes added to commit" outLower ||
       hasLowerSubstr "nothing added to commit" outLower)
  let kind :=
    if hasLowerSubstr "not a git repository" combinedLower ||
       hasLowerSubstr "must be run in a work tree" combinedLower ||
       hasLowerSubstr "not allowed in a bare repository" combinedLower then
      .notARepo
    else if hasLowerSubstr "nothing to commit" combinedLower ||
            hasLowerSubstr "no changes added to commit" combinedLower ||
            hasLowerSubstr "nothing added to commit" combinedLower ||
            commitNothingOut then
      .nothingToCommit
    else if hasLowerSubstr "is already used by worktree" combinedLower ||
            hasLowerSubstr "is already checked out" combinedLower ||
            hasLowerSubstr "used by worktree" combinedLower then
      .branchInUse
    else if hasLowerSubstr "would be overwritten by" combinedLower ||
            hasLowerSubstr "would lose untracked files" combinedLower ||
            hasLowerSubstr "would be removed by" combinedLower ||
            hasLowerSubstr "local changes" combinedLower ||
            hasLowerSubstr "uncommitted changes" combinedLower ||
            hasLowerSubstr "contains modified or untracked files" combinedLower ||
            hasLowerSubstr "is not fully merged" combinedLower then
      .dirtyWorktree
    else if hasLowerSubstr "unresolved conflict" combinedLower ||
            hasLowerSubstr "merge conflict" combinedLower ||
            hasLowerSubstr "conflict (" combinedLower ||
            hasLowerSubstr "fix conflicts" combinedLower ||
            hasLowerSubstr "unmerged files" combinedLower ||
            hasLowerSubstr "unmerged path" combinedLower ||
            hasLowerSubstr "is unmerged" combinedLower ||
            hasLowerSubstr "needs merge" combinedLower ||
            hasLowerSubstr "resolve your current index first" combinedLower then
      .conflict
    else if hasLowerSubstr "already exists" combinedLower ||
            hasLowerSubstr "already registered" combinedLower then
      .alreadyExists
    else if hasLowerSubstr "unknown revision" combinedLower ||
            hasLowerSubstr "ambiguous argument" combinedLower ||
            hasLowerSubstr "ambiguous object name" combinedLower ||
            hasLowerSubstr "matched multiple" combinedLower ||
            hasLowerSubstr "a branch is expected" combinedLower ||
            hasLowerSubstr "expected commit type" combinedLower ||
            hasLowerSubstr "not a valid object name" combinedLower ||
            hasLowerSubstr "not a valid commit name" combinedLower ||
            hasLowerSubstr "needed a single revision" combinedLower ||
            hasLowerSubstr "not a valid branch point" combinedLower ||
            hasLowerSubstr "could not parse object" combinedLower ||
            hasLowerSubstr "bad revision" combinedLower ||
            hasLowerSubstr "bad object" combinedLower ||
            hasLowerSubstr "failed to resolve" combinedLower ||
            hasLowerSubstr "invalid reference" combinedLower ||
            hasLowerSubstr "unable to read tree" combinedLower ||
            hasLowerSubstr "reference is not a tree" combinedLower ||
            hasLowerSubstr "does not have any commits yet" combinedLower ||
            hasLowerSubstr "not a valid branch name" combinedLower ||
            (cmd == "checkout" &&
             hasLowerSubstr "pathspec" combinedLower &&
             hasLowerSubstr "did not match" combinedLower) then
      .invalidRef
    else if (hasLowerSubstr "pathspec" combinedLower && hasLowerSubstr "did not match" combinedLower) ||
            hasLowerSubstr "does not exist" combinedLower ||
            hasLowerSubstr "not a valid worktree" combinedLower ||
            hasLowerSubstr "is not a working tree" combinedLower ||
            hasLowerSubstr "couldn't find remote ref" combinedLower ||
            hasLowerSubstr "no such file or directory" combinedLower ||
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

/-- Resolve probe `cwd` by joining optional base `cwd?` with ancestor candidate `cand`. -/
def joinProbeCwd (base? : Option String) (cand : String) : Option String :=
  match base? with
  | none => some cand
  | some base =>
    if cand.startsWith "/" then some cand
    else if cand == "." then some base
    else
      let cleanBase := stripTrailingSlashes base
      if cleanBase == "/" then some ("/" ++ cand)
      else if cleanBase.toList.isEmpty then some cand
      else some (cleanBase ++ "/" ++ cand)

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
          let stripped :=
            if raw.startsWith "refs/heads/" then
              String.ofList (raw.toList.drop 11)
            else
              raw
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

/-- Compute the lexicographically smallest lowest common ancestor of two commits, or `none` if disjoint. -/
def mergeBaseImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath : String) (a b : CommitId) : m (Except GitError (Option CommitId)) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    if !isValidCommitIdStr a.hex || !isValidCommitIdStr b.hex then
      return .error { kind := .invalidRef, message := "invalid commit ID argument" }
    match ← runGitRaw ops
        { cwd := some repoPath, args := #["merge-base", "--all", a.hex, b.hex] } with
    | .error e => return .error e
    | .ok out =>
      if out.exitCode == 0 then
        match decodeUtf8Checked out.stdout with
        | .error e => return .error e
        | .ok s =>
          let lines := ((s.splitOn "\n").map trimAsciiWhitespace).filter (!·.isEmpty)
          match lines.mapM mkCommitId with
          | .error e => return .error e
          | .ok cids =>
            let minCid? := cids.foldl
              (fun best c =>
                match best with
                | none => some c
                | some b => if c.hex < b.hex then some c else some b)
              none
            match minCid? with
            | some cid => return .ok (some cid)
            | none => return .error { kind := .parseError, message := "empty merge-base --all output" }
      else if out.exitCode == 1 && (classifyError "merge-base" out).kind == .commandFailed &&
          !hasFatalOrErrorChars (sanitizeLowerForClassify (decodeUtf8Lossy out.stderr)) then
        return .ok none
      else
        return .error (classifyError "merge-base" out)

/-- Query `git status --porcelain=v1 --find-renames=100% -z` and parse all entries. -/
def statusImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m) (repoPath : String) :
    m (Except GitError (Array StatusEntry)) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    match ← runGitChecked ops "status"
        { cwd := some repoPath, args := #["status", "--porcelain=v1", "--find-renames=100%", "--untracked-files=normal", "-z"] } with
    | .error e => return .error e
    | .ok out => return parsePorcelainStatusZ out.stdout

/-- Query `git diff --name-status --find-renames=100% -z` between `revA` and optional `revB?`. -/
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
      let args :=
        #["diff", "--name-status", "--find-renames=100%", "-z", revA] ++
        rbArgs ++ #["--"] ++ paths
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

/-- Initialize a new repository at `path` (re-init allowed only at matching existing repo root). -/
def initImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (path : String) (bare : Bool) (initialBranch? : Option RefName) : m (Except GitError Unit) := do
  match validateRepoPath path with
  | .error e => return .error e
  | .ok () =>
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

/-- Create a commit with validated message and optional author/committer overrides. -/
def commitImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath : String) (opts : CommitOptions) : m (Except GitError CommitId) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    match validateCommitOptions opts with
    | .error e => return .error e
    | .ok () =>
      let nEnv :=
        match opts.authorName with
        | none => #[]
        | some n => #[("GIT_AUTHOR_NAME", some n), ("GIT_COMMITTER_NAME", some n)]
      let eEnv :=
        match opts.authorEmail with
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

/-- Scan `git ls-remote --refs` output for any remote ref mapping to a `HEAD`-shadowing destination. -/
def findGlobShadowHit (srcPfx dstPfx : String) (lsStdout : ByteArray) : Option String :=
  let lines := ((decodeUtf8Lossy lsStdout).splitOn "\n").map trimAsciiWhitespace
  lines.findSome? fun ln =>
    match ln.splitOn "\t" with
    | [_, sRef] =>
      if sRef.startsWith srcPfx then
        let suffix := String.ofList (sRef.toList.drop srcPfx.toList.length)
        let dRef := dstPfx ++ suffix
        if isHeadShadowingRef dRef then some dRef else none
      else none
    | _ => none

/-- Reject glob fetch refspecs whose remote matches would write a `HEAD`-shadowing local ref. -/
def checkGlobHeadShadow {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath remote : String) (pf : ParsedFetchRefspec) : m (Except GitError Unit) := do
  if !canGlobShadowHead pf then
    return .ok ()
  match ← runGitChecked ops "rev-parse"
      { cwd := some repoPath, args := #["rev-parse", "--git-dir"] } with
  | .error e => return .error e
  | .ok _ =>
    match ← runGitChecked ops "ls-remote"
        { cwd := some repoPath, args := #["ls-remote", "--refs", "--", remote, pf.src ++ "/*"] } with
    | .error e => return .error e
    | .ok lsOut =>
      let srcPfx := pf.src ++ "/"
      let dstPfx := (pf.dst?.getD pf.src) ++ "/"
      match findGlobShadowHit srcPfx dstPfx lsOut.stdout with
      | some dRef =>
        return .error
          { kind := .commandFailed
            command := some "fetch"
            message := s!"refusing to fetch into HEAD-shadowing ref '{dRef}'" }
      | none => return .ok ()

/-- Fetch non-interactively from `remote` with optional `refspec?` and `prune`. -/
def fetchImpl {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath remote : String) (refspec? : Option String) (prune : Bool) :
    m (Except GitError Unit) := do
  match validateRepoPath repoPath with
  | .error e => return .error e
  | .ok () =>
    if !isValidRemoteOrRefspec remote then
      return .error { kind := .invalidInput, message := s!"invalid remote name: '{remote}'" }
    let refRes : Except GitError (Array String × Option ParsedFetchRefspec) :=
      match refspec? with
      | none => .ok (#[], none)
      | some r =>
        match parseFetchRefspec? r with
        | some pf => .ok (#[r], some pf)
        | none => .error { kind := .invalidInput, message := s!"invalid refspec: '{r}'" }
    match refRes with
    | .error e => return .error e
    | .ok (rArgs, pf?) =>
      let shadowCheck ←
        match pf? with
        | none => pure (.ok ())
        | some pf => checkGlobHeadShadow ops repoPath remote pf
      match shadowCheck with
      | .error e => return .error e
      | .ok () =>
        let args := #["fetch"] ++ (if prune then #["--prune"] else #[]) ++ #[remote] ++ rArgs
        match ← runGitChecked ops "fetch" { cwd := some repoPath, args := args } with
        | .error e => return .error e
        | .ok _ => return .ok ()

/-- Normalize a worktree path for matching against `git worktree list --porcelain`. -/
def normalizeWtProbePath (p : String) : String :=
  if p.startsWith "/" then
    (String.fromUTF8? (joinAbsByteParts (normalizeDotDotParts [] (splitByteSlash p.toUTF8)))).getD
      (stripTrailingSlashes p)
  else
    stripTrailingSlashes p

/-- Scan `git worktree list --porcelain` stdout for whether `wtNorm?` is registered and whether it is locked. -/
def findPorcelainWorktreeDestFlags (stdout : ByteArray) (wtNorm? : Option String) : Bool × Bool :=
  let stanzas := (decodeUtf8Lossy stdout).splitOn "\n\n"
  stanzas.foldl
    (fun (acc : Bool × Bool) stz =>
      let lines := (stz.splitOn "\n").map trimAsciiWhitespace
      let matchesDest :=
        match wtNorm? with
        | some wn => lines.any (fun ln => ln == "worktree " ++ wn)
        | none => false
      if !matchesDest then acc
      else
        let isLocked := lines.any (fun ln => ln == "locked" || ln.startsWith "locked ")
        (true, acc.2 || isLocked))
    (false, false)

/-- Attach a new worktree to a 40-hex local branch name when `t` is not an existing commit SHA, falling back to `defaultArgs`. -/
def worktreeAddMaybe40HexBranch {m : Type → Type} [Monad m] (ops : RawGitOpsM m)
    (repoPath : String) (opts : WorktreeAddOptions) (t : String) (defaultArgs : Array String) :
    m (Except GitError Unit) := do
  match ← runGitRaw ops
      { cwd := some repoPath, args := #["rev-parse", "-q", "--verify", t ++ "^{commit}"] } with
  | .error e => return .error e
  | .ok revOut =>
    if revOut.exitCode == 0 then
      match ← runGitChecked ops "worktree" { cwd := some repoPath, args := defaultArgs } with
      | .error e => return .error e
      | .ok _ => return .ok ()
    else
      match ← runGitRaw ops
          { cwd := some repoPath, args := #["show-ref", "--verify", "--quiet", "refs/heads/" ++ t] } with
      | .error e => return .error e
      | .ok refOut =>
        if refOut.exitCode != 0 then
          match ← runGitChecked ops "worktree" { cwd := some repoPath, args := defaultArgs } with
          | .error e => return .error e
          | .ok _ => return .ok ()
        else
          match ← runGitChecked ops "worktree"
              { cwd := some repoPath, args := #["worktree", "list", "--porcelain"] } with
          | .error e => return .error e
          | .ok wtOut =>
            let wtLines := ((decodeUtf8Lossy wtOut.stdout).splitOn "\n").map trimAsciiWhitespace
            let inUse := !opts.force && wtLines.contains ("branch refs/heads/" ++ t)
            let wtCwd := joinProbeCwd (some repoPath) opts.path
            let wtNorm? := wtCwd.map normalizeWtProbePath
            let (isRegistered, isLocked) := findPorcelainWorktreeDestFlags wtOut.stdout wtNorm?
            if isLocked then
              return .error { kind := .commandFailed, command := some "worktree", message := s!"'{opts.path}' is a missing but locked worktree" }
            else if isRegistered && !opts.force then
              return .error { kind := .alreadyExists, command := some "worktree", message := s!"worktree '{opts.path}' already registered" }
            else if inUse then
              let dirRes ← runGitRaw ops { cwd := wtCwd, args := #["version"] }
              let earlyErr? : Option GitError :=
                match dirRes with
                | .error e =>
                  if e.kind == .invalidPath || e.kind == .invalidInput || e.kind == .timeout then some e
                  else none
                | .ok _ => none
              match earlyErr? with
              | some e => return .error e
              | none =>
                let isFileErr :=
                  match dirRes with
                  | .ok dirOut => dirOut.exitCode != 0 && containsSubstrCI "not a directory" (decodeUtf8Lossy dirOut.stderr)
                  | .error _ => false
                if isFileErr then
                  return .error { kind := .alreadyExists, command := some "worktree", message := s!"'{opts.path}' already exists" }
                else
                  return .error { kind := .branchInUse, command := some "worktree", message := s!"'{t}' is already used by worktree" }
            else
              let detArgs :=
                #["worktree", "add"] ++ (if opts.force then #["--force"] else #[]) ++
                #["--detach", "--", opts.path, "refs/heads/" ++ t]
              match ← runGitChecked ops "worktree" { cwd := some repoPath, args := detArgs } with
              | .error e => return .error e
              | .ok _ =>
                match ← runGitChecked ops "symbolic-ref"
                    { cwd := wtCwd, args := #["symbolic-ref", "HEAD", "refs/heads/" ++ t] } with
                | .error e =>
                  let _ ← runGitChecked ops "worktree"
                    { cwd := some repoPath, args := #["worktree", "remove", "--force", "--", opts.path] }
                  return .error e
                | .ok _ => return .ok ()

/-- Create a linked worktree via `git worktree add`, validating branch/target options. -/
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
          if !opts.detach && bArgs.isEmpty then
            match opts.target? with
            | some t =>
              if isValidCommitIdStr t && t.length == 40 then
                worktreeAddMaybe40HexBranch ops repoPath opts t args
              else
                match ← runGitChecked ops "worktree" { cwd := some repoPath, args := args } with
                | .error e => return .error e
                | .ok _ => return .ok ()
            | none =>
              match ← runGitChecked ops "worktree" { cwd := some repoPath, args := args } with
              | .error e => return .error e
              | .ok _ => return .ok ()
          else
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
