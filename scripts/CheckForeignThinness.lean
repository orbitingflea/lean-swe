import Lean

/-!
Non-Lean thinness CI gate (`scripts/CheckForeignThinness.lean`).

Enforces two rules against `.foreign-budget.json`:
1. Every git-tracked non-Lean file outside static metadata must be registered in
   `.foreign-budget.json` (`files` or `vendored_files`), with `actual_lines <= max_lines`
   and exact SHA-256 verification on `vendored_files`.
2. Every non-`legacy_unmigrated` `.c`/`.h` file in `files` is lexed (stripping comments,
   string/char literals, and tracking preprocessor tokens) and checked per extracted function
   against complexity, branch, loop, and thick-logic bans unless explicitly overridden.
-/

open Lean

private def staticMetadataFiles : Std.HashSet String :=
  Std.HashSet.emptyWithCapacity 16
    |>.insert ".gitignore"
    |>.insert ".gitattributes"
    |>.insert "LICENSE"
    |>.insert "README.md"
    |>.insert "lean-toolchain"
    |>.insert "lake-manifest.json"
    |>.insert ".proof-memory.json"
    |>.insert ".foreign-budget.json"

private structure FileBudget where
  maxLines : Nat
  legacyUnmigrated : Bool
  deriving Inhabited

private structure VendoredBudget where
  sha256 : String
  maxLines? : Option Nat
  deriving Inhabited

private structure FuncOverride where
  maxCodeLines : Nat := 35
  maxBranches : Nat := 8
  allowArrayCopyLoop : Bool := false
  maxLoops? : Option Nat := none
  allowPoll : Bool := false
  deriving Inhabited

private structure ForeignBudget where
  files : Std.HashMap String FileBudget
  vendored : Std.HashMap String VendoredBudget
  overrides : Std.HashMap String FuncOverride
  threadHelpers : Std.HashSet String

private inductive CTokKind where
  | ident (name : String)
  | lbrace
  | rbrace
  | lparen
  | rparen
  | lt
  | qmark
  | semi
  | eq
  | dotOrArrow
  | hash
  | tokenPaste
  | digraph
  | strLit (val : String)
  | lit
  | other
  deriving BEq, Inhabited

private structure CTok where
  kind : CTokKind
  line : Nat
  inPreproc : Bool
  preprocId : Nat := 0
  deriving Inhabited

private structure CFunc where
  name : String
  body : Array CTok
  deriving Inhabited

private def isSpaceByte (b : UInt8) : Bool :=
  b == 32 || b == 9 || b == 13 || b == 11 || b == 12

private def isDigitByte (b : UInt8) : Bool :=
  b >= 48 && b <= 57

private def isIdentStartByte (b : UInt8) : Bool :=
  (b >= 65 && b <= 90) || (b >= 97 && b <= 122) || b == 95

private def isIdentContByte (b : UInt8) : Bool :=
  isIdentStartByte b || isDigitByte b

private def isDigraphPair (a b : UInt8) : Bool :=
  (a == 60 && b == 37) || (a == 37 && b == 62) ||
  (a == 60 && b == 58) || (a == 58 && b == 62) ||
  (a == 37 && b == 58)

private def bytesSliceToAsciiString (bytes : ByteArray) (start stop : Nat) : String := Id.run do
  let mut s := ""
  for i in [start : stop] do
    let b := bytes[i]!
    s := s.push (Char.ofNat b.toNat)
  return s

private def countLinesBytes (bytes : ByteArray) : Nat := Id.run do
  if bytes.isEmpty then
    return 0
  let mut count := 0
  for i in [0 : bytes.size] do
    if bytes[i]! == 10 then
      count := count + 1
  if bytes[bytes.size - 1]! != 10 then
    count := count + 1
  return count

private def stripLineSplices (bytes : ByteArray) : ByteArray × Array Nat := Id.run do
  let n := bytes.size
  let mut out := ByteArray.emptyWithCapacity n
  let mut lines := Array.mkEmpty n
  let mut i := 0
  let mut origLine := 1
  while i < n do
    let b := bytes[i]!
    if b == 92 && i + 1 < n && bytes[i + 1]! == 10 then
      origLine := origLine + 1
      i := i + 2
    else if b == 92 && i + 2 < n && bytes[i + 1]! == 13 && bytes[i + 2]! == 10 then
      origLine := origLine + 1
      i := i + 3
    else
      out := out.push b
      lines := lines.push origLine
      if b == 10 then
        origLine := origLine + 1
      i := i + 1
  return (out, lines)

private def lexCBytes (rawBytes : ByteArray) : Array CTok := Id.run do
  let (bytes, lineMap) := stripLineSplices rawBytes
  let n := bytes.size
  let mut i := 0
  let mut atLineStart := true
  let mut inPreproc := false
  let mut curPreprocId : Nat := 0
  let mut tokens : Array CTok := #[]
  while i < n do
    let b := bytes[i]!
    let line := lineMap[i]!
    if b == 10 then
      atLineStart := true
      inPreproc := false
      i := i + 1
    else if isSpaceByte b then
      i := i + 1
    else if b == 47 && i + 1 < n && bytes[i + 1]! == 42 then
      i := i + 2
      while i < n do
        if bytes[i]! == 42 && i + 1 < n && bytes[i + 1]! == 47 then
          i := i + 2
          break
        if bytes[i]! == 10 && !inPreproc then
          atLineStart := true
        i := i + 1
    else if b == 47 && i + 1 < n && bytes[i + 1]! == 47 then
      i := i + 2
      while i < n do
        if bytes[i]! == 10 then
          atLineStart := true
          inPreproc := false
          i := i + 1
          break
        i := i + 1
    else if b == 34 || b == 39 then
      let quote := b
      let startLine := line
      atLineStart := false
      i := i + 1
      let litStart := i
      let mut litEnd := i
      while i < n do
        let c := bytes[i]!
        if c == 92 then
          if i + 1 < n then
            i := i + 2
          else
            i := i + 1
          litEnd := i
        else if c == quote then
          litEnd := i
          i := i + 1
          break
        else if c == 10 then
          litEnd := i
          i := i + 1
          break
        else
          i := i + 1
          litEnd := i
      let kind : CTokKind :=
        if quote == 34 then .strLit (bytesSliceToAsciiString bytes litStart litEnd)
        else .lit
      tokens := tokens.push { kind, line := startLine, inPreproc, preprocId := if inPreproc then curPreprocId else 0 }
    else if i + 1 < n && isDigraphPair b bytes[i + 1]! then
      atLineStart := false
      tokens := tokens.push { kind := .digraph, line, inPreproc, preprocId := if inPreproc then curPreprocId else 0 }
      i := i + 2
    else if b == 35 then
      if i + 1 < n && bytes[i + 1]! == 35 then
        tokens := tokens.push { kind := .tokenPaste, line, inPreproc, preprocId := if inPreproc then curPreprocId else 0 }
        atLineStart := false
        i := i + 2
      else
        if atLineStart then
          inPreproc := true
          curPreprocId := curPreprocId + 1
        tokens := tokens.push { kind := .hash, line, inPreproc, preprocId := if inPreproc then curPreprocId else 0 }
        atLineStart := false
        i := i + 1
    else if isIdentStartByte b then
      atLineStart := false
      let start := i
      i := i + 1
      while i < n && isIdentContByte bytes[i]! do
        i := i + 1
      let name := bytesSliceToAsciiString bytes start i
      tokens := tokens.push { kind := .ident name, line, inPreproc, preprocId := if inPreproc then curPreprocId else 0 }
    else if isDigitByte b then
      atLineStart := false
      let startLine := line
      i := i + 1
      while i < n && (isIdentContByte bytes[i]! || bytes[i]! == 46) do
        i := i + 1
      tokens := tokens.push { kind := .lit, line := startLine, inPreproc, preprocId := if inPreproc then curPreprocId else 0 }
    else if b == 45 && i + 1 < n && bytes[i + 1]! == 62 then
      atLineStart := false
      tokens := tokens.push { kind := .dotOrArrow, line, inPreproc, preprocId := if inPreproc then curPreprocId else 0 }
      i := i + 2
    else
      atLineStart := false
      let kind : CTokKind := match b with
        | 123 => .lbrace
        | 125 => .rbrace
        | 40 => .lparen
        | 41 => .rparen
        | 60 => .lt
        | 63 => .qmark
        | 59 => .semi
        | 61 => .eq
        | 46 => .dotOrArrow
        | _ => .other
      tokens := tokens.push { kind, line, inPreproc, preprocId := if inPreproc then curPreprocId else 0 }
      i := i + 1
  return tokens

private def hasTopLevelEq (hdr : Array CTok) : Bool := Id.run do
  let mut pdepth : Nat := 0
  for tok in hdr do
    match tok.kind with
    | .lparen => pdepth := pdepth + 1
    | .rparen => if pdepth > 0 then pdepth := pdepth - 1
    | .eq => if pdepth == 0 then return true
    | _ => pure ()
  return false

private def findMatchingLParenRev (hdr : Array CTok) (rpIdx : Nat) : Option Nat := Id.run do
  let mut depth : Nat := 0
  let mut k := rpIdx + 1
  while k > 0 do
    k := k - 1
    match hdr[k]!.kind with
    | .rparen => depth := depth + 1
    | .lparen =>
      if depth <= 1 then
        return some k
      depth := depth - 1
    | _ => pure ()
  return none

private def stripTrailingAttributes (hdr : Array CTok) : Array CTok := Id.run do
  let mut cur := hdr
  while cur.size >= 2 do
    if cur[cur.size - 1]!.kind != .rparen then
      break
    let some lp := findMatchingLParenRev cur (cur.size - 1) | break
    if lp > 0 then
      if let .ident attrKw := cur[lp - 1]!.kind then
        if attrKw == "__attribute__" || attrKw == "__attribute" then
          cur := cur.extract 0 (lp - 1)
          continue
    break
  return cur

private def isNonFuncIdent (name : String) : Bool :=
  name == "if" || name == "else" || name == "while" || name == "for" || name == "do" ||
  name == "switch" || name == "case" || name == "default" || name == "return" ||
  name == "goto" || name == "break" || name == "continue" || name == "sizeof" ||
  name == "_Alignof" || name == "alignof" || name == "typeof" || name == "__typeof__" ||
  name == "__attribute__" || name == "__attribute" || name == "_Static_assert" ||
  name == "struct" || name == "union" || name == "enum" || name == "typedef" ||
  name == "void" || name == "char" || name == "short" || name == "int" || name == "long" ||
  name == "float" || name == "double" || name == "signed" || name == "unsigned" ||
  name == "_Bool" || name == "bool" || name == "const" || name == "volatile" ||
  name == "restrict" || name == "__restrict" || name == "__restrict__" ||
  name == "static" || name == "inline" || name == "__inline" || name == "__inline__" ||
  name == "extern" || name == "auto" || name == "register" || name == "_Noreturn" ||
  name == "_Thread_local"

private def isPtrOrQualTok (tok : CTok) : Bool :=
  match tok.kind with
  | .other => true
  | .ident q => q == "const" || q == "volatile" || q == "restrict" || q == "__restrict" || q == "__restrict__"
  | _ => false

private partial def extractInsideDeclarator (tokens : Array CTok) : Option String := do
  let cur := stripTrailingAttributes tokens
  if cur.isEmpty then
    none
  match cur[cur.size - 1]!.kind with
  | .ident name =>
    if isNonFuncIdent name then none else some name
  | .rparen =>
    let lp ← findMatchingLParenRev cur (cur.size - 1)
    let prefixToks := cur.extract 0 lp
    if prefixToks.all isPtrOrQualTok then
      extractInsideDeclarator (cur.extract (lp + 1) (cur.size - 1))
    else
      extractInsideDeclarator prefixToks
  | _ => none

private def extractHeaderFuncName (hdr : Array CTok) : Option String := do
  if hasTopLevelEq hdr then
    none
  let trimmed := stripTrailingAttributes hdr
  if trimmed.isEmpty then
    none
  if trimmed[trimmed.size - 1]!.kind != .rparen then
    none
  let lp ← findMatchingLParenRev trimmed (trimmed.size - 1)
  if lp == 0 then
    none
  let beforeParams := stripTrailingAttributes (trimmed.extract 0 lp)
  if beforeParams.isEmpty then
    none
  match beforeParams[beforeParams.size - 1]!.kind with
  | .ident name =>
    if isNonFuncIdent name then none else some name
  | .rparen =>
    let innerLp ← findMatchingLParenRev beforeParams (beforeParams.size - 1)
    let isTypeof := innerLp > 0 && match beforeParams[innerLp - 1]!.kind with
      | .ident kw => kw == "typeof" || kw == "__typeof__"
      | _ => false
    if isTypeof then
      none
    else
      extractInsideDeclarator (beforeParams.extract (innerLp + 1) (beforeParams.size - 1))
  | _ => none

private def isAggregateTypeDefHdr (hdr : Array CTok) : Bool := Id.run do
  if hasTopLevelEq hdr then
    return false
  let mut hasAggKw := false
  let mut i := 0
  while i < hdr.size do
    match hdr[i]!.kind with
    | .ident kw =>
      if kw == "__attribute__" || kw == "__attribute" then
        if i + 1 < hdr.size && hdr[i + 1]!.kind == .lparen then
          let mut depth := 1
          let mut j := i + 2
          while j < hdr.size && depth > 0 do
            if hdr[j]!.kind == .lparen then depth := depth + 1
            else if hdr[j]!.kind == .rparen then depth := depth - 1
            j := j + 1
          i := j
          continue
      if kw == "struct" || kw == "union" || kw == "enum" then
        hasAggKw := true
    | .lparen => return false
    | _ => pure ()
    i := i + 1
  return hasAggKw

private def isExternCBlockHeader (hdr : Array CTok) : Bool :=
  hdr.size == 2 && hdr[0]!.kind == .ident "extern" && hdr[1]!.kind == .strLit "C"

private partial def collectCFunctionsAndTopLevel
    (path : String)
    (codeTokens : Array CTok) : Except String (Array CFunc × Array CTok × Array CTok) := do
  let mut funcs : Array CFunc := #[]
  let mut topLevel : Array CTok := #[]
  let mut aggFields : Array CTok := #[]
  let mut idx := 0
  let mut stmtStart := 0
  while idx < codeTokens.size do
    let tok := codeTokens[idx]!
    match tok.kind with
    | .semi =>
      topLevel := topLevel.push tok
      stmtStart := idx + 1
      idx := idx + 1
    | .rbrace =>
      return ← .error s!"UNBALANCED_C_BRACES: unexpected closing brace at {path}:{tok.line}"
    | .lbrace =>
      let mut depth := 1
      let mut closeIdx := idx + 1
      while closeIdx < codeTokens.size && depth > 0 do
        match codeTokens[closeIdx]!.kind with
        | .lbrace => depth := depth + 1
        | .rbrace => depth := depth - 1
        | _ => pure ()
        if depth > 0 then
          closeIdx := closeIdx + 1
      if depth != 0 then
        return ← .error s!"UNBALANCED_C_BRACES: unclosed opening brace at {path}:{tok.line}"
      let hdr := codeTokens.extract stmtStart idx
      let inner := codeTokens.extract (idx + 1) closeIdx
      if isExternCBlockHeader hdr then
        let (innerFuncs, innerTop, innerAgg) ← collectCFunctionsAndTopLevel path inner
        funcs := funcs ++ innerFuncs
        topLevel := topLevel ++ innerTop
        aggFields := aggFields ++ innerAgg
      else if let some fnName := extractHeaderFuncName hdr then
        funcs := funcs.push { name := fnName, body := inner }
      else if isAggregateTypeDefHdr hdr then
        aggFields := aggFields ++ inner
      else if hasTopLevelEq hdr then
        topLevel := topLevel ++ inner
      else
        return ← .error s!"UNRECOGNIZED_C_TOPLEVEL_BLOCK: {path}:{tok.line} unrecognized top-level brace block"
      idx := closeIdx + 1
      stmtStart := closeIdx + 1
    | _ =>
      topLevel := topLevel.push tok
      idx := idx + 1
  return (funcs, topLevel, aggFields)

private def isBannedThickToken
    (tokens : Array CTok)
    (i : Nat)
    (allowPoll : Bool := false)
    (allowMuxNames : Bool := false) : Option String :=
  let tok := tokens[i]!
  let isMemberAccess := i > 0 && tokens[i - 1]!.kind == .dotOrArrow
  match tok.kind with
  | .digraph => some "C digraph"
  | .tokenPaste => some "##"
  | .ident name =>
    if name == "strtok" || name == "strtok_r" || name == "strstr" || name == "strcasestr" ||
        name == "BPF_JUMP" || name == "BPF_STMT" || name.startsWith "epoll_" then
      some name
    else if !allowMuxNames && !isMemberAccess && (name == "select" || name == "pselect" || name == "thrd_create") then
      some name
    else if !allowMuxNames && !isMemberAccess && !allowPoll && (name == "poll" || name == "ppoll") then
      some name
    else
      none
  | _ => none

private def countDistinctLines (tokens : Array CTok) : Nat := Id.run do
  let mut seen : Std.HashSet Nat := {}
  for tok in tokens do
    seen := seen.insert tok.line
  return seen.size

private def checkFunction
    (relPath : String)
    (fn : CFunc)
    (budget : ForeignBudget) : Array String := Id.run do
  let mut errs : Array String := #[]
  let fnKey := s!"{relPath}::{fn.name}"
  let ov := budget.overrides.getD fnKey {}
  let codeLines := countDistinctLines fn.body
  if codeLines > ov.maxCodeLines then
    errs := errs.push s!"C_FUNC_TOO_LONG: {fnKey} has {codeLines} non-blank code lines (max {ov.maxCodeLines})"

  let mut branches := 0
  let mut forCount := 0
  let mut whileCount := 0
  let mut doCount := 0
  for i in [0 : fn.body.size] do
    let tok := fn.body[i]!
    match tok.kind with
    | .qmark => branches := branches + 1
    | .ident name =>
      if name == "if" || name == "switch" then
        branches := branches + 1
      else if name == "for" then
        forCount := forCount + 1
      else if name == "while" then
        whileCount := whileCount + 1
      else if name == "do" then
        doCount := doCount + 1
      else if name == "goto" then
        errs := errs.push s!"C_LOOP_FORBIDDEN: {fnKey}:{tok.line} uses forbidden 'goto'"
      else if name == "pthread_create" && !budget.threadHelpers.contains fnKey then
        errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {fnKey}:{tok.line} uses pthread_create outside named_thread_helpers"
    | _ => pure ()
    if let some bad := isBannedThickToken fn.body i ov.allowPoll then
      errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {fnKey}:{tok.line} uses forbidden '{bad}'"

  if branches > ov.maxBranches then
    errs := errs.push s!"C_FUNC_TOO_BRANCHY: {fnKey} has {branches} branches (max {ov.maxBranches})"

  let totalLoops := forCount + whileCount + doCount
  let loopsOk := match ov.maxLoops? with
    | some maxL => totalLoops <= maxL
    | none =>
      if ov.allowArrayCopyLoop then
        forCount <= 1 && whileCount == 0 && doCount == 0
      else
        totalLoops == 0
  if !loopsOk then
    errs := errs.push s!"C_LOOP_FORBIDDEN: {fnKey} contains loop(s) (for={forCount}, while={whileCount}, do={doCount})"
  return errs

private def normalizeIncludePath (fromFile : String) (target : String) : Option String := Id.run do
  if target.startsWith "/" then
    return none
  let mut parts := (fromFile.splitOn "/").dropLast
  for seg in target.splitOn "/" do
    if seg == "" || seg == "." then
      continue
    else if seg == ".." then
      if parts.isEmpty then
        return none
      parts := parts.dropLast
    else
      parts := parts ++ [seg]
  return some (String.intercalate "/" parts)

private def checkPreprocTokens
    (relPath : String)
    (allTokens : Array CTok)
    (budget : ForeignBudget) : Array String := Id.run do
  let allowPollInFile := budget.overrides.fold (init := false) fun acc key ov =>
    acc || (ov.allowPoll && key.startsWith s!"{relPath}::")
  let mut errs : Array String := #[]
  let mut curPreprocIsInclude : Bool := false
  let mut i := 0
  while i < allTokens.size do
    let tok := allTokens[i]!
    if tok.inPreproc then
      let isDirectiveStart := i == 0 || allTokens[i - 1]!.preprocId != tok.preprocId
      if isDirectiveStart then
        curPreprocIsInclude :=
          tok.kind == .hash && i + 1 < allTokens.size &&
            allTokens[i + 1]!.preprocId == tok.preprocId &&
            allTokens[i + 1]!.kind == .ident "include"
      if let .ident name := tok.kind then
        if name == "for" || name == "while" || name == "do" || name == "goto" then
          errs := errs.push s!"C_LOOP_FORBIDDEN: {relPath}:{tok.line} uses '{name}' in preprocessor directive"
        else if name == "pthread_create" then
          errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{tok.line} uses pthread_create in preprocessor directive"
      if let some bad := isBannedThickToken allTokens i (allowPollInFile && curPreprocIsInclude) then
        errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{tok.line} uses forbidden '{bad}' in preprocessor directive"
      if isDirectiveStart && tok.kind == .hash && i + 1 < allTokens.size && allTokens[i + 1]!.preprocId == tok.preprocId then
        match allTokens[i + 1]!.kind with
        | .ident "include" =>
          if i + 2 >= allTokens.size || allTokens[i + 2]!.preprocId != tok.preprocId then
            errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{tok.line} invalid #include directive"
          else
            match allTokens[i + 2]!.kind with
            | .lt => pure ()
            | .strLit incTarget =>
              if !incTarget.endsWith ".h" then
                errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{tok.line} quoted #include '{incTarget}' must end in .h"
              else
                match normalizeIncludePath relPath incTarget with
                | none =>
                  errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{tok.line} #include '{incTarget}' escapes repository root"
                | some resolved =>
                  if let some fb := budget.files.get? resolved then
                    if fb.legacyUnmigrated then
                      errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{tok.line} cannot #include legacy_unmigrated '{resolved}'"
            | _ =>
              errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{tok.line} #include target must be <...> or \"*.h\""
        | .ident "define" =>
          let defineLine := tok.line
          let mut j := i + 2
          let mut lines : Std.HashSet Nat := ({} : Std.HashSet Nat).insert defineLine
          while j < allTokens.size && allTokens[j]!.inPreproc && allTokens[j]!.preprocId == tok.preprocId do
            let dt := allTokens[j]!
            lines := lines.insert dt.line
            match dt.kind with
            | .lbrace | .rbrace =>
              errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{defineLine} #define contains brace"
            | .semi =>
              errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{defineLine} #define contains semicolon"
            | .qmark =>
              errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{defineLine} #define contains '?'"
            | .ident kw =>
              if kw == "if" || kw == "switch" then
                errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{defineLine} #define contains '{kw}'"
            | _ => pure ()
            j := j + 1
          if lines.size > 15 then
            errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{defineLine} #define spans {lines.size} lines (max 15)"
        | _ => pure ()
    i := i + 1
  return errs

private def collectIntraFileCallees (defined : Std.HashSet String) (body : Array CTok) : Array String := Id.run do
  let mut callees : Array String := #[]
  let mut seen : Std.HashSet String := {}
  for i in [0 : body.size] do
    if let .ident callee := body[i]!.kind then
      if defined.contains callee && !seen.contains callee then
        let mut prev := i
        while prev > 0 && body[prev - 1]!.kind == .lparen do
          prev := prev - 1
        let isMemberAccess := prev > 0 && body[prev - 1]!.kind == .dotOrArrow
        if !isMemberAccess then
          let mut next := i + 1
          while next < body.size && body[next]!.kind == .rparen do
            next := next + 1
          let isCallSite := next < body.size && body[next]!.kind == .lparen
          let isPtrAssign := i > 0 && (body[i - 1]!.kind == .eq || body[i - 1]!.kind == .ident "return")
          if isCallSite || isPtrAssign then
            seen := seen.insert callee
            callees := callees.push callee
  return callees

private def findCallCycleErrors (relPath : String) (funcs : Array CFunc) : Array String := Id.run do
  let mut defined : Std.HashSet String := {}
  for fn in funcs do
    defined := defined.insert fn.name
  let mut adj : Std.HashMap String (Array String) := {}
  for fn in funcs do
    let existing := adj.getD fn.name #[]
    let nexts := collectIntraFileCallees defined fn.body
    adj := adj.insert fn.name (existing ++ nexts)
  let mut errs : Array String := #[]
  let mut reported : Std.HashSet String := {}
  for fn in funcs do
    if reported.contains fn.name then
      continue
    let mut visited : Std.HashSet String := {}
    let mut stack := adj.getD fn.name #[]
    let mut hasCycle := false
    while !stack.isEmpty do
      let cur := stack[stack.size - 1]!
      stack := stack.pop
      if cur == fn.name then
        hasCycle := true
        break
      if !visited.contains cur then
        visited := visited.insert cur
        for nxt in adj.getD cur #[] do
          stack := stack.push nxt
    if hasCycle then
      reported := reported.insert fn.name
      errs := errs.push s!"C_LOOP_FORBIDDEN: {relPath}::{fn.name} participates in recursive call cycle"
  return errs

private def checkNonFuncTokens
    (relPath : String)
    (tokens : Array CTok)
    (allowMuxNames : Bool) : Array String := Id.run do
  let mut errs : Array String := #[]
  for i in [0 : tokens.size] do
    let tok := tokens[i]!
    if let some bad := isBannedThickToken tokens i false allowMuxNames then
      errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{tok.line} uses forbidden '{bad}' at top level"
    match tok.kind with
    | .qmark =>
      errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{tok.line} uses '?' at top level"
    | .ident name =>
      if name == "for" || name == "while" || name == "do" || name == "goto" then
        errs := errs.push s!"C_LOOP_FORBIDDEN: {relPath}:{tok.line} uses '{name}' at top level"
      else if name == "if" || name == "switch" then
        errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{tok.line} uses '{name}' at top level"
      else if name == "pthread_create" then
        errs := errs.push s!"C_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{tok.line} uses pthread_create at top level"
    | _ => pure ()
  return errs

private def checkNonLegacyCFile
    (relPath : String)
    (bytes : ByteArray)
    (budget : ForeignBudget) : Array String × Nat := Id.run do
  let allTokens := lexCBytes bytes
  let mut errs := checkPreprocTokens relPath allTokens budget

  let codeTokens := allTokens.filter (!·.inPreproc)
  match collectCFunctionsAndTopLevel relPath codeTokens with
  | .error e =>
    errs := errs.push e
    return (errs, 0)
  | .ok (funcs, topLevel, aggFields) =>
    errs := errs ++ checkNonFuncTokens relPath topLevel false
    errs := errs ++ checkNonFuncTokens relPath aggFields true
    errs := errs ++ findCallCycleErrors relPath funcs
    for fn in funcs do
      errs := errs ++ checkFunction relPath fn budget
    return (errs, funcs.size)

private def parseJsonNatField (obj : Json) (field : String) : Except String Nat := do
  match obj.getObjVal? field with
  | .error _ => .error s!"missing integer field '{field}'"
  | .ok (.num jn) =>
    if jn.exponent != 0 || jn.mantissa < 0 then
      .error s!"field '{field}' must be a non-negative integer"
    else
      .ok jn.mantissa.toNat
  | .ok _ => .error s!"field '{field}' must be a non-negative integer"

private def parseJsonBoolField (obj : Json) (field : String) : Except String Bool := do
  match obj.getObjVal? field with
  | .error _ => .error s!"missing boolean field '{field}'"
  | .ok (.bool b) => .ok b
  | .ok _ => .error s!"field '{field}' must be a boolean"

private def ensureAllowedKeys (ctx : String) (obj : Json) (allowed : Array String) : Except String Unit := do
  let .obj map := obj | .error s!"BUDGET_SCHEMA_ERROR: {ctx} must be an object"
  for (k, _) in map do
    if !allowed.contains k then
      .error s!"BUDGET_SCHEMA_ERROR: {ctx} has unknown key '{k}'"

private def parseBudget (raw : String) : Except String ForeignBudget := do
  let json ← Json.parse raw |>.mapError (fun e => s!"BUDGET_SCHEMA_ERROR: invalid JSON ({e})")
  let .obj _ := json | .error "BUDGET_SCHEMA_ERROR: root must be a JSON object"
  ensureAllowedKeys "root" json #["version", "files", "vendored_files", "function_overrides", "named_thread_helpers"]
  let v ← parseJsonNatField json "version" |>.mapError (fun e => s!"BUDGET_SCHEMA_ERROR: {e}")
  if v != 1 then
    .error s!"BUDGET_SCHEMA_ERROR: unsupported version {v}"

  let filesJson ← json.getObjVal? "files" |>.mapError (fun _ => "BUDGET_SCHEMA_ERROR: missing 'files' object")
  let .obj filesObj := filesJson | .error "BUDGET_SCHEMA_ERROR: 'files' must be an object"
  let mut files : Std.HashMap String FileBudget := {}
  for (path, entry) in filesObj do
    ensureAllowedKeys s!"files[{path}]" entry #["max_lines", "legacy_unmigrated"]
    let maxLines ← parseJsonNatField entry "max_lines" |>.mapError (fun e => s!"BUDGET_SCHEMA_ERROR: files[{path}] {e}")
    let legacy ← parseJsonBoolField entry "legacy_unmigrated" |>.mapError (fun e => s!"BUDGET_SCHEMA_ERROR: files[{path}] {e}")
    files := files.insert path { maxLines, legacyUnmigrated := legacy }

  let vendoredJson ← json.getObjVal? "vendored_files" |>.mapError (fun _ => "BUDGET_SCHEMA_ERROR: missing 'vendored_files' object")
  let .obj vendoredObj := vendoredJson | .error "BUDGET_SCHEMA_ERROR: 'vendored_files' must be an object"
  let mut vendored : Std.HashMap String VendoredBudget := {}
  for (path, entry) in vendoredObj do
    ensureAllowedKeys s!"vendored_files[{path}]" entry #["sha256", "max_lines"]
    if files.contains path then
      .error s!"BUDGET_SCHEMA_ERROR: '{path}' cannot appear in both 'files' and 'vendored_files'"
    let sha ← entry.getObjValAs? String "sha256" |>.mapError (fun _ => s!"BUDGET_SCHEMA_ERROR: vendored_files[{path}] missing string 'sha256'")
    let maxLines? ← match entry.getObjVal? "max_lines" with
      | .error _ => pure none
      | .ok _ => some <$> parseJsonNatField entry "max_lines" |>.mapError (fun e => s!"BUDGET_SCHEMA_ERROR: vendored_files[{path}] {e}")
    vendored := vendored.insert path { sha256 := sha, maxLines? }

  let overridesJson := (json.getObjVal? "function_overrides").toOption.getD (.obj {})
  let .obj overridesObj := overridesJson | .error "BUDGET_SCHEMA_ERROR: 'function_overrides' must be an object"
  let mut overrides : Std.HashMap String FuncOverride := {}
  for (fnKey, entry) in overridesObj do
    ensureAllowedKeys s!"function_overrides[{fnKey}]" entry #["max_code_lines", "max_branches", "allow_array_copy_loop", "max_loops", "allow_poll"]
    let maxCodeLines ← match entry.getObjVal? "max_code_lines" with
      | .error _ => pure 35
      | .ok _ => parseJsonNatField entry "max_code_lines" |>.mapError (fun e => s!"BUDGET_SCHEMA_ERROR: function_overrides[{fnKey}] {e}")
    let maxBranches ← match entry.getObjVal? "max_branches" with
      | .error _ => pure 8
      | .ok _ => parseJsonNatField entry "max_branches" |>.mapError (fun e => s!"BUDGET_SCHEMA_ERROR: function_overrides[{fnKey}] {e}")
    let allowCopy ← match entry.getObjVal? "allow_array_copy_loop" with
      | .error _ => pure false
      | .ok _ => parseJsonBoolField entry "allow_array_copy_loop" |>.mapError (fun e => s!"BUDGET_SCHEMA_ERROR: function_overrides[{fnKey}] {e}")
    let maxLoops? ← match entry.getObjVal? "max_loops" with
      | .error _ => pure none
      | .ok _ => some <$> parseJsonNatField entry "max_loops" |>.mapError (fun e => s!"BUDGET_SCHEMA_ERROR: function_overrides[{fnKey}] {e}")
    let allowPoll ← match entry.getObjVal? "allow_poll" with
      | .error _ => pure false
      | .ok _ => parseJsonBoolField entry "allow_poll" |>.mapError (fun e => s!"BUDGET_SCHEMA_ERROR: function_overrides[{fnKey}] {e}")
    overrides := overrides.insert fnKey {
      maxCodeLines
      maxBranches
      allowArrayCopyLoop := allowCopy
      maxLoops?
      allowPoll
    }

  let helpersJson := (json.getObjVal? "named_thread_helpers").toOption.getD (.arr #[])
  let .arr helpersArr := helpersJson | .error "BUDGET_SCHEMA_ERROR: 'named_thread_helpers' must be an array"
  let mut threadHelpers : Std.HashSet String := {}
  for item in helpersArr do
    let .str s := item | .error "BUDGET_SCHEMA_ERROR: 'named_thread_helpers' items must be strings"
    threadHelpers := threadHelpers.insert s

  return { files, vendored, overrides, threadHelpers }

private def gitLsFiles (repoDir : System.FilePath) : IO (Except String (Array String)) := do
  let out ← IO.Process.output {
    cmd := "git"
    args := #["-C", repoDir.toString, "ls-files", "-z"]
  }
  if out.exitCode != 0 then
    return .error s!"GIT_LS_FILES_FAILED: {out.stderr.trimAscii.toString}"
  let parts := out.stdout.splitOn "\x00"
  return .ok (parts.filter (!·.isEmpty)).toArray

private def computeSha256 (filePath : System.FilePath) : IO (Except String String) := do
  let out ← IO.Process.output {
    cmd := "sha256sum"
    args := #[filePath.toString]
  }
  if out.exitCode != 0 then
    return .error s!"SHA256_FAILED: {filePath}: {out.stderr.trimAscii.toString}"
  let hex := (out.stdout.splitOn " ").headD ""
  if hex.length != 64 then
    return .error s!"SHA256_PARSE_FAILED: {filePath}: unexpected output '{out.stdout.trimAscii.toString}'"
  return .ok hex

private def isCOrHeader (relPath : String) : Bool :=
  relPath.endsWith ".c" || relPath.endsWith ".h" ||
  relPath.endsWith ".inc" || relPath.endsWith ".inl" ||
  relPath.endsWith ".cc" || relPath.endsWith ".cpp" ||
  relPath.endsWith ".cxx" || relPath.endsWith ".hpp"

private def isAeneasExtractedRustPath (relPath : String) : Bool :=
  relPath == "LeanSwe/PostFork/rust/src/child.rs" ||
  relPath == "LeanSwe/PostFork/rust/src/fd_ops.rs"

private inductive RTokKind where
  | ident (name : String)
  | lbrace
  | rbrace
  | lparen
  | rparen
  | lbrack
  | rbrack
  | lt
  | gt
  | arrow
  | fatArrow
  | comma
  | hash
  | bang
  | colon2
  | semi
  | qmark
  | amp2
  | pipe2
  | lit
  | other
  deriving BEq, Inhabited

private structure RTok where
  kind : RTokKind
  line : Nat
  deriving Inhabited

private structure RFunc where
  name : String
  body : Array RTok
  deriving Inhabited

private def countRawHashes (bytes : ByteArray) (start : Nat) : Option Nat := Id.run do
  let n := bytes.size
  let mut k := 0
  let mut j := start
  while j < n && bytes[j]! == 35 do
    k := k + 1
    j := j + 1
  if j < n && bytes[j]! == 34 then
    return some k
  return none

private def hasClosingRawHashes (bytes : ByteArray) (pos k : Nat) : Bool := Id.run do
  if pos + k > bytes.size then
    return false
  for off in [0 : k] do
    if bytes[pos + off]! != 35 then
      return false
  return true

private def lexRustBytes (bytes : ByteArray) : Array RTok := Id.run do
  let n := bytes.size
  let mut i := 0
  let mut line := 1
  let mut out : Array RTok := #[]
  while i < n do
    let b := bytes[i]!
    if b == 10 then
      line := line + 1
      i := i + 1
    else if isSpaceByte b then
      i := i + 1
    else if b == 47 && i + 1 < n && bytes[i + 1]! == 47 then
      i := i + 2
      while i < n && bytes[i]! != 10 do
        i := i + 1
    else if b == 47 && i + 1 < n && bytes[i + 1]! == 42 then
      i := i + 2
      let mut depth := 1
      while i < n && depth > 0 do
        if bytes[i]! == 47 && i + 1 < n && bytes[i + 1]! == 42 then
          depth := depth + 1
          i := i + 2
        else if bytes[i]! == 42 && i + 1 < n && bytes[i + 1]! == 47 then
          depth := depth - 1
          i := i + 2
        else
          if bytes[i]! == 10 then line := line + 1
          i := i + 1
    else if (b == 114 || ((b == 98 || b == 99) && i + 1 < n && bytes[i + 1]! == 114)) &&
        (countRawHashes bytes (if b == 114 then i + 1 else i + 2)).isSome then
      let startLine := line
      let hStart := if b == 114 then i + 1 else i + 2
      let k := (countRawHashes bytes hStart).getD 0
      i := hStart + k + 1
      while i < n do
        if bytes[i]! == 10 then
          line := line + 1
          i := i + 1
        else if bytes[i]! == 34 && hasClosingRawHashes bytes (i + 1) k then
          i := i + 1 + k
          break
        else
          i := i + 1
      out := out.push { kind := .lit, line := startLine }
    else if b == 34 || ((b == 98 || b == 99) && i + 1 < n && bytes[i + 1]! == 34) then
      let startLine := line
      i := if b == 34 then i + 1 else i + 2
      while i < n do
        let c := bytes[i]!
        if c == 92 then
          if i + 1 < n && bytes[i + 1]! == 10 then line := line + 1
          i := min n (i + 2)
        else if c == 34 then
          i := i + 1
          break
        else
          if c == 10 then line := line + 1
          i := i + 1
      out := out.push { kind := .lit, line := startLine }
    else if b == 39 || (b == 98 && i + 1 < n && bytes[i + 1]! == 39) then
      let qIdx := if b == 39 then i else i + 1
      if qIdx + 2 < n && bytes[qIdx + 1]! != 92 && bytes[qIdx + 1]! != 39 && bytes[qIdx + 1]! != 10 &&
          bytes[qIdx + 2]! == 39 then
        out := out.push { kind := .lit, line }
        i := qIdx + 3
      else if qIdx + 1 < n && bytes[qIdx + 1]! == 92 then
        let startLine := line
        i := qIdx + 1
        while i < n && bytes[i]! != 10 do
          if bytes[i]! == 92 then
            i := min n (i + 2)
          else if bytes[i]! == 39 then
            i := i + 1
            break
          else
            i := i + 1
        out := out.push { kind := .lit, line := startLine }
      else if b == 39 && qIdx + 1 < n && bytes[qIdx + 1]! >= 128 then
        let mut u := qIdx + 2
        while u < n && bytes[u]! >= 128 && bytes[u]! < 192 do
          u := u + 1
        if u < n && bytes[u]! == 39 then
          out := out.push { kind := .lit, line }
          i := u + 1
        else
          i := i + 1
      else
        i := i + 1
    else if b == 114 && i + 1 < n && bytes[i + 1]! == 35 && i + 2 < n && isIdentStartByte bytes[i + 2]! then
      let start := i + 2
      i := i + 3
      while i < n && isIdentContByte bytes[i]! do
        i := i + 1
      out := out.push { kind := .ident (bytesSliceToAsciiString bytes start i), line }
    else if isIdentStartByte b then
      let start := i
      i := i + 1
      while i < n && isIdentContByte bytes[i]! do
        i := i + 1
      out := out.push { kind := .ident (bytesSliceToAsciiString bytes start i), line }
    else if isDigitByte b then
      i := i + 1
      while i < n && (isIdentContByte bytes[i]! || bytes[i]! == 46) do
        i := i + 1
      out := out.push { kind := .lit, line }
    else if b == 58 && i + 1 < n && bytes[i + 1]! == 58 then
      out := out.push { kind := .colon2, line }
      i := i + 2
    else if b == 38 && i + 1 < n && bytes[i + 1]! == 38 then
      out := out.push { kind := .amp2, line }
      i := i + 2
    else if b == 124 && i + 1 < n && bytes[i + 1]! == 124 then
      out := out.push { kind := .pipe2, line }
      i := i + 2
    else if b == 45 && i + 1 < n && bytes[i + 1]! == 62 then
      out := out.push { kind := .arrow, line }
      i := i + 2
    else if b == 61 && i + 1 < n && bytes[i + 1]! == 62 then
      out := out.push { kind := .fatArrow, line }
      i := i + 2
    else
      let kind : RTokKind := match b with
        | 123 => .lbrace
        | 125 => .rbrace
        | 40 => .lparen
        | 41 => .rparen
        | 91 => .lbrack
        | 93 => .rbrack
        | 60 => .lt
        | 62 => .gt
        | 44 => .comma
        | 35 => .hash
        | 33 => .bang
        | 59 => .semi
        | 63 => .qmark
        | _ => .other
      out := out.push { kind, line }
      i := i + 1
  return out

private def isAllowedSysSyscallNr (s : String) : Bool :=
  s == "SYS_rt_sigaction" || s == "SYS_rt_sigprocmask" ||
  s == "SYS_close_range" || s == "SYS_getdents64"

private def isAllowedSysLibcItem (s : String) : Bool :=
  isAllowedSysSyscallNr s ||
  s == "__errno_location" || s == "_exit" || s == "chdir" || s == "close" ||
  s == "dup2" || s == "execve" || s == "fcntl" || s == "open" ||
  s == "read" || s == "setpgid" || s == "syscall" || s == "write" ||
  s == "EINVAL" || s == "SIG_DFL" || s == "SIG_IGN" || s == "SIG_UNBLOCK" ||
  s == "F_GETFD" || s == "F_SETFD" || s == "F_DUPFD_CLOEXEC" ||
  s == "O_RDONLY" || s == "O_DIRECTORY" || s == "O_CLOEXEC" ||
  s == "c_int" || s == "c_long" || s == "c_ulong" || s == "c_void"

private def isAllowedPostForkNoMangleFn (s : String) : Bool :=
  s == "leanswe_postfork_run_child" || s == "leanswe_postfork_close_fds_above2_except"

private def isExternalRustQual (relPath : String) (s : String) : Bool :=
  s == "libc" || s == "core" || s == "child" || s == "fd_ops" ||
  (s == "sys" && relPath != "LeanSwe/PostFork/rust/src/sys.rs")

private def collectRustIntraFileCallees
    (relPath : String)
    (defined : Std.HashSet String)
    (body : Array RTok) : Array String := Id.run do
  let mut callees : Array String := #[]
  let mut seen : Std.HashSet String := {}
  for i in [0 : body.size] do
    if let .ident callee := body[i]!.kind then
      if defined.contains callee && !seen.contains callee then
        let extQual :=
          i >= 2 && body[i - 1]!.kind == .colon2 &&
          match body[i - 2]!.kind with
          | .ident q => isExternalRustQual relPath q
          | _ => false
        if !extQual then
          seen := seen.insert callee
          callees := callees.push callee
  return callees

private def findRustCallCycleErrors (relPath : String) (funcs : Array RFunc) : Array String := Id.run do
  let mut defined : Std.HashSet String := {}
  for fn in funcs do
    defined := defined.insert fn.name
  let mut adj : Std.HashMap String (Array String) := {}
  for fn in funcs do
    let existing := adj.getD fn.name #[]
    adj := adj.insert fn.name (existing ++ collectRustIntraFileCallees relPath defined fn.body)
  let mut errs : Array String := #[]
  let mut reported : Std.HashSet String := {}
  for fn in funcs do
    if reported.contains fn.name then
      continue
    let mut visited : Std.HashSet String := {}
    let mut stack := adj.getD fn.name #[]
    let mut hasCycle := false
    while !stack.isEmpty do
      let cur := stack.back!
      stack := stack.pop
      if cur == fn.name then
        hasCycle := true
        break
      if !visited.contains cur then
        visited := visited.insert cur
        for nxt in adj.getD cur #[] do
          stack := stack.push nxt
    if hasCycle then
      reported := reported.insert fn.name
      errs := errs.push s!"RUST_LOOP_FORBIDDEN: {relPath}::{fn.name} participates in recursive call cycle"
  return errs

private def checkAeneasRustFile (relPath : String) (bytes : ByteArray) : Array String := Id.run do
  let toks := lexRustBytes bytes
  let mut errs : Array String := #[]
  let hasForbidUnsafe :=
    toks.size >= 8 &&
    toks[0]!.kind == .hash &&
    toks[1]!.kind == .bang &&
    toks[2]!.kind == .lbrack &&
    toks[3]!.kind == .ident "forbid" &&
    toks[4]!.kind == .lparen &&
    toks[5]!.kind == .ident "unsafe_code" &&
    toks[6]!.kind == .rparen &&
    toks[7]!.kind == .rbrack
  if !hasForbidUnsafe then
    errs := errs.push s!"RUST_AENEAS_UNSAFE_FORBIDDEN: {relPath} must start with #![forbid(unsafe_code)]"
  for tok in toks do
    if let .ident name := tok.kind then
      if name == "cfg" || name == "cfg_attr" || name == "charon" then
        errs := errs.push s!"RUST_AENEAS_CFG_FORBIDDEN: {relPath}:{tok.line} uses '{name}' (split-brain hazard)"
      else if name == "unsafe" || name == "extern" || name == "libc" || name == "std" ||
          name == "syscall" || name == "asm" || name == "global_asm" || name == "naked_asm" ||
          name == "no_mangle" || name == "export_name" || name == "link_section" ||
          name == "link_name" || name == "linkage" || name == "no_link" || name == "extern_weak" ||
          name == "macro_rules" || name == "include" || name == "include_bytes" || name == "include_str" then
        errs := errs.push s!"RUST_AENEAS_THICK_FORBIDDEN: {relPath}:{tok.line} uses forbidden '{name}'"
  return errs

private partial def scanRustScope
    (relPath : String)
    (toks : Array RTok)
    (inFnBody : Bool) : Array RFunc × Array String := Id.run do
  let n := toks.size
  let mut funcs : Array RFunc := #[]
  let mut errs : Array String := #[]
  let mut i := 0
  while i < n do
    if toks[i]!.kind == .ident "fn" then
      if i + 1 < n && toks[i + 1]!.kind == .lparen then
        i := i + 1
        continue
      else if i + 1 < n then
        if let .ident fnName := toks[i + 1]!.kind then
          let mut j := i + 2
          let mut pdepth := 0
          let mut bdepth := 0
          let mut adepth := 0
          let mut cdepth := 0
          let mut hdrMalformed := false
          while j < n do
            match toks[j]!.kind with
            | .lparen => pdepth := pdepth + 1
            | .rparen =>
              if pdepth > 0 then
                pdepth := pdepth - 1
              else
                hdrMalformed := true
                break
            | .lbrack => bdepth := bdepth + 1
            | .rbrack =>
              if bdepth > 0 then
                bdepth := bdepth - 1
              else
                hdrMalformed := true
                break
            | .lt =>
              if pdepth == 0 && bdepth == 0 && cdepth == 0 then
                adepth := adepth + 1
            | .gt =>
              if pdepth == 0 && bdepth == 0 && cdepth == 0 then
                if adepth > 0 then
                  adepth := adepth - 1
                else
                  hdrMalformed := true
                  break
            | .semi =>
              if pdepth == 0 && bdepth == 0 && adepth == 0 && cdepth == 0 then
                break
            | .lbrace =>
              if pdepth == 0 && bdepth == 0 && adepth == 0 && cdepth == 0 then
                break
              else
                cdepth := cdepth + 1
            | .rbrace =>
              if cdepth > 0 then
                cdepth := cdepth - 1
              else
                hdrMalformed := true
                break
            | _ => pure ()
            j := j + 1
          if hdrMalformed || j >= n then
            errs := errs.push s!"RUST_MALFORMED_FN: {relPath}:{toks[i]!.line} malformed header in fn '{fnName}'"
            i := i + 2
            continue
          let (hdrFuncs, hdrErrs) := scanRustScope relPath (toks.extract (i + 2) j) false
          funcs := funcs ++ hdrFuncs
          errs := errs ++ hdrErrs
          if toks[j]!.kind == .semi then
            i := j + 1
            continue
          else if toks[j]!.kind == .lbrace then
            let bodyStart := j + 1
            let mut depth := 1
            j := bodyStart
            while j < n && depth > 0 do
              match toks[j]!.kind with
              | .lbrace => depth := depth + 1
              | .rbrace => depth := depth - 1
              | _ => pure ()
              j := j + 1
            if depth != 0 then
              errs := errs.push s!"RUST_MALFORMED_FN: {relPath}:{toks[i]!.line} unclosed body in fn '{fnName}'"
              i := n
              continue
            let bodyEnd := j - 1
            let bodyToks := toks.extract bodyStart bodyEnd
            funcs := funcs.push { name := fnName, body := bodyToks }
            let mut lineSet : Std.HashSet Nat := {}
            let mut branches := 0
            for t in bodyToks do
              lineSet := lineSet.insert t.line
              match t.kind with
              | .ident "if" | .ident "match" | .amp2 | .pipe2 | .qmark => branches := branches + 1
              | _ => pure ()
            if lineSet.size > 50 then
              errs := errs.push s!"RUST_FUNC_TOO_LONG: {relPath}::{fnName} has {lineSet.size} code lines (max 50)"
            if branches > 8 then
              errs := errs.push s!"RUST_FUNC_TOO_MANY_BRANCHES: {relPath}::{fnName} has {branches} branches (max 8)"
            let (innerFuncs, innerErrs) := scanRustScope relPath bodyToks true
            funcs := funcs ++ innerFuncs
            errs := errs ++ innerErrs
            i := j
            continue
          else
            errs := errs.push s!"RUST_MALFORMED_FN: {relPath}:{toks[i]!.line} unexpected token in fn '{fnName}'"
            i := i + 2
            continue
        else
          errs := errs.push s!"RUST_MALFORMED_FN: {relPath}:{toks[i]!.line} unexpected token after 'fn'"
          i := i + 1
          continue
      else
        errs := errs.push s!"RUST_MALFORMED_FN: {relPath}:{toks[i]!.line} trailing 'fn' at EOF"
        i := i + 1
        continue
    if !inFnBody then
      match toks[i]!.kind with
      | .ident "if" | .ident "match" | .amp2 | .pipe2 | .qmark =>
        errs := errs.push s!"RUST_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{toks[i]!.line} uses branch outside fn body"
      | _ => pure ()
    i := i + 1
  return (funcs, errs)

private def checkNonAeneasRustFile (relPath : String) (bytes : ByteArray) : Array String := Id.run do
  let toks := lexRustBytes bytes
  let n := toks.size
  let mut errs : Array String := #[]
  let mut inUseStmt := false
  for idx in [0 : n] do
    let tok := toks[idx]!
    if tok.kind == .ident "use" then
      inUseStmt := true
    else if tok.kind == .semi then
      inUseStmt := false
    if let .ident name := tok.kind then
      if name == "for" || name == "while" || name == "loop" then
        errs := errs.push s!"RUST_LOOP_FORBIDDEN: {relPath}:{tok.line} uses '{name}'"
      else if name == "macro_rules" then
        errs := errs.push s!"RUST_MACRO_FORBIDDEN: {relPath}:{tok.line} uses 'macro_rules'"
      else if name == "include" || name == "include_bytes" || name == "include_str" ||
          name == "asm" || name == "global_asm" || name == "naked_asm" ||
          name == "export_name" || name == "link_section" || name == "link_name" ||
          name == "linkage" || name == "no_link" || name == "extern_weak" ||
          name == "std" || name == "cfg_attr" || name == "charon" then
        errs := errs.push s!"RUST_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{tok.line} uses '{name}'"
      else if name == "mod" then
        let okLibMod :=
          relPath == "LeanSwe/PostFork/rust/src/lib.rs" &&
          idx + 2 < n &&
          (match toks[idx + 1]!.kind with | .ident _ => true | _ => false) &&
          toks[idx + 2]!.kind == .semi
        if !okLibMod then
          errs := errs.push s!"RUST_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{tok.line} uses inline or unauthorized 'mod'"
      else if relPath == "LeanSwe/PostFork/rust/src/sys.rs" &&
          (name == "child" || name == "fd_ops" ||
            (name == "ffi" && !(idx >= 2 && toks[idx - 2]!.kind == .ident "core" && toks[idx - 1]!.kind == .colon2))) then
        errs := errs.push s!"RUST_THICK_CONSTRUCT_FORBIDDEN: {relPath}:{tok.line} references upper module '{name}'"
      else if name == "cfg" then
        let allowedCfg :=
          (relPath == "LeanSwe/PostFork/rust/src/lib.rs" || relPath == "LeanSwe/PostFork/rust/src/sys.rs") &&
          idx + 5 < n &&
          toks[idx + 1]!.kind == .lparen &&
          toks[idx + 2]!.kind == .ident "feature" &&
          toks[idx + 3]!.kind == .other &&
          toks[idx + 4]!.kind == .lit &&
          toks[idx + 5]!.kind == .rparen
        if !allowedCfg then
          errs := errs.push s!"RUST_CFG_FORBIDDEN: {relPath}:{tok.line} uses unauthorized cfg predicate"
      else if name == "extern" then
        let okExternFn :=
          (idx + 1 < n && toks[idx + 1]!.kind == .ident "fn") ||
          (idx + 2 < n && toks[idx + 1]!.kind == .lit && toks[idx + 2]!.kind == .ident "fn")
        if !okExternFn then
          errs := errs.push s!"RUST_EXTERN_BLOCK_FORBIDDEN: {relPath}:{tok.line} uses foreign extern block or crate"
      else if name == "libc" then
        if relPath != "LeanSwe/PostFork/rust/src/sys.rs" then
          errs := errs.push s!"RUST_DIRECT_LIBC_FORBIDDEN: {relPath}:{tok.line} references 'libc' outside sys.rs"
        else if inUseStmt || idx + 2 >= n || toks[idx + 1]!.kind != .colon2 || (idx > 0 && toks[idx - 1]!.kind == .colon2) then
          errs := errs.push s!"RUST_DIRECT_LIBC_FORBIDDEN: {relPath}:{tok.line} shadows, aliases, or unqualifies 'libc'"
        else
          match toks[idx + 2]!.kind with
          | .ident item =>
            if !isAllowedSysLibcItem item then
              errs := errs.push s!"RUST_DIRECT_LIBC_FORBIDDEN: {relPath}:{tok.line} uses non-allowlisted libc item '{item}'"
          | _ =>
            errs := errs.push s!"RUST_DIRECT_LIBC_FORBIDDEN: {relPath}:{tok.line} shadows, aliases, or unqualifies 'libc'"
      else if name == "syscall" then
        let okCall :=
          relPath == "LeanSwe/PostFork/rust/src/sys.rs" &&
          idx >= 2 &&
          toks[idx - 2]!.kind == .ident "libc" &&
          toks[idx - 1]!.kind == .colon2 &&
          idx + 5 < n &&
          toks[idx + 1]!.kind == .lparen &&
          toks[idx + 2]!.kind == .ident "libc" &&
          toks[idx + 3]!.kind == .colon2 &&
          toks[idx + 5]!.kind == .comma &&
          match toks[idx + 4]!.kind with
          | .ident nr => isAllowedSysSyscallNr nr
          | _ => false
        if !okCall then
          errs := errs.push s!"RUST_SYSCALL_NR_FORBIDDEN: {relPath}:{tok.line} invokes non-allowlisted or uncanonical syscall"
      else if name == "no_mangle" then
        if relPath != "LeanSwe/PostFork/rust/src/ffi.rs" then
          errs := errs.push s!"RUST_NO_MANGLE_FORBIDDEN: {relPath}:{tok.line} uses #[no_mangle] outside ffi.rs"
        else
          let mut j := idx + 1
          let mut fnTarget? : Option String := none
          while j + 1 < n && toks[j]!.kind != .lbrace && toks[j]!.kind != .semi do
            if toks[j]!.kind == .ident "fn" then
              if let .ident fnName := toks[j + 1]!.kind then
                fnTarget? := some fnName
              break
            j := j + 1
          match fnTarget? with
          | some fnName =>
            if !isAllowedPostForkNoMangleFn fnName then
              errs := errs.push s!"RUST_NO_MANGLE_FORBIDDEN: {relPath}:{tok.line} exports unauthorized symbol '{fnName}'"
          | none =>
            errs := errs.push s!"RUST_NO_MANGLE_FORBIDDEN: {relPath}:{tok.line} #[no_mangle] does not attach to a named fn"
  let (funcs, scopeErrs) := scanRustScope relPath toks false
  errs := errs ++ scopeErrs ++ findRustCallCycleErrors relPath funcs
  return errs

private def isAllowedLeanSourcePath (relPath : String) : Bool :=
  if !relPath.endsWith ".lean" then
    false
  else if relPath == "lakefile.lean" || relPath == "LeanSwe.lean" then
    true
  else if !(relPath.splitOn "/").contains "c" && (
      relPath.startsWith "Core/" ||
      relPath.startsWith "LeanSwe/" ||
      relPath.startsWith "Tests/" ||
      relPath.startsWith "Fuzz/") then
    true
  else
    relPath.startsWith "scripts/Check" && (relPath.splitOn "/").length == 2

/-- Audit tracked non-Lean files and non-legacy C code against `.foreign-budget.json`. -/
def main (args : List String) : IO UInt32 := do
  let repoDir : System.FilePath := args.headD "."
  let budgetPath := repoDir / ".foreign-budget.json"
  unless ← budgetPath.pathExists do
    IO.eprintln s!"MISSING_FOREIGN_BUDGET: {budgetPath}"
    return 1

  let budgetRaw ← IO.FS.readFile budgetPath
  let budget ← match parseBudget budgetRaw with
    | .ok b => pure b
    | .error err =>
      IO.eprintln err
      return 1

  let trackedFiles ← match ← gitLsFiles repoDir with
    | .ok fs => pure fs
    | .error err =>
      IO.eprintln err
      return 1

  let mut errors : Array String := #[]
  let mut trackedForeign := 0
  let mut checkedCFiles := 0
  let mut checkedCFuncs := 0
  let mut legacyCFiles := 0
  let mut seenVendored : Std.HashSet String := {}

  for relPath in trackedFiles do
    if staticMetadataFiles.contains relPath then
      continue
    let fullPath := repoDir / relPath
    if isAllowedLeanSourcePath relPath then
      if ← fullPath.pathExists then
        let leanBytes ← IO.FS.readBinFile fullPath
        if leanBytes.size >= 2 && leanBytes[0]! == 35 && leanBytes[1]! == 33 then
          errors := errors.push s!"LEAN_SHEBANG_FORBIDDEN: {relPath} starts with '#!'"
      continue
    if let some vend := budget.vendored.get? relPath then
      trackedForeign := trackedForeign + 1
      seenVendored := seenVendored.insert relPath
      unless ← fullPath.pathExists do
        errors := errors.push s!"VENDORED_HASH_MISMATCH: missing vendored file {relPath}"
        continue
      match ← computeSha256 fullPath with
      | .error err => errors := errors.push s!"VENDORED_HASH_MISMATCH: {err}"
      | .ok actualHex =>
        if actualHex != vend.sha256 then
          errors := errors.push s!"VENDORED_HASH_MISMATCH: {relPath} sha256={actualHex} expected={vend.sha256}"
      if let some maxL := vend.maxLines? then
        let bytes ← IO.FS.readBinFile fullPath
        let actualLines := countLinesBytes bytes
        if actualLines > maxL then
          errors := errors.push s!"FOREIGN_LINE_CAP_EXCEEDED: {relPath} has {actualLines} lines (max {maxL})"
      continue

    trackedForeign := trackedForeign + 1
    let some entry := budget.files.get? relPath | do
      errors := errors.push s!"UNBUDGETED_FOREIGN_FILE: {relPath} is tracked in git but absent from .foreign-budget.json"
      continue

    unless ← fullPath.pathExists do
      errors := errors.push s!"MISSING_TRACKED_FOREIGN_FILE: {relPath}"
      continue
    let bytes ← IO.FS.readBinFile fullPath
    let actualLines := countLinesBytes bytes
    if actualLines > entry.maxLines then
      errors := errors.push s!"FOREIGN_LINE_CAP_EXCEEDED: {relPath} has {actualLines} lines (max {entry.maxLines})"

    if isCOrHeader relPath then
      if entry.legacyUnmigrated then
        legacyCFiles := legacyCFiles + 1
      else
        checkedCFiles := checkedCFiles + 1
        let (fileErrs, fnCount) := checkNonLegacyCFile relPath bytes budget
        checkedCFuncs := checkedCFuncs + fnCount
        errors := errors ++ fileErrs
    else if relPath.endsWith ".rs" && !entry.legacyUnmigrated then
      if isAeneasExtractedRustPath relPath then
        errors := errors ++ checkAeneasRustFile relPath bytes
      else
        errors := errors ++ checkNonAeneasRustFile relPath bytes

  for (vendPath, _) in budget.vendored do
    if !seenVendored.contains vendPath then
      errors := errors.push s!"VENDORED_HASH_MISMATCH: vendored file {vendPath} is not tracked by git"

  IO.println s!"FOREIGN_THINNESS_CHECK: tracked_foreign={trackedForeign} checked_c_files={checkedCFiles} checked_c_funcs={checkedCFuncs} legacy_c_files={legacyCFiles} errors={errors.size}"
  if errors.isEmpty then
    return 0
  else
    for err in errors do
      IO.eprintln err
    return 1
