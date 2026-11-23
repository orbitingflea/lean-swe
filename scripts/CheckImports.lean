import Lean

/-!
Lean 4 module-header import hygiene gate (`scripts/CheckImports.lean`).

Uses Lean's own `Lean.Parser.parseHeader` and `Lean.Elab.headerToImports` to enforce
import policy across every `.lean` file in the repository without requiring compiled
`.olean` artifacts or running Lake:

1. Rejects non-UTF-8 files, embedded NUL (`0x00`) bytes, and leading UTF-8 BOM (`U+FEFF`).
2. Checks `msgs.hasErrors` BEFORE calling `Lean.Elab.headerToImports` so malformed
   headers (such as dangling `import all`, partial trailing dots like `import Mathlib.`,
   `public import all`, `import all` / `public import` / `meta import` without `module`,
   or unterminated block comments) fail closed without panicking.
3. Rejects misplaced `import` / `private import` directives immediately after the parsed
   header (including after leading module/doc comments).
4. Rejects `import all` targeting any module whose root is outside the intra-repo roots
   (`Core`, `LeanSwe`, `Fuzz`, `Tests`), including French-quoted single-segment names
   such as `import all «LeanSwe.Foo»`.
5. Rejects bare umbrella imports (`import Mathlib`, `import «Mathlib»`,
   `public import Mathlib`, `meta import Mathlib`, etc.); specific submodules such as
   `import Mathlib.Data.Nat.Basic` are allowed.

Usage:
  `lean -DwarningAsError=true --run scripts/CheckImports.lean [PATH...]`
  `lean -DwarningAsError=true --run scripts/CheckImports.lean --self-test`
-/

open Lean

private def internalImportRoots : Array String :=
  #["Core", "LeanSwe", "Fuzz", "Tests"]

private def forbiddenUmbrellaImports : Array String :=
  #["Mathlib"]

private def isInternalImportRoot (mod : Name) : Bool :=
  let root := mod.getRoot
  match root with
  | .str .anonymous rootSeg =>
    !rootSeg.contains '.' &&
    internalImportRoots.contains rootSeg &&
    (root == `Core || root == `LeanSwe || root == `Fuzz || root == `Tests)
  | _ => false

private def isForbiddenUmbrellaImport (mod : Name) : Bool :=
  match mod with
  | .str .anonymous seg => forbiddenUmbrellaImports.contains seg
  | _ => false

private def isWellFormedImportNode (stx : Syntax) : Bool :=
  stx.isOfKind `Lean.Parser.Module.import &&
  stx.getNumArgs == 6 &&
  (stx.getArg 5).matchesNull 0 &&
  ((stx.getArg 0).isNone ||
    ((stx.getArg 0).matchesNull 1 && ((stx.getArg 0).getArg 0).isOfKind `Lean.Parser.Module.public)) &&
  ((stx.getArg 1).isNone ||
    ((stx.getArg 1).matchesNull 1 && ((stx.getArg 1).getArg 0).isOfKind `Lean.Parser.Module.meta)) &&
  ((stx.getArg 3).isNone ||
    ((stx.getArg 3).matchesNull 1 && ((stx.getArg 3).getArg 0).isOfKind `Lean.Parser.Module.all))

private def isWellFormedHeaderNode (stx : Syntax) : Bool :=
  stx.isOfKind `Lean.Parser.Module.header &&
  stx.getNumArgs == 3 &&
  ((stx.getArg 0).isNone ||
    ((stx.getArg 0).matchesNull 1 && ((stx.getArg 0).getArg 0).isOfKind `Lean.Parser.Module.moduleTk)) &&
  ((stx.getArg 1).isNone ||
    ((stx.getArg 1).matchesNull 1 && ((stx.getArg 1).getArg 0).isOfKind `Lean.Parser.Module.prelude)) &&
  (stx.getArg 2).getArgs.all isWellFormedImportNode

private def isAsciiWs (b : UInt8) : Bool :=
  b == 32 || b == 9 || b == 10 || b == 13

private def isAsciiIdentStart (b : UInt8) : Bool :=
  (b >= 65 && b <= 90) || (b >= 97 && b <= 122) || b == 95

private def isIdentContByte (b : UInt8) : Bool :=
  isAsciiIdentStart b || (b >= 48 && b <= 57) || b == 39 || b == 33 || b == 63 || b >= 128

private def skipWsAndComments (bytes : ByteArray) (start : Nat) : Except Nat Nat := Id.run do
  let n := bytes.size
  let mut i := start
  while i < n do
    let b := bytes[i]!
    if isAsciiWs b then
      i := i + 1
    else if b == 45 && i + 1 < n && bytes[i + 1]! == 45 then
      i := i + 2
      while i < n && bytes[i]! != 10 do
        i := i + 1
    else if b == 47 && i + 1 < n && bytes[i + 1]! == 45 then
      let openPos := i
      i := i + 2
      let mut depth : Nat := 1
      while i < n && depth > 0 do
        let c := bytes[i]!
        if c == 47 && i + 1 < n && bytes[i + 1]! == 45 then
          depth := depth + 1
          i := i + 2
        else if c == 45 && i + 1 < n && bytes[i + 1]! == 47 then
          depth := depth - 1
          i := i + 2
        else
          i := i + 1
      if depth > 0 then
        return .error openPos
    else
      break
  return .ok i

private def readAsciiWord? (bytes : ByteArray) (start : Nat) : Option (String × Nat) := Id.run do
  let n := bytes.size
  if start >= n then
    return none
  let b0 := bytes[start]!
  if !isAsciiIdentStart b0 then
    return none
  let mut i := start
  while i < n && isIdentContByte bytes[i]! do
    if bytes[i]! >= 128 then
      return none
    i := i + 1
  let mut word := ""
  for k in [start : i] do
    word := word.push (Char.ofNat bytes[k]!.toNat)
  return some (word, i)

private def isImportModifier (word : String) : Bool :=
  word == "public" || word == "private" || word == "meta"

private def isBomAt (bytes : ByteArray) (pos : Nat) : Bool :=
  pos + 2 < bytes.size &&
  bytes[pos]! == 0xEF &&
  bytes[pos + 1]! == 0xBB &&
  bytes[pos + 2]! == 0xBF

private def checkPostHeaderLeadingImport (relPath : String) (bytes : ByteArray) (baseOffset : Nat)
    (fileMap : FileMap) (startPos : String.Pos.Raw) : Option String := Id.run do
  let mut pos := baseOffset + startPos.byteIdx
  let mut mods : Array String := #[]
  let mut firstPos? : Option Nat := none
  while pos < bytes.size do
    match skipWsAndComments bytes pos with
    | .error openPos =>
      let lineNo := (fileMap.toPosition ⟨openPos - baseOffset⟩).line
      return some s!"{relPath}:{lineNo}: malformed module header: unterminated block comment"
    | .ok nextPos =>
      if nextPos < bytes.size && bytes[nextPos]! == 0 then
        let lineNo := (fileMap.toPosition ⟨nextPos - baseOffset⟩).line
        return some s!"{relPath}:{lineNo}: disallowed NUL byte (0x00) at header boundary"
      if isBomAt bytes nextPos then
        let lineNo := (fileMap.toPosition ⟨nextPos - baseOffset⟩).line
        return some s!"{relPath}:{lineNo}: disallowed UTF-8 BOM (U+FEFF) at header boundary"
      let some (word, endPos) := readAsciiWord? bytes nextPos
        | return none
      if firstPos?.isNone then
        firstPos? := some (nextPos - baseOffset)
      if word == "import" then
        let tokPos := firstPos?.getD (nextPos - baseOffset)
        let lineNo := (fileMap.toPosition ⟨tokPos⟩).line
        if mods.contains "private" then
          let pfx := " ".intercalate (mods.push "import").toList
          return some s!"{relPath}:{lineNo}: disallowed '{pfx}' directive (Lean 4 forbids 'private import')"
        else
          let pfx := " ".intercalate (mods.push "import").toList
          return some s!"{relPath}:{lineNo}: misplaced '{pfx}' directive after header"
      else if isImportModifier word then
        mods := mods.push word
        pos := endPos
      else
        return none
  return none

private def countLeadingUtf8BomBytes (bytes : ByteArray) : Nat := Id.run do
  let mut offset := 0
  while isBomAt bytes offset do
    offset := offset + 3
  return offset

private def stripLeadingUtf8Boms (src : String) : Bool × String := Id.run do
  let mut hadBom := false
  let mut cur := src
  while cur.startsWith "\uFEFF" do
    hadBom := true
    cur := (cur.drop 1).copy
  return (hadBom, cur)

private def cleanMessageText (msg : Message) : IO String := do
  let raw := (← msg.data.toString).trimAscii.toString
  return raw.replace "\r\n" " " |>.replace "\n" " "

private def checkSourceWithBytes (relPath : String) (bytes : ByteArray) (rawSrc : String) : IO (Nat × Array String) := do
  let mut violations : Array String := #[]
  let bomBytes := countLeadingUtf8BomBytes bytes
  let (hadBom, src) :=
    if bomBytes > 0 then
      stripLeadingUtf8Boms rawSrc
    else
      (false, rawSrc)
  if hadBom then
    violations := violations.push
      s!"{relPath}:1: disallowed leading UTF-8 BOM (U+FEFF); Lean files must be UTF-8 without BOM"

  let inputCtx := Parser.mkInputContext src relPath
  let (stx, pst, msgs) ← Parser.parseHeader inputCtx

  if msgs.hasErrors then
    let mut emitted := 0
    for m in msgs.toList do
      if m.severity == .error then
        let text ← cleanMessageText m
        violations := violations.push s!"{relPath}:{m.pos.line}: malformed module header: {text}"
        emitted := emitted + 1
    if emitted == 0 then
      violations := violations.push s!"{relPath}:1: malformed module header"
    return (0, violations)

  if !isWellFormedHeaderNode stx.raw then
    violations := violations.push s!"{relPath}:1: malformed module header syntax node"
    return (0, violations)

  let importNodes := (stx.raw.getArg 2).getArgs
  let imps := Elab.headerToImports stx (includeInit := false)
  for idx in [0 : imps.size] do
    let imp := imps[idx]!
    let lineNo := match importNodes[idx]?.bind (·.getPos?) with
      | some p => (inputCtx.fileMap.toPosition p).line
      | none => 1
    let modStr := imp.module.toString
    if imp.importAll && !isInternalImportRoot imp.module then
      violations := violations.push
        s!"{relPath}:{lineNo}: disallowed external 'import all {modStr}' (only intra-repo modules under Core/LeanSwe/Fuzz/Tests may use 'import all')"
    if isForbiddenUmbrellaImport imp.module then
      violations := violations.push
        s!"{relPath}:{lineNo}: disallowed umbrella import '{modStr}' (import specific submodule(s) instead, e.g. 'Mathlib.Data.Nat.Basic')"

  if let some err := checkPostHeaderLeadingImport relPath bytes bomBytes inputCtx.fileMap pst.pos then
    violations := violations.push err

  return (imps.size, violations)

private def checkSourceText (relPath : String) (rawSrc : String) : IO (Nat × Array String) :=
  checkSourceWithBytes relPath rawSrc.toUTF8 rawSrc

private def checkFileBytes (relPath : String) (bytes : ByteArray) : IO (Nat × Array String) := do
  let some rawSrc := String.fromUTF8? bytes
    | return (0, #[s!"{relPath}:1: invalid UTF-8 encoding (cannot decode Lean source file)"])
  checkSourceWithBytes relPath bytes rawSrc

private def isSkippedWalkDir (relPath fileName : String) : Bool :=
  fileName == ".git" ||
  fileName == ".lake" ||
  fileName == ".lint-cache" ||
  fileName == ".agents" ||
  relPath == "build" ||
  relPath == "target" ||
  relPath.endsWith "/rust/target"

private def hasSkippedUntrackedSegment (relPath : String) : Bool :=
  let segs := relPath.splitOn "/"
  segs.any (fun s => s == ".git" || s == ".lake" || s == ".lint-cache" || s == ".agents")

private def isRegularFileSymlinkSafe (fullPath : System.FilePath) : IO (Option IO.FS.FileType) := do
  try
    let md ← fullPath.symlinkMetadata
    return some md.type
  catch _ =>
    return none

private def gitListLeanFiles (repoDir : System.FilePath) : IO (Except String (Array String)) := do
  let trackedOut ← IO.Process.output {
    cmd := "git"
    args := #["-C", repoDir.toString, "ls-files", "-s", "-z"]
  }
  if trackedOut.exitCode != 0 then
    return .error s!"git ls-files failed in '{repoDir}': {trackedOut.stderr.trimAscii.toString}"

  let mut seen : Std.HashSet String := {}
  let mut paths : Array String := #[]
  for rec in trackedOut.stdout.splitOn "\x00" do
    if rec.isEmpty then
      continue
    let tabIdx := rec.splitOn "\t"
    if tabIdx.length < 2 then
      continue
    let metaPart := tabIdx[0]!
    let relPath := "\t".intercalate tabIdx.tail!
    let mode := (metaPart.splitOn " ").headD ""
    if (mode == "100644" || mode == "100755") && relPath.endsWith ".lean" then
      if !seen.contains relPath then
        seen := seen.insert relPath
        paths := paths.push relPath

  let otherOut ← IO.Process.output {
    cmd := "git"
    args := #["-C", repoDir.toString, "ls-files", "--others", "--exclude-standard", "-z"]
  }
  if otherOut.exitCode != 0 then
    return .error s!"git ls-files --others failed in '{repoDir}': {otherOut.stderr.trimAscii.toString}"
  for relPath in otherOut.stdout.splitOn "\x00" do
    if relPath.isEmpty || !relPath.endsWith ".lean" || hasSkippedUntrackedSegment relPath then
      continue
    if !seen.contains relPath then
      seen := seen.insert relPath
      paths := paths.push relPath

  return .ok (paths.qsort (· < ·))

private def walkDirLeanFiles (rootDir : System.FilePath) : IO (Except String (Array String)) := do
  let mut stack : Array (System.FilePath × String) := #[(rootDir, "")]
  let mut files : Array String := #[]
  while !stack.isEmpty do
    let (curDir, relPrefix) := stack.back!
    stack := stack.pop
    let entries ← try
      curDir.readDir
    catch e =>
      return .error s!"failed to read directory '{curDir}': {e}"
    for entry in entries do
      let rel := if relPrefix.isEmpty then entry.fileName else s!"{relPrefix}/{entry.fileName}"
      let full := entry.path
      match ← isRegularFileSymlinkSafe full with
      | some .symlink => pure ()
      | some .dir =>
        if !isSkippedWalkDir rel entry.fileName then
          stack := stack.push (full, rel)
      | some .file =>
        if entry.fileName.endsWith ".lean" then
          files := files.push rel
      | some .other => pure ()
      | none =>
        return .error s!"failed to inspect '{full}'"
  return .ok (files.qsort (· < ·))

private structure CheckSummary where
  checked : Nat := 0
  imports : Nat := 0
  violations : Array String := #[]
  errors : Array String := #[]

private def checkTargetPath (target : System.FilePath) : IO CheckSummary := do
  let md? ← isRegularFileSymlinkSafe target
  match md? with
  | none =>
    return { errors := #[s!"target path not found or unreadable: {target}"] }
  | some .symlink =>
    return {}
  | some .other =>
    return { errors := #[s!"target path is neither regular file nor directory: {target}"] }
  | some .file =>
    let bytes ← try
      IO.FS.readBinFile target
    catch e =>
      return { errors := #[s!"failed to read '{target}': {e}"] }
    let (impCount, viols) ← checkFileBytes target.toString bytes
    return { checked := 1, imports := impCount, violations := viols }
  | some .dir =>
    let isGitRoot ← (target / ".git").pathExists
    let relPaths ← if isGitRoot then
      match ← gitListLeanFiles target with
      | .ok ps => pure ps
      | .error e => return { errors := #[e] }
    else
      match ← walkDirLeanFiles target with
      | .ok ps => pure ps
      | .error e => return { errors := #[e] }
    let mut checked := 0
    let mut totalImports := 0
    let mut violations : Array String := #[]
    let mut errors : Array String := #[]
    for relPath in relPaths do
      let fullPath := target / relPath
      match ← isRegularFileSymlinkSafe fullPath with
      | some .file =>
        checked := checked + 1
        let bytes ← try
          IO.FS.readBinFile fullPath
        catch e =>
          errors := errors.push s!"failed to read '{relPath}': {e}"
          continue
        let (impCount, viols) ← checkFileBytes relPath bytes
        totalImports := totalImports + impCount
        violations := violations ++ viols
      | some .symlink => pure ()
      | some _ => pure ()
      | none => pure ()
    return { checked, imports := totalImports, violations, errors }

private def containsSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def writeFileCreatingParents (p : System.FilePath) (content : String) : IO Unit := do
  if let some parent := p.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile p content

private def writeBinCreatingParents (p : System.FilePath) (bytes : ByteArray) : IO Unit := do
  if let some parent := p.parent then
    IO.FS.createDirAll parent
  IO.FS.writeBinFile p bytes

private def runCmdOk (cwd : System.FilePath) (cmd : String) (args : Array String) : IO Unit := do
  let out ← IO.Process.output {
    cmd := cmd
    args := args
    cwd := some cwd
    env := #[
      ("GIT_AUTHOR_NAME", some "Test"),
      ("GIT_AUTHOR_EMAIL", some "test@example.com"),
      ("GIT_COMMITTER_NAME", some "Test"),
      ("GIT_COMMITTER_EMAIL", some "test@example.com")
    ]
  }
  if out.exitCode != 0 then
    throw (IO.userError s!"command '{cmd} {" ".intercalate args.toList}' failed: {out.stdout}{out.stderr}")

private def makeTempDir (pfx : String) : IO System.FilePath := do
  let out ← IO.Process.output {
    cmd := "mktemp"
    args := #["-d", s!"/tmp/{pfx}.XXXXXX"]
  }
  if out.exitCode != 0 then
    throw (IO.userError s!"mktemp failed: {out.stderr}")
  return ⟨out.stdout.trimAscii.toString⟩

private def removeDirForce (p : System.FilePath) : IO Unit := do
  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", p.toString] }

private def assertTrue (label : String) (cond : Bool) (detail : String := "") : IO Unit := do
  unless cond do
    throw (IO.userError s!"SELF_TEST_FAIL [{label}]: {detail}")

private def runSelfTests : IO UInt32 := do
  let mut checks : Nat := 0

  let umbrellaCases : Array (String × String) := #[
    ("bare_eof", "import Mathlib"),
    ("bare_nl", "import Mathlib\n"),
    ("mod_public", "module\npublic import Mathlib\n"),
    ("mod_meta", "module\nmeta import Mathlib\n"),
    ("mod_public_meta", "module\npublic meta import Mathlib\n"),
    ("quoted_mathlib", "import «Mathlib»\n"),
    ("trailing_line_comment", "import Mathlib -- trailing comment\n"),
    ("nospace_line_comment", "import Mathlib--no-space comment\n"),
    ("trailing_block_comment", "import Mathlib /- trailing block -/\n"),
    ("inline_block_comment", "import /- inline -/ Mathlib\n"),
    ("multiline_import", "import\n  Mathlib\n"),
    ("same_line_first", "import Mathlib import LeanSwe.Json.Types\n"),
    ("same_line_second", "import Aeneas import Mathlib\n"),
    ("space_dot", "import Mathlib .Data.Nat.Basic\n"),
    ("newline_dot", "import Mathlib\n.Data.Nat.Basic\n"),
    ("comment_dot", "import Mathlib/- c -/.Data.Nat.Basic\n"),
    ("prelude_umbrella", "prelude\nimport Mathlib\n"),
    ("crlf_umbrella", "module\r\nimport Mathlib\r\n"),
    ("after_unclosed_in_line_comment", "-- comment with unclosed /-\nimport Mathlib\n")
  ]
  for (label, src) in umbrellaCases do
    let (_, errs) ← checkSourceText "Demo.lean" src
    assertTrue s!"umbrella:{label}" (errs.size == 1 && containsSubstr errs[0]! "umbrella import 'Mathlib'")
      s!"got {errs}"
    checks := checks + 1

  let (_, unclosedLineErrs) ← checkSourceText "After.lean" "-- comment with unclosed /-\nimport Mathlib\n"
  assertTrue "line_number_after_comment"
    (unclosedLineErrs.size == 1 && containsSubstr unclosedLineErrs[0]! "After.lean:2:")
    s!"got {unclosedLineErrs}"
  checks := checks + 1

  let (_, bomUmbrellaErrs) ← checkSourceText "Demo.lean" "\uFEFFimport Mathlib\r\n"
  assertTrue "bom_umbrella"
    (bomUmbrellaErrs.size == 2 &&
      containsSubstr bomUmbrellaErrs[0]! "UTF-8 BOM" &&
      containsSubstr bomUmbrellaErrs[1]! "umbrella import 'Mathlib'")
    s!"got {bomUmbrellaErrs}"
  checks := checks + 1

  let (_, bomMultiErrs) ← checkSourceText "Demo.lean" "\uFEFF\uFEFFimport Mathlib\n"
  assertTrue "bom_multi_umbrella"
    (bomMultiErrs.size == 2 &&
      containsSubstr bomMultiErrs[0]! "UTF-8 BOM" &&
      containsSubstr bomMultiErrs[1]! "umbrella import 'Mathlib'")
    s!"got {bomMultiErrs}"
  checks := checks + 1

  let (_, bomCleanErrs) ← checkSourceText "Demo.lean" "\uFEFFimport Core.Types\n"
  assertTrue "bom_alone_rejected"
    (bomCleanErrs.size == 1 && containsSubstr bomCleanErrs[0]! "Demo.lean:1: disallowed leading UTF-8 BOM")
    s!"got {bomCleanErrs}"
  checks := checks + 1

  let (_, bomPrivErrs) ← checkSourceText "Demo.lean" "\uFEFFprivate import Mathlib\n"
  assertTrue "bom_then_private_import"
    (bomPrivErrs.size == 2 &&
      containsSubstr bomPrivErrs[0]! "UTF-8 BOM" &&
      containsSubstr bomPrivErrs[1]! "private import")
    s!"got {bomPrivErrs}"
  checks := checks + 1

  let midBomSrc := "import " ++ String.singleton (Char.ofNat 0xFEFF) ++ "Mathlib\n"
  let (_, midBomErrs) ← checkSourceText "Demo.lean" midBomSrc
  assertTrue "mid_bom_rejected" (!midBomErrs.isEmpty) s!"got {midBomErrs}"
  checks := checks + 1

  let externalAllCases : Array (String × String × String) := #[
    ("mathlib_sub", "module\nimport all Mathlib.Data.Nat.Basic\n", "Mathlib.Data.Nat.Basic"),
    ("meta_std", "module\nmeta import all Std.Data.HashMap\n", "Std.Data.HashMap"),
    ("aeneas", "module\nimport all Aeneas\n", "Aeneas"),
    ("aesop", "module\nimport all Aesop\n", "Aesop"),
    ("quoted_mathlib_seg", "module\nimport all «Mathlib».Data.Nat.Basic\n", "Mathlib.Data.Nat.Basic"),
    ("leanswe_extra", "module\nimport all LeanSweExtra.Foo\n", "LeanSweExtra.Foo"),
    ("core_extra", "module\nimport all CoreExtra\n", "CoreExtra"),
    ("fuzz_extra", "module\nimport all FuzzExtra.Suite\n", "FuzzExtra.Suite"),
    ("tests_extra", "module\nimport all TestsExtra.Main\n", "TestsExtra.Main"),
    ("quoted_leanswe_dot", "module\nimport all «LeanSwe.Foo»\n", "«LeanSwe.Foo»"),
    ("quoted_leanswe_dot_sub", "module\nimport all «LeanSwe.Foo».Bar\n", "«LeanSwe.Foo».Bar"),
    ("quoted_core_dot", "module\nimport all «Core.Types»\n", "«Core.Types»"),
    ("multiline_comment", "module\nimport /- c -/ all\n  -- comment\n  Batteries.Data.List\n", "Batteries.Data.List"),
    ("prelude_all", "module\nprelude\nimport all Batteries.Foo\n", "Batteries.Foo")
  ]
  for (label, src, expectedMod) in externalAllCases do
    let (_, errs) ← checkSourceText "Demo.lean" src
    assertTrue s!"external_all:{label}"
      (errs.size == 1 &&
        containsSubstr errs[0]! s!"disallowed external 'import all {expectedMod}'")
      s!"got {errs}"
    checks := checks + 1

  let (_, bothErrs) ← checkSourceText "Demo.lean" "module\nimport all Mathlib\n"
  assertTrue "import_all_mathlib_both"
    (bothErrs.size == 2 &&
      containsSubstr bothErrs[0]! "Demo.lean:2:" &&
      containsSubstr bothErrs[0]! "import all Mathlib" &&
      containsSubstr bothErrs[1]! "Demo.lean:2:" &&
      containsSubstr bothErrs[1]! "umbrella import 'Mathlib'")
    s!"got {bothErrs}"
  checks := checks + 1

  let malformedCases : Array (String × String) := #[
    ("dangling_all_bare", "import all\n"),
    ("dangling_all_mod", "module\nimport all\n"),
    ("dangling_all_dot_bare", "import all\n.Foo\n"),
    ("dangling_all_dot_mod", "module\nimport all\n.Foo\n"),
    ("dangling_pub_all_pair", "public import all\npublic import Mathlib\n"),
    ("mod_dangling_pub_all_pair", "module\npublic import all\npublic import Mathlib\n"),
    ("pub_all_without_mod", "public import all Batteries.Foo\n"),
    ("mod_pub_all_ext", "module\npublic import all Batteries.Foo\n"),
    ("mod_pub_all_int", "module\npublic import all LeanSwe.Foo.Impl\n"),
    ("pub_meta_all_without_mod", "public meta import all Lean.Meta\n"),
    ("mod_pub_meta_all", "module\npublic meta import all Lean.Meta\n"),
    ("bare_public_import", "public import Mathlib\n"),
    ("bare_meta_import", "meta import Mathlib\n"),
    ("bare_public_meta_import", "public meta import Mathlib\n"),
    ("bare_import_all_ext", "import all Mathlib.Data.Nat.Basic\n"),
    ("bare_import_all_int", "import all LeanSwe.Foo.Impl\n"),
    ("bare_meta_import_all", "meta import all Std.Data.HashMap\n"),
    ("trailing_dot_space", "import Mathlib. Data.Nat.Basic\n"),
    ("trailing_dot_eof", "import Mathlib."),
    ("unclosed_header_comment", "/- unclosed\nimport Core.Types\n"),
    ("unclosed_post_header_comment", "import Core.Types\n/- unclosed after header\n"),
    ("numeric_seg", "module\nimport all «LeanSwe».1\n")
  ]
  for (label, src) in malformedCases do
    let (_, errs) ← checkSourceText "Demo.lean" src
    assertTrue s!"malformed:{label}"
      (!errs.isEmpty && containsSubstr errs[0]! "malformed module header")
      s!"got {errs}"
    checks := checks + 1

  let misplacedCases : Array (String × String × String) := #[
    ("private_bare", "private import Mathlib\n", "private import"),
    ("private_mod", "module\nprivate import Mathlib\n", "private import"),
    ("private_all_ext", "private import all Init.Core\n", "private import"),
    ("private_all_ext_mod", "module\nprivate import all Init.Core\n", "private import"),
    ("private_all_int", "private import all LeanSwe.Foo.Impl\n", "private import"),
    ("private_meta", "module\nprivate meta import Mathlib\n", "private meta import"),
    ("private_comment_import", "private /- c -/ import Mathlib\n", "private import"),
    ("after_module_doc", "/-! module doc -/\nimport Mathlib\n", "misplaced 'import'"),
    ("after_doc_comment", "/-- doc comment -/\nimport Mathlib\n", "misplaced 'import'"),
    ("after_doc_public_import", "module\n/-! module doc -/\npublic import Mathlib\n", "misplaced 'public import'")
  ]
  for (label, src, needle) in misplacedCases do
    let (_, errs) ← checkSourceText "Demo.lean" src
    assertTrue s!"misplaced:{label}"
      (errs.size == 1 && containsSubstr errs[0]! needle)
      s!"got {errs}"
    checks := checks + 1

  let badUtf8Cases : Array (String × ByteArray) := #[
    ("invalid_ff_fe", ByteArray.mk #[0xFF, 0xFE, 0x0A]),
    ("truncated_multibyte", ByteArray.mk #[0xE2, 0x82]),
    ("overlong_nul", ByteArray.mk #[0xC0, 0x80])
  ]
  for (label, bs) in badUtf8Cases do
    let (_, errs) ← checkFileBytes "Bad.lean" bs
    assertTrue s!"bad_utf8:{label}"
      (errs.size == 1 && containsSubstr errs[0]! "invalid UTF-8")
      s!"got {errs}"
    checks := checks + 1

  let nulBytes := ByteArray.mk (#[0x00] ++ "import Mathlib\n".toUTF8.data)
  let (_, nulErrs) ← checkFileBytes "Nul.lean" nulBytes
  assertTrue "nul_byte_rejected"
    (nulErrs.size == 1 && containsSubstr nulErrs[0]! "NUL byte")
    s!"got {nulErrs}"
  checks := checks + 1

  let nulAfterImp := ByteArray.mk ("import Core.Types\n".toUTF8.data ++ #[0x00] ++ "import Mathlib\n".toUTF8.data)
  let (_, nulAfterErrs) ← checkFileBytes "Nul2.lean" nulAfterImp
  assertTrue "nul_after_import_rejected"
    (nulAfterErrs.size == 1 && containsSubstr nulAfterErrs[0]! "Nul2.lean:2:" && containsSubstr nulAfterErrs[0]! "NUL byte")
    s!"got {nulAfterErrs}"
  checks := checks + 1

  let nulMidImp := ByteArray.mk ("import ".toUTF8.data ++ #[0x00] ++ "Mathlib\n".toUTF8.data)
  let (_, nulMidErrs) ← checkFileBytes "Nul3.lean" nulMidImp
  assertTrue "nul_mid_import_rejected" (!nulMidErrs.isEmpty) s!"got {nulMidErrs}"
  checks := checks + 1

  let nulInComment := ByteArray.mk ("/- a".toUTF8.data ++ #[0x00] ++ "b -/\nimport Mathlib\n".toUTF8.data)
  let (_, nulCmtErrs) ← checkFileBytes "Nul4.lean" nulInComment
  assertTrue "nul_in_comment_catches_import"
    (nulCmtErrs.size == 1 && containsSubstr nulCmtErrs[0]! "umbrella import 'Mathlib'")
    s!"got {nulCmtErrs}"
  checks := checks + 1

  let (_, bomAfterImpErrs) ← checkSourceText "Bom2.lean" "import Core.Types\n\uFEFFimport Mathlib\n"
  assertTrue "bom_after_import_rejected"
    (bomAfterImpErrs.size == 1 && containsSubstr bomAfterImpErrs[0]! "Bom2.lean:2:" && containsSubstr bomAfterImpErrs[0]! "UTF-8 BOM")
    s!"got {bomAfterImpErrs}"
  checks := checks + 1

  let allowedClassic := "\n".intercalate [
    "import Mathlib.Data.Nat.Basic",
    "import «Mathlib».Data.Nat.Basic",
    "import Mathlib.«Data».Nat.Basic",
    "import Mathlib.all",
    "import MathlibExtra",
    "import Mathlib_Extra",
    "import Mathlib'",
    "import Mathlib1",
    "import Mathlib₁",
    "import My.Mathlib",
    "import LeanSwe.Mathlib",
    "import Aeneas",
    "import Lean",
    "import Lake",
    "import all.Foo",
    "import all.Mathlib",
    "import «all»",
    "private def x : Nat := 1",
    "def import₁ : Nat := 0"
  ]
  let (classicCount, classicErrs) ← checkSourceText "Classic.lean" allowedClassic
  assertTrue "allowed_classic" (classicErrs.isEmpty && classicCount == 17)
    s!"count={classicCount} errs={classicErrs}"
  checks := checks + 1

  let allowedModule := "\n".intercalate [
    "module",
    "import Mathlib.Data.Nat.Basic",
    "public import Mathlib.Tactic.Ring",
    "meta import Mathlib.Logic.Basic",
    "public meta import Mathlib.Logic.Basic",
    "import «Mathlib».Data.Nat.Basic",
    "import Mathlib.«Data».Nat.Basic",
    "import Mathlib.all",
    "import MathlibExtra",
    "import Mathlib_Extra",
    "import Mathlib'",
    "import Mathlib1",
    "import Mathlib₁",
    "import My.Mathlib",
    "import LeanSwe.Mathlib",
    "import Aeneas",
    "import Lean",
    "import Lake",
    "import all.Foo",
    "import all.Mathlib",
    "import «all»",
    "import all LeanSwe.Foo.Impl",
    "meta import all LeanSwe.Foo.Impl",
    "import all «LeanSwe».Foo.Impl",
    "import all\n  -- multiline intra-repo import all\n  LeanSwe.Bar.Impl",
    "import all Core.NondetTest",
    "import all Fuzz.Common.Rng",
    "import all Tests.Main",
    "import all LeanSwe",
    "import all Core",
    "import all Fuzz",
    "import all Tests",
    "import all «LeanSwe»",
    "private def hidden : Nat := 1",
    "public def shown : Nat := 2"
  ]
  let (modCount, modErrs) ← checkSourceText "Ok.lean" allowedModule
  assertTrue "allowed_module" (modErrs.isEmpty && modCount == 32)
    s!"count={modCount} errs={modErrs}"
  checks := checks + 1

  let (_, emptyErrs) ← checkSourceText "Empty.lean" ""
  assertTrue "empty_file" emptyErrs.isEmpty s!"got {emptyErrs}"
  checks := checks + 1

  let safeBody := "\n".intercalate [
    "-- never write `import Mathlib` or `import all Mathlib.Foo`",
    "/- block comment: import Mathlib; public import all Batteries.Foo -/",
    "/- outer /- nested comment -/ import Mathlib\n   import all Aeneas -/",
    "import LeanSwe.PostFork.Types -- don't write import Mathlib",
    "/-- Doc comment: never use `import Mathlib` or `import all Std.Time`. -/",
    "/-! Module doc: avoid `import Mathlib` and `meta import all Lean.Meta`. -/",
    "def s1 : String := \"import Mathlib\\nimport all Batteries.Foo\"",
    "def s2 : String := \"\nimport Mathlib\nimport all Mathlib.Foo\n\"",
    "def s3 : String := \"escaped \\\" import Mathlib\"",
    "def s4 (x : String) : String := s!\"{x} import Mathlib import all Aeneas\"",
    "def s5 : String := r#\"import Mathlib\nimport all Mathlib.Foo\"#",
    "def s6 : String := r##\" \"import Mathlib\" \"##",
    "def c1 : Char := '\"'",
    "def s7 : String := \"import Mathlib\"",
    "def f (x : Nat) := obj.import Mathlib",
    "def n := `import",
    "def q := ``import",
    "def «import» := Mathlib",
    "def quoted := (import Mathlib)"
  ]
  let (safeCount, safeErrs) ← checkSourceText "Safe.lean" safeBody
  assertTrue "safe_comments_strings_tokens" (safeErrs.isEmpty && safeCount == 1)
    s!"count={safeCount} errs={safeErrs}"
  checks := checks + 1

  let tmpRoot ← makeTempDir "check-imports-test"
  try
    let outsideDir := tmpRoot / "outside"
    writeFileCreatingParents (outsideDir / "BadOutside.lean") "import Mathlib\n"

    let walkDir := tmpRoot / "plain"
    writeFileCreatingParents (walkDir / "Core/Types.lean") "def t : Nat := 1\n"
    writeFileCreatingParents (walkDir / "LeanSwe/Demo/Proofs.lean")
      "module\nimport Mathlib.Data.Nat.Basic\nimport all LeanSwe.Demo.Impl\n"
    writeFileCreatingParents (walkDir / ".lake/packages/bad/Bad.lean") "import Mathlib\n"
    writeFileCreatingParents (walkDir / "harness/.lake/build/Bad.lean") "import Mathlib\n"
    writeFileCreatingParents (walkDir / ".lint-cache/Bad.lean") "import Mathlib\n"
    writeFileCreatingParents (walkDir / ".agents/Bad.lean") "import Mathlib\n"
    writeFileCreatingParents (walkDir / "LeanSwe/PostFork/rust/target/Bad.lean") "import Mathlib\n"
    runCmdOk tmpRoot "ln" #["-s", (outsideDir / "BadOutside.lean").toString, (walkDir / "Link.lean").toString]
    runCmdOk tmpRoot "ln" #["-s", outsideDir.toString, (walkDir / "LinkDir").toString]

    let plainOk ← checkTargetPath walkDir
    assertTrue "walk_skips_build_dirs_and_symlinks"
      (plainOk.checked == 2 && plainOk.violations.isEmpty && plainOk.errors.isEmpty)
      s!"checked={plainOk.checked} viols={plainOk.violations} errs={plainOk.errors}"
    checks := checks + 1

    writeFileCreatingParents (walkDir / "LeanSwe/Demo/Bad.lean") "import Mathlib\n"
    writeBinCreatingParents (walkDir / "LeanSwe/Demo/BadUtf8.lean") (ByteArray.mk #[0xFF, 0xFE])
    writeBinCreatingParents (walkDir / "LeanSwe/Demo/Bom.lean")
      (ByteArray.mk (#[0xEF, 0xBB, 0xBF] ++ "import Core.Types\n".toUTF8.data))
    let plainBad ← checkTargetPath walkDir
    assertTrue "walk_catches_bad_utf8_and_bom"
      (plainBad.checked == 5 &&
        plainBad.violations.size == 3 &&
        plainBad.violations.any (containsSubstr · "LeanSwe/Demo/Bad.lean:1:") &&
        plainBad.violations.any (containsSubstr · "LeanSwe/Demo/BadUtf8.lean:1:") &&
        plainBad.violations.any (containsSubstr · "LeanSwe/Demo/Bom.lean:1:"))
      s!"checked={plainBad.checked} viols={plainBad.violations}"
    checks := checks + 1

    let singleOk ← checkTargetPath (walkDir / "Core/Types.lean")
    assertTrue "single_file_ok"
      (singleOk.checked == 1 && singleOk.violations.isEmpty && singleOk.errors.isEmpty)
      s!"checked={singleOk.checked} viols={singleOk.violations}"
    checks := checks + 1

    let missingRes ← checkTargetPath (tmpRoot / "nonexistent.lean")
    assertTrue "missing_target_errors" (!missingRes.errors.isEmpty) s!"errs={missingRes.errors}"
    checks := checks + 1

    let repoDir := tmpRoot / "repo"
    IO.FS.createDirAll repoDir
    runCmdOk repoDir "git" #["init", "-q"]
    writeFileCreatingParents (repoDir / "LeanSwe/Demo/Impl.lean") "import Core.Types\ndef x := 1\n"
    writeFileCreatingParents (repoDir / "LeanSwe/Demo/Types.lean") "def t := 1\n"
    writeFileCreatingParents (repoDir / "LeanSwe/Demo/Proofs.lean")
      "module\nimport Mathlib.Data.Nat.Basic\nimport all LeanSwe.Demo.Impl\n"
    runCmdOk repoDir "ln" #["-s", "Types.lean", (repoDir / "LeanSwe/Demo/Link.lean").toString]
    runCmdOk repoDir "git" #["add", "."]
    runCmdOk repoDir "git" #["-c", "commit.gpgsign=false", "commit", "-q", "-m", "base"]
    runCmdOk repoDir "git" #["rm", "-q", "LeanSwe/Demo/Impl.lean"]
    runCmdOk repoDir "git" #["-c", "commit.gpgsign=false", "commit", "-q", "-m", "remove impl"]

    writeFileCreatingParents (repoDir / ".lake/packages/bad/Bad.lean") "import Mathlib\n"
    writeFileCreatingParents (repoDir / "harness/.lake/build/Bad.lean") "import Mathlib\n"

    let repoOk ← checkTargetPath repoDir
    assertTrue "git_repo_clean_and_symlink_skipped"
      (repoOk.checked == 2 && repoOk.violations.isEmpty && repoOk.errors.isEmpty)
      s!"checked={repoOk.checked} viols={repoOk.violations} errs={repoOk.errors}"
    checks := checks + 1

    writeFileCreatingParents (repoDir / "LeanSwe/Fresh/Types.lean")
      "module\nimport all Batteries.Foo\ndef f := 1\n"
    writeFileCreatingParents (repoDir / "LeanSwe/Demo/Types.lean") "import Mathlib\ndef t := 1\n"
    runCmdOk repoDir "git" #["add", "-f", "LeanSwe/Fresh/Types.lean", "LeanSwe/Demo/Types.lean", ".lake/packages/bad/Bad.lean"]
    runCmdOk repoDir "git" #["-c", "commit.gpgsign=false", "commit", "-q", "-m", "bad imports and forced .lake"]

    let repoBad ← checkTargetPath repoDir
    assertTrue "git_repo_rejects_bad_and_forced_lake"
      (repoBad.checked == 4 &&
        repoBad.violations.any (containsSubstr · "LeanSwe/Demo/Types.lean:1:") &&
        repoBad.violations.any (containsSubstr · "LeanSwe/Fresh/Types.lean:2:") &&
        repoBad.violations.any (containsSubstr · ".lake/packages/bad/Bad.lean:1:"))
      s!"checked={repoBad.checked} viols={repoBad.violations}"
    checks := checks + 1
  finally
    removeDirForce tmpRoot

  IO.println s!"IMPORT_POLICY_SELFTEST: ok (checks={checks})"
  return 0

private def usageText : String :=
  "Usage: lean -DwarningAsError=true --run scripts/CheckImports.lean [--self-test | PATH...]"

/-- Check Lean 4 import hygiene using `Lean.Parser.parseHeader` across all `.lean` files. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--help"] | ["-h"] =>
    IO.println usageText
    return 0
  | ["--self-test"] =>
    try
      return ← runSelfTests
    catch e =>
      IO.eprintln s!"IMPORT_POLICY_SELFTEST: failed ({e})"
      return 1
  | _ =>
    for arg in args do
      if arg.startsWith "-" then
        IO.eprintln s!"IMPORT_POLICY_ERROR: unknown or misplaced flag '{arg}'"
        IO.eprintln usageText
        return 2
    let targets : List System.FilePath :=
      if args.isEmpty then ["."] else args.map System.FilePath.mk
    let mut totalChecked := 0
    let mut totalImports := 0
    let mut allViolations : Array String := #[]
    let mut allErrors : Array String := #[]
    for target in targets do
      let res ← checkTargetPath target
      totalChecked := totalChecked + res.checked
      totalImports := totalImports + res.imports
      allViolations := allViolations ++ res.violations
      allErrors := allErrors ++ res.errors
    if !allViolations.isEmpty then
      IO.eprintln s!"IMPORT_POLICY_CHECK: failed ({allViolations.size} violation(s) across {totalChecked} .lean file(s))"
      for v in allViolations do
        IO.eprintln s!"IMPORT_POLICY_VIOLATION: {v}"
    if !allErrors.isEmpty then
      for err in allErrors do
        IO.eprintln s!"IMPORT_POLICY_ERROR: {err}"
    if !allViolations.isEmpty || !allErrors.isEmpty then
      return 1
    IO.println s!"IMPORT_POLICY_CHECK: ok (checked={totalChecked} imports={totalImports} errors=0)"
    return 0
