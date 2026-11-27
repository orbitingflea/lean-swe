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
   (`Core`, `LeanSwe`, `Fuzz`, `ModelMutants`), including French-quoted single-segment names
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
  #["Core", "LeanSwe", "Fuzz", "ModelMutants", "UnitTests"]

private def forbiddenUmbrellaImports : Array String :=
  #["Mathlib"]

private def isInternalImportRoot (mod : Name) : Bool :=
  let root := mod.getRoot
  match root with
  | .str .anonymous rootSeg =>
    !rootSeg.contains '.' &&
    internalImportRoots.contains rootSeg &&
    (root == `Core || root == `LeanSwe || root == `Fuzz || root == `ModelMutants || root == `UnitTests)
  | _ => false

private def layer1AllowedRoots : Array String :=
  #["Init", "Std", "Lean", "Core", "LeanSwe"]

private def layer2RoleSegments : Array String :=
  #["Model", "Proofs", "Properties", "SpecTests", "SpecMutants", "Verified", "Aeneas"]

private def allRoleMarkerSegments : Array String :=
  #["Types", "Model", "Interface", "Impl", "SysBridge", "Proofs", "Properties",
    "SpecTests", "SpecMutants", "Verified", "Aeneas", "RuntimeTests", "TestSupport"]

private def modelForbiddenImpRoles : Array String :=
  #["Impl", "SysBridge", "Proofs", "SpecTests", "SpecMutants", "Verified", "Aeneas"]

private def proofsCrossForbiddenImpRoles : Array String :=
  #["Impl", "SysBridge", "Aeneas", "SpecTests", "SpecMutants", "Verified", "Proofs", "Properties"]

private def harnessAlwaysForbiddenSegments : Array String :=
  #["SpecTests", "SpecMutants", "Proofs", "Verified", "SysBridge"]

private partial def normalizeRelPath (relPath : String) : String :=
  if relPath.startsWith "./" then normalizeRelPath (relPath.drop 2).toString else relPath

private def normalizedModSegments (mod : Name) : List String :=
  mod.components.flatMap fun c =>
    match c with
    | .str _ s => s.splitOn "."
    | _ => [c.toString]

/-- Split a `LeanSwe.*` segment list into `(pkgSegments, effectiveRole, roleAndTailSegments)`
without hardcoding any `LeanSwe.<Pkg>` names. -/
private def classifyLeanSweSegments (segs : List String) : Option (List String × String × List String) :=
  match segs with
  | "LeanSwe" :: rest =>
    let rec findMarker (idx : Nat) (xs : List String) : Option (List String × List String) :=
      match xs with
      | [] => none
      | h :: t =>
        if idx >= 1 && allRoleMarkerSegments.contains h then
          some (rest.take idx, h :: t)
        else
          findMarker (idx + 1) t
    match findMarker 0 rest with
    | none => none
    | some (pkgTail, rem) =>
      let head := rem.headD ""
      let last := rem.getLastD ""
      let effRole :=
        if head == "Aeneas" then
          if last == "Types" || last == "TypesExternal" then "Types"
          else if rem.drop 1 |>.contains "Model" then "Model"
          else "Aeneas"
        else
          head
      some ("LeanSwe" :: pkgTail, effRole, rem)
  | _ => none

/-- Extract the owning fuzz suite leaf directory for `harness/Fuzz/<Leaf>/...`
(or `harness/Fuzz/LinuxSyscall/<Leaf>/...`), excluding `Common` and top-level files. -/
private def fuzzSuiteLeaf? (normPath : String) : Option String :=
  if !normPath.startsWith "harness/Fuzz/" then none
  else
    let rel := (normPath.drop 13).toString
    match rel.splitOn "/" with
    | "LinuxSyscall" :: leaf :: _ :: _ => some leaf
    | leaf :: _ :: _ =>
      if leaf == "Common" || leaf == "LinuxSyscall" then none else some leaf
    | _ => none

private def checkLayerImportPolicy (relPath policyPath : String) (lineNo : Nat) (mod : Name) : Option String :=
  let normPath := normalizeRelPath policyPath
  let modStr := mod.toString
  let segs := normalizedModSegments mod
  let rootSeg := segs.headD ""
  if normPath == "LeanSwe.lean" || normPath.startsWith "Core/" || normPath.startsWith "LeanSwe/" then
    if !layer1AllowedRoots.contains rootSeg then
      some s!"{relPath}:{lineNo}: Layer 1 forbids external/upper-layer import '{modStr}' (allowed roots: Init, Std, Lean, Core, LeanSwe)"
    else if rootSeg == "LeanSwe" && (segs.drop 1).any layer2RoleSegments.contains then
      some s!"{relPath}:{lineNo}: Layer 1 forbids importing Layer 2 module '{modStr}'"
    else
      none
  else if normPath.startsWith "proofs/LeanSwe/" && normPath.endsWith ".lean" then
    let stripped := (normPath.drop 7).toString
    let srcSegs := ((stripped.dropEnd 5).toString).splitOn "/"
    match classifyLeanSweSegments srcSegs, classifyLeanSweSegments segs with
    | some (srcPkg, srcRole, _), some (impPkg, impRole, impRem) =>
      if srcRole == "Model" then
        if modelForbiddenImpRoles.contains impRole then
          some s!"{relPath}:{lineNo}: Layer 2 Model file forbids importing '{modStr}' (role {impRole})"
        else if impPkg != srcPkg && impRem.head? == some "Aeneas" then
          some s!"{relPath}:{lineNo}: Layer 2 Model file forbids cross-package Aeneas import '{modStr}'"
        else
          none
      else if srcRole == "Proofs" || srcRole == "Properties" then
        if impPkg != srcPkg && (impRem.head? == some "Aeneas" || proofsCrossForbiddenImpRoles.contains impRole) then
          some s!"{relPath}:{lineNo}: Layer 2 {srcRole} file forbids cross-package direct import '{modStr}' (only Types/Model/Interface allowed)"
        else
          none
      else
        none
    | _, _ => none
  else if normPath.startsWith "harness/" && normPath != "harness/lakefile.lean" then
    if rootSeg == "LeanSweProofs" then
      some s!"{relPath}:{lineNo}: Layer 3 harness forbids importing umbrella '{modStr}'"
    else if rootSeg == "LeanSwe" then
      if (segs.drop 1).any harnessAlwaysForbiddenSegments.contains then
        some s!"{relPath}:{lineNo}: Layer 3 harness forbids importing '{modStr}' (SpecTests/SpecMutants/Proofs/Verified/SysBridge banned)"
      else if normPath == "harness/UnitTests.lean" || normPath.startsWith "harness/UnitTests/" ||
          normPath.startsWith "harness/ModelMutants/" then
        if (segs.drop 1).any (fun s => s == "Impl" || s == "Aeneas") then
          some s!"{relPath}:{lineNo}: Layer 3 ModelMutants/UnitTests forbids importing '{modStr}' (Impl/Aeneas banned)"
        else
          none
      else if normPath.startsWith "harness/Fuzz/" then
        let suiteLeaf := fuzzSuiteLeaf? normPath
        match classifyLeanSweSegments segs with
        | some (impPkg, _, impRem) =>
          let pkgLeaf := impPkg.getLastD ""
          if (segs.drop 1).contains "Impl" then
            -- Explicit minimal Fuzz mock rule: a fuzz suite may import only its own
            -- target package's top-level `Impl` module (no `Impl.*` submodules, no cross-suite `Impl`).
            if impRem == ["Impl"] && suiteLeaf == some pkgLeaf then
              none
            else
              some s!"{relPath}:{lineNo}: Layer 3 Fuzz forbids importing '{modStr}' (only matching suite's top-level <Pkg>.Impl is permitted)"
          else if (segs.drop 1).contains "Aeneas" then
            -- Explicit minimal Fuzz Aeneas differential-testing rule: a fuzz suite may import only
            -- its own target package's `Aeneas.Funs` or `Aeneas.Model`.
            if (impRem == ["Aeneas", "Funs"] || impRem == ["Aeneas", "Model"]) && suiteLeaf == some pkgLeaf then
              none
            else
              some s!"{relPath}:{lineNo}: Layer 3 Fuzz forbids importing '{modStr}' (only matching suite's Aeneas.Funs or Aeneas.Model is permitted)"
          else
            none
        | none =>
          if (segs.drop 1).any (fun s => s == "Impl" || s == "Aeneas") then
            some s!"{relPath}:{lineNo}: Layer 3 Fuzz forbids importing '{modStr}'"
          else
            none
      else
        none
    else
      none
  else
    none

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

/-- Return the 1-based line number of the first embedded NUL (`0x00`) byte in valid UTF-8
`rawSrc`, or `none`. Uses compiled `String.find?` rather than an interpreted `ByteArray` loop
so `--run` avoids multi-second byte-indexing overhead across the repository. -/
private def firstNulLine? (rawSrc : String) : Option Nat :=
  (rawSrc.find? "\x00").map fun p => ((FileMap.ofString rawSrc).toPosition p.offset).line

private def checkSourceWithBytes (relPath : String) (bytes : ByteArray) (rawSrc : String)
    (policyPath? : Option String := none) : IO (Nat × Array String) := do
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
  if let some nulLine := firstNulLine? rawSrc then
    violations := violations.push
      s!"{relPath}:{nulLine}: disallowed embedded NUL byte (0x00)"

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
        s!"{relPath}:{lineNo}: disallowed external 'import all {modStr}' (only intra-repo modules under Core/LeanSwe/Fuzz/ModelMutants/UnitTests may use 'import all')"
    if isForbiddenUmbrellaImport imp.module then
      violations := violations.push
        s!"{relPath}:{lineNo}: disallowed umbrella import '{modStr}' (import specific submodule(s) instead, e.g. 'Mathlib.Data.Nat.Basic')"
    if let some layerErr := checkLayerImportPolicy relPath (policyPath?.getD relPath) lineNo imp.module then
      violations := violations.push layerErr

  if let some err := checkPostHeaderLeadingImport relPath bytes bomBytes inputCtx.fileMap pst.pos then
    violations := violations.push err

  return (imps.size, violations)

private def checkSourceText (relPath : String) (rawSrc : String) : IO (Nat × Array String) :=
  checkSourceWithBytes relPath rawSrc.toUTF8 rawSrc

private def checkFileBytes (relPath : String) (bytes : ByteArray)
    (policyPath? : Option String := none) : IO (Nat × Array String) := do
  let some rawSrc := String.fromUTF8? bytes
    | return (0, #[s!"{relPath}:1: invalid UTF-8 encoding (cannot decode Lean source file)"])
  checkSourceWithBytes relPath bytes rawSrc policyPath?

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

private inductive ResolvedTargetType where
  | file
  | dir
  | other

private def resolveTopLevelTarget (target : System.FilePath) :
    IO (Except String (System.FilePath × ResolvedTargetType)) := do
  match ← isRegularFileSymlinkSafe target with
  | none =>
    return .error s!"target path not found or unreadable: {target}"
  | some .file =>
    return .ok (target, .file)
  | some .dir =>
    return .ok (target, .dir)
  | some .other =>
    return .ok (target, .other)
  | some .symlink =>
    let resolved ← try
      IO.FS.realPath target
    catch e =>
      return .error s!"failed to resolve target symlink '{target}': {e}"
    match ← isRegularFileSymlinkSafe resolved with
    | some .file => return .ok (resolved, .file)
    | some .dir => return .ok (resolved, .dir)
    | some .other => return .ok (resolved, .other)
    | some .symlink =>
      return .error s!"target symlink '{target}' did not resolve past symlink '{resolved}'"
    | none =>
      return .error s!"target symlink '{target}' resolves to missing or unreadable path '{resolved}'"

private partial def findEnclosingRepoRoot (dir : System.FilePath) : IO (Option System.FilePath) := do
  if (← (dir / ".git").pathExists) || (← (dir / "LeanSwe.lean").pathExists) then
    return some dir
  match dir.parent with
  | some p =>
    if p == dir then return none
    else findEnclosingRepoRoot p
  | none => return none

private def policyPathForFile (repoRoot? : Option System.FilePath)
    (fullPath : System.FilePath) (fallback : String) : String :=
  match repoRoot? with
  | some root =>
    let rootStr := root.toString
    let pfx := if rootStr.endsWith "/" then rootStr else rootStr ++ "/"
    let fullStr := fullPath.toString
    if fullStr.startsWith pfx then
      (fullStr.drop pfx.length).toString
    else
      fallback
  | none => fallback

private def checkTargetPath (target : System.FilePath) : IO CheckSummary := do
  let (resolvedTarget, targetType) ← match ← resolveTopLevelTarget target with
    | .ok resolved => pure resolved
    | .error err => return { errors := #[err] }
  let absTarget ← try IO.FS.realPath resolvedTarget catch _ => pure resolvedTarget
  match targetType with
  | .other =>
    return { errors := #[s!"target path is neither regular file nor directory: {target}"] }
  | .file =>
    let bytes ← try
      IO.FS.readBinFile resolvedTarget
    catch e =>
      return { errors := #[s!"failed to read '{target}': {e}"] }
    let repoRoot? ← findEnclosingRepoRoot (absTarget.parent.getD absTarget)
    let policyPath := policyPathForFile repoRoot? absTarget target.toString
    let (impCount, viols) ← checkFileBytes target.toString bytes (some policyPath)
    return { checked := 1, imports := impCount, violations := viols }
  | .dir =>
    let isGitRoot ← (absTarget / ".git").pathExists
    let repoRoot? ← if isGitRoot then pure (some absTarget) else findEnclosingRepoRoot absTarget
    let relPaths ← if isGitRoot then
      match ← gitListLeanFiles resolvedTarget with
      | .ok ps => pure ps
      | .error e => return { errors := #[e] }
    else
      match ← walkDirLeanFiles resolvedTarget with
      | .ok ps => pure ps
      | .error e => return { errors := #[e] }
    let mut checked := 0
    let mut totalImports := 0
    let mut violations : Array String := #[]
    let mut errors : Array String := #[]
    for relPath in relPaths do
      let fullPath := resolvedTarget / relPath
      let absFilePath := absTarget / relPath
      match ← isRegularFileSymlinkSafe fullPath with
      | some .file =>
        checked := checked + 1
        let bytes ← try
          IO.FS.readBinFile fullPath
        catch e =>
          errors := errors.push s!"failed to read '{relPath}': {e}"
          continue
        let policyPath := policyPathForFile repoRoot? absFilePath relPath
        let (impCount, viols) ← checkFileBytes relPath bytes (some policyPath)
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
    ("tests_retired", "module\nimport all Tests.Main\n", "Tests.Main"),
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
    ("overlong_nul", ByteArray.mk #[0xC0, 0x80]),
    ("nul_then_invalid_ff", ByteArray.mk #[0x00, 0xFF])
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
    (nulErrs.size == 1 && containsSubstr nulErrs[0]! "Nul.lean:1:" && containsSubstr nulErrs[0]! "NUL byte")
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
  assertTrue "nul_mid_import_rejected"
    (nulMidErrs.any (containsSubstr · "NUL byte") &&
      nulMidErrs.any (containsSubstr · "malformed module header"))
    s!"got {nulMidErrs}"
  checks := checks + 1

  let nulInComment := ByteArray.mk ("/- a".toUTF8.data ++ #[0x00] ++ "b -/\nimport Mathlib\n".toUTF8.data)
  let (_, nulCmtErrs) ← checkFileBytes "Nul4.lean" nulInComment
  assertTrue "nul_in_comment_catches_nul_and_import"
    (nulCmtErrs.size == 2 &&
      containsSubstr nulCmtErrs[0]! "Nul4.lean:1:" &&
      containsSubstr nulCmtErrs[0]! "NUL byte" &&
      containsSubstr nulCmtErrs[1]! "Nul4.lean:2:" &&
      containsSubstr nulCmtErrs[1]! "umbrella import 'Mathlib'")
    s!"got {nulCmtErrs}"
  checks := checks + 1

  let nulBodyCases : Array (String × String × ByteArray) := #[
    ("body", "NulBody.lean:3:",
      ByteArray.mk ("import Core.Types\ndef x := 1\n".toUTF8.data ++ #[0x00] ++ "\ndef y := 2\n".toUTF8.data)),
    ("block_comment_ok_import", "NulCmt.lean:1:",
      ByteArray.mk ("/- a".toUTF8.data ++ #[0x00] ++ "b -/\nimport Core.Types\n".toUTF8.data)),
    ("line_comment_ok_import", "NulLineCmt.lean:1:",
      ByteArray.mk ("-- a".toUTF8.data ++ #[0x00] ++ "b\nimport Core.Types\n".toUTF8.data)),
    ("string_literal", "NulStr.lean:2:",
      ByteArray.mk ("import Core.Types\ndef s : String := \"".toUTF8.data ++ #[0x00] ++ "\"\n".toUTF8.data)),
    ("trailing_eof", "NulEof.lean:2:",
      ByteArray.mk ("import Core.Types\n".toUTF8.data ++ #[0x00])),
    ("quoted_ident", "NulIdent.lean:1:",
      ByteArray.mk ("import «foo".toUTF8.data ++ #[0x00] ++ "bar»\n".toUTF8.data)),
    ("only_nul", "NulOnly.lean:1:",
      ByteArray.mk #[0x00])
  ]
  for (label, expectedLoc, bs) in nulBodyCases do
    let fileName := (expectedLoc.splitOn ":").head!
    let (_, errs) ← checkFileBytes fileName bs
    assertTrue s!"nul_embedded:{label}"
      (errs.size == 1 && containsSubstr errs[0]! expectedLoc && containsSubstr errs[0]! "NUL byte")
      s!"got {errs}"
    checks := checks + 1

  let nulAfterBomAndBad := ByteArray.mk
    (#[0xEF, 0xBB, 0xBF] ++ "import Mathlib\ndef x := 1\n".toUTF8.data ++ #[0x00] ++ "\n".toUTF8.data)
  let (_, nulBomErrs) ← checkFileBytes "NulBom.lean" nulAfterBomAndBad
  assertTrue "nul_after_bom_and_bad_import"
    (nulBomErrs.size == 3 &&
      containsSubstr nulBomErrs[0]! "NulBom.lean:1:" && containsSubstr nulBomErrs[0]! "UTF-8 BOM" &&
      containsSubstr nulBomErrs[1]! "NulBom.lean:3:" && containsSubstr nulBomErrs[1]! "NUL byte" &&
      containsSubstr nulBomErrs[2]! "NulBom.lean:1:" && containsSubstr nulBomErrs[2]! "umbrella import 'Mathlib'")
    s!"got {nulBomErrs}"
  checks := checks + 1

  let (_, nulSrcErrs) ← checkSourceText "NulSrc.lean" "import Core.Types\ndef x := 1\n\x00\ndef y := 2\n"
  assertTrue "nul_in_body_via_source_text"
    (nulSrcErrs.size == 1 && containsSubstr nulSrcErrs[0]! "NulSrc.lean:3:" && containsSubstr nulSrcErrs[0]! "NUL byte")
    s!"got {nulSrcErrs}"
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
    "import all LeanSwe",
    "import all Core",
    "import all Fuzz",
    "import all «LeanSwe»",
    "private def hidden : Nat := 1",
    "public def shown : Nat := 2"
  ]
  let (modCount, modErrs) ← checkSourceText "Ok.lean" allowedModule
  assertTrue "allowed_module" (modErrs.isEmpty && modCount == 30)
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
    writeFileCreatingParents (walkDir / "proofs/LeanSwe/Demo/Proofs.lean")
      "module\nimport Mathlib.Data.Nat.Basic\nimport all LeanSwe.Demo.Impl\n"
    writeFileCreatingParents (walkDir / ".lake/packages/bad/Bad.lean") "import Mathlib\n"
    writeFileCreatingParents (walkDir / "harness/.lake/build/Bad.lean") "import Mathlib\n"
    writeFileCreatingParents (walkDir / ".lint-cache/Bad.lean") "import Mathlib\n"
    writeFileCreatingParents (walkDir / ".agents/Bad.lean") "import Mathlib\n"
    writeFileCreatingParents (walkDir / "LeanSwe/PostFork/rust/target/Bad.lean") "import Mathlib\n"
    runCmdOk tmpRoot "ln" #["-s", (outsideDir / "BadOutside.lean").toString, (walkDir / "Link.lean").toString]
    runCmdOk tmpRoot "ln" #["-s", outsideDir.toString, (walkDir / "LinkDir").toString]
    runCmdOk tmpRoot "ln" #["-s", ".", (walkDir / "SelfLoop").toString]
    runCmdOk tmpRoot "ln" #["-s", (tmpRoot / "missing-inside.lean").toString, (walkDir / "BrokenInside.lean").toString]

    let plainOk ← checkTargetPath walkDir
    assertTrue "walk_skips_build_dirs_and_symlinks"
      (plainOk.checked == 2 && plainOk.violations.isEmpty && plainOk.errors.isEmpty)
      s!"checked={plainOk.checked} viols={plainOk.violations} errs={plainOk.errors}"
    checks := checks + 1

    let plainLink := tmpRoot / "plain-link"
    let plainLinkChain := tmpRoot / "plain-link-chain"
    let plainRelLink := tmpRoot / "plain-rel-link"
    runCmdOk tmpRoot "ln" #["-s", walkDir.toString, plainLink.toString]
    runCmdOk tmpRoot "ln" #["-s", plainLink.toString, plainLinkChain.toString]
    runCmdOk tmpRoot "ln" #["-s", "plain", plainRelLink.toString]

    let plainLinkOk ← checkTargetPath plainLink
    assertTrue "top_level_dir_symlink_clean_and_skips_internal_symlinks"
      (plainLinkOk.checked == 2 && plainLinkOk.violations.isEmpty && plainLinkOk.errors.isEmpty)
      s!"checked={plainLinkOk.checked} viols={plainLinkOk.violations} errs={plainLinkOk.errors}"
    checks := checks + 1

    let plainChainOk ← checkTargetPath plainLinkChain
    assertTrue "top_level_dir_symlink_chain_clean"
      (plainChainOk.checked == 2 && plainChainOk.violations.isEmpty && plainChainOk.errors.isEmpty)
      s!"checked={plainChainOk.checked} viols={plainChainOk.violations} errs={plainChainOk.errors}"
    checks := checks + 1

    let plainRelOk ← checkTargetPath plainRelLink
    assertTrue "top_level_dir_relative_symlink_clean"
      (plainRelOk.checked == 2 && plainRelOk.violations.isEmpty && plainRelOk.errors.isEmpty)
      s!"checked={plainRelOk.checked} viols={plainRelOk.violations} errs={plainRelOk.errors}"
    checks := checks + 1

    writeFileCreatingParents (walkDir / "proofs/LeanSwe/Demo/Bad.lean") "import Mathlib\n"
    writeBinCreatingParents (walkDir / "LeanSwe/Demo/BadUtf8.lean") (ByteArray.mk #[0xFF, 0xFE])
    writeBinCreatingParents (walkDir / "LeanSwe/Demo/Bom.lean")
      (ByteArray.mk (#[0xEF, 0xBB, 0xBF] ++ "import Core.Types\n".toUTF8.data))
    writeBinCreatingParents (walkDir / "LeanSwe/Demo/NulBody.lean")
      (ByteArray.mk ("import Core.Types\ndef x := 1\n".toUTF8.data ++ #[0x00] ++ "\ndef y := 2\n".toUTF8.data))
    let plainBad ← checkTargetPath walkDir
    assertTrue "walk_catches_bad_utf8_bom_and_nul"
      (plainBad.checked == 6 &&
        plainBad.violations.size == 4 &&
        plainBad.violations.any (containsSubstr · "proofs/LeanSwe/Demo/Bad.lean:1:") &&
        plainBad.violations.any (containsSubstr · "LeanSwe/Demo/BadUtf8.lean:1:") &&
        plainBad.violations.any (containsSubstr · "LeanSwe/Demo/Bom.lean:1:") &&
        plainBad.violations.any (fun v => containsSubstr v "LeanSwe/Demo/NulBody.lean:3:" && containsSubstr v "NUL byte"))
      s!"checked={plainBad.checked} viols={plainBad.violations}"
    checks := checks + 1

    let plainLinkBad ← checkTargetPath plainLink
    assertTrue "top_level_dir_symlink_catches_violations"
      (plainLinkBad.checked == 6 &&
        plainLinkBad.errors.isEmpty &&
        plainLinkBad.violations.size == 4 &&
        plainLinkBad.violations.any (containsSubstr · "proofs/LeanSwe/Demo/Bad.lean:1:") &&
        plainLinkBad.violations.any (containsSubstr · "LeanSwe/Demo/NulBody.lean:3:"))
      s!"checked={plainLinkBad.checked} viols={plainLinkBad.violations} errs={plainLinkBad.errors}"
    checks := checks + 1

    let singleOk ← checkTargetPath (walkDir / "Core/Types.lean")
    assertTrue "single_file_ok"
      (singleOk.checked == 1 && singleOk.violations.isEmpty && singleOk.errors.isEmpty)
      s!"checked={singleOk.checked} viols={singleOk.violations}"
    checks := checks + 1

    let singleFileLinkOk := tmpRoot / "ok-file-link.lean"
    let singleFileLinkRel := tmpRoot / "ok-file-rel.lean"
    let singleFileLinkBad := tmpRoot / "bad-file-link.lean"
    let singleFileLinkBadChain := tmpRoot / "bad-file-chain.lean"
    runCmdOk tmpRoot "ln" #["-s", (walkDir / "Core/Types.lean").toString, singleFileLinkOk.toString]
    runCmdOk tmpRoot "ln" #["-s", "plain/Core/Types.lean", singleFileLinkRel.toString]
    runCmdOk tmpRoot "ln" #["-s", (outsideDir / "BadOutside.lean").toString, singleFileLinkBad.toString]
    runCmdOk tmpRoot "ln" #["-s", singleFileLinkBad.toString, singleFileLinkBadChain.toString]

    let symOkRes ← checkTargetPath singleFileLinkOk
    assertTrue "top_level_file_symlink_ok"
      (symOkRes.checked == 1 && symOkRes.violations.isEmpty && symOkRes.errors.isEmpty)
      s!"checked={symOkRes.checked} viols={symOkRes.violations} errs={symOkRes.errors}"
    checks := checks + 1

    let symRelOkRes ← checkTargetPath singleFileLinkRel
    assertTrue "top_level_file_relative_symlink_ok"
      (symRelOkRes.checked == 1 && symRelOkRes.violations.isEmpty && symRelOkRes.errors.isEmpty)
      s!"checked={symRelOkRes.checked} viols={symRelOkRes.violations} errs={symRelOkRes.errors}"
    checks := checks + 1

    let symBadRes ← checkTargetPath singleFileLinkBad
    assertTrue "top_level_file_symlink_violation"
      (symBadRes.checked == 1 &&
        symBadRes.errors.isEmpty &&
        symBadRes.violations.size == 1 &&
        containsSubstr symBadRes.violations[0]! s!"{singleFileLinkBad}:1:" &&
        containsSubstr symBadRes.violations[0]! "umbrella import 'Mathlib'")
      s!"checked={symBadRes.checked} viols={symBadRes.violations} errs={symBadRes.errors}"
    checks := checks + 1

    let symBadChainRes ← checkTargetPath singleFileLinkBadChain
    assertTrue "top_level_file_symlink_chain_violation"
      (symBadChainRes.checked == 1 &&
        symBadChainRes.errors.isEmpty &&
        symBadChainRes.violations.size == 1 &&
        containsSubstr symBadChainRes.violations[0]! "umbrella import 'Mathlib'")
      s!"checked={symBadChainRes.checked} viols={symBadChainRes.violations} errs={symBadChainRes.errors}"
    checks := checks + 1

    let brokenLink := tmpRoot / "broken-link.lean"
    runCmdOk tmpRoot "ln" #["-s", (tmpRoot / "does-not-exist.lean").toString, brokenLink.toString]
    let brokenRes ← checkTargetPath brokenLink
    assertTrue "top_level_broken_symlink_errors"
      (brokenRes.checked == 0 &&
        !brokenRes.errors.isEmpty &&
        containsSubstr brokenRes.errors[0]! brokenLink.toString)
      s!"checked={brokenRes.checked} errs={brokenRes.errors}"
    checks := checks + 1

    let brokenDirLink := tmpRoot / "broken-dir-link"
    runCmdOk tmpRoot "ln" #["-s", (tmpRoot / "does-not-exist-dir").toString, brokenDirLink.toString]
    let brokenDirRes ← checkTargetPath brokenDirLink
    assertTrue "top_level_broken_dir_symlink_errors"
      (brokenDirRes.checked == 0 && !brokenDirRes.errors.isEmpty)
      s!"checked={brokenDirRes.checked} errs={brokenDirRes.errors}"
    checks := checks + 1

    let loopLink := tmpRoot / "loop-link"
    runCmdOk tmpRoot "ln" #["-s", "loop-link", loopLink.toString]
    let loopRes ← checkTargetPath loopLink
    assertTrue "top_level_cyclic_symlink_errors"
      (loopRes.checked == 0 && !loopRes.errors.isEmpty)
      s!"checked={loopRes.checked} errs={loopRes.errors}"
    checks := checks + 1

    if ← (⟨"/dev/null"⟩ : System.FilePath).pathExists then
      let devNullLink := tmpRoot / "devnull-link"
      runCmdOk tmpRoot "ln" #["-s", "/dev/null", devNullLink.toString]
      let devNullRes ← checkTargetPath devNullLink
      assertTrue "top_level_non_regular_symlink_errors"
        (devNullRes.checked == 0 && !devNullRes.errors.isEmpty)
        s!"checked={devNullRes.checked} errs={devNullRes.errors}"
      checks := checks + 1

    let missingRes ← checkTargetPath (tmpRoot / "nonexistent.lean")
    assertTrue "missing_target_errors" (!missingRes.errors.isEmpty) s!"errs={missingRes.errors}"
    checks := checks + 1

    let repoDir := tmpRoot / "repo"
    IO.FS.createDirAll repoDir
    runCmdOk repoDir "git" #["init", "-q"]
    writeFileCreatingParents (repoDir / "LeanSwe/Demo/Impl.lean") "import Core.Types\ndef x := 1\n"
    writeFileCreatingParents (repoDir / "LeanSwe/Demo/Types.lean") "def t := 1\n"
    writeFileCreatingParents (repoDir / "proofs/LeanSwe/Demo/Proofs.lean")
      "module\nimport Mathlib.Data.Nat.Basic\nimport all LeanSwe.Demo.Impl\n"
    runCmdOk repoDir "ln" #["-s", "Types.lean", (repoDir / "LeanSwe/Demo/Link.lean").toString]
    runCmdOk repoDir "git" #["add", "."]
    runCmdOk repoDir "git" #["-c", "commit.gpgsign=false", "commit", "-q", "-m", "base"]
    runCmdOk repoDir "git" #["rm", "-q", "LeanSwe/Demo/Impl.lean"]
    runCmdOk repoDir "git" #["-c", "commit.gpgsign=false", "commit", "-q", "-m", "remove impl"]

    writeFileCreatingParents (repoDir / ".lake/packages/bad/Bad.lean") "import Mathlib\n"
    writeFileCreatingParents (repoDir / "harness/.lake/build/Bad.lean") "import Mathlib\n"
    runCmdOk repoDir "ln" #["-s", (outsideDir / "BadOutside.lean").toString, (repoDir / "LeanSwe/Demo/UntrackedLink.lean").toString]

    let repoOk ← checkTargetPath repoDir
    assertTrue "git_repo_clean_and_symlink_skipped"
      (repoOk.checked == 2 && repoOk.violations.isEmpty && repoOk.errors.isEmpty)
      s!"checked={repoOk.checked} viols={repoOk.violations} errs={repoOk.errors}"
    checks := checks + 1

    let repoLink := tmpRoot / "repo-link"
    runCmdOk tmpRoot "ln" #["-s", repoDir.toString, repoLink.toString]
    let repoLinkOk ← checkTargetPath repoLink
    assertTrue "top_level_git_repo_symlink_clean"
      (repoLinkOk.checked == 2 && repoLinkOk.violations.isEmpty && repoLinkOk.errors.isEmpty)
      s!"checked={repoLinkOk.checked} viols={repoLinkOk.violations} errs={repoLinkOk.errors}"
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

    let repoLinkBad ← checkTargetPath repoLink
    assertTrue "top_level_git_repo_symlink_catches_violations"
      (repoLinkBad.checked == 4 &&
        repoLinkBad.errors.isEmpty &&
        repoLinkBad.violations.any (containsSubstr · "LeanSwe/Demo/Types.lean:1:") &&
        repoLinkBad.violations.any (containsSubstr · "LeanSwe/Fresh/Types.lean:2:") &&
        repoLinkBad.violations.any (containsSubstr · ".lake/packages/bad/Bad.lean:1:"))
      s!"checked={repoLinkBad.checked} viols={repoLinkBad.violations} errs={repoLinkBad.errors}"
    checks := checks + 1
  finally
    removeDirForce tmpRoot

  let layerAllowedCases : Array (String × String × String) := #[
    ("l1_init_float_model", "LeanSwe/Demo/Impl.lean", "import Init.Data.Float.Model\nimport Std.Data.HashMap\nimport Core.ConcOps\nimport LeanSwe.Demo.Types\n"),
    ("l1_core_imports_core", "Core/ConcOps.lean", "import Core.Obeys\n"),
    ("l1_umbrella_types", "LeanSwe.lean", "import Core.Obeys\nimport LeanSwe.Demo.Interface\n"),
    ("l2_model_imports_types_and_dep_model", "proofs/LeanSwe/Demo/Model.lean", "import LeanSwe.Demo.Types\nimport LeanSwe.Other.Types\nimport LeanSwe.Other.Model\n"),
    ("l2_aeneas_model_imports_aeneas_types", "proofs/LeanSwe/Demo/Aeneas/Model/World.lean", "import LeanSwe.Demo.Aeneas.Types\n"),
    ("l2_proofs_same_pkg_impl_and_cross_iface", "proofs/LeanSwe/Demo/Proofs.lean", "import LeanSwe.Demo.Impl\nimport LeanSwe.Demo.SysBridge\nimport LeanSwe.Other.Types\nimport LeanSwe.Other.Model\nimport LeanSwe.Other.Interface\n"),
    ("l2_nested_pkg_same_raw_impl", "proofs/LeanSwe/Demo/Raw/Proofs.lean", "import LeanSwe.Demo.Raw.Impl\nimport LeanSwe.Demo.Raw.Model\n"),
    ("l3_unit_tests_import_all", "harness/UnitTests/Sample.lean", "module\nimport all UnitTests\nimport LeanSwe.Demo.Types\nimport LeanSwe.Demo.Model\nimport LeanSwe.Demo.Interface\n"),
    ("l3_model_mutants_iface_model", "harness/ModelMutants/Demo.lean", "import Core.Obeys\nimport LeanSwe.Demo.Model\nimport LeanSwe.Demo.Interface\n"),
    ("l3_fuzz_matching_suite_top_impl", "harness/Fuzz/Demo/Suite.lean", "import LeanSwe.Demo.Impl\nimport LeanSwe.Demo.Interface\nimport LeanSwe.Demo.Model\n"),
    ("l3_fuzz_matching_linuxsyscall_impl", "harness/Fuzz/LinuxSyscall/Demo/Strace.lean", "import LeanSwe.LinuxSyscall.Demo.Impl\n"),
    ("l3_fuzz_matching_aeneas_funs_model", "harness/Fuzz/Demo/Suite.lean", "import LeanSwe.Demo.Aeneas.Funs\nimport LeanSwe.Demo.Aeneas.Model\n")
  ]
  for (label, path, src) in layerAllowedCases do
    let (_, errs) ← checkSourceText path src
    assertTrue s!"layer_ok:{label}" errs.isEmpty s!"got {errs}"
    checks := checks + 1

  let layerRejectedCases : Array (String × String × String × String) := #[
    ("l1_imports_model", "LeanSwe/Demo/Impl.lean", "import LeanSwe.Demo.Model\n", "Layer 1 forbids importing Layer 2"),
    ("l1_imports_proofs", "LeanSwe/Demo/Interface.lean", "import LeanSwe.Demo.Proofs\n", "Layer 1 forbids importing Layer 2"),
    ("l1_imports_properties", "LeanSwe/Demo/Types.lean", "import LeanSwe.Demo.Properties\n", "Layer 1 forbids importing Layer 2"),
    ("l1_imports_spectests", "LeanSwe/Demo/Impl.lean", "import LeanSwe.Demo.SpecTests\n", "Layer 1 forbids importing Layer 2"),
    ("l1_imports_specmutants", "LeanSwe/Demo/Impl.lean", "import LeanSwe.Demo.SpecMutants\n", "Layer 1 forbids importing Layer 2"),
    ("l1_imports_verified", "LeanSwe/Demo/Impl.lean", "import LeanSwe.Demo.Verified\n", "Layer 1 forbids importing Layer 2"),
    ("l1_imports_aeneas_sub", "LeanSwe/Demo/Impl.lean", "import LeanSwe.Demo.Aeneas.Funs\n", "Layer 1 forbids importing Layer 2"),
    ("l1_imports_ext_aeneas", "LeanSwe/Demo/Impl.lean", "import Aeneas\n", "Layer 1 forbids external/upper-layer import"),
    ("l1_imports_ext_mathlib", "Core/ConcOps.lean", "import Mathlib.Data.Nat.Basic\n", "Layer 1 forbids external/upper-layer import"),
    ("l1_umbrella_model", "LeanSwe.lean", "import LeanSwe.Demo.Model\n", "Layer 1 forbids importing Layer 2"),
    ("l1_quoted_spoof_model", "LeanSwe/Demo/Impl.lean", "import «LeanSwe.Demo.Model»\n", "Layer 1 forbids importing Layer 2"),
    ("l2_model_imports_impl", "proofs/LeanSwe/Demo/Model.lean", "import LeanSwe.Demo.Impl\n", "Layer 2 Model file forbids importing"),
    ("l2_model_imports_sysbridge", "proofs/LeanSwe/Demo/Model/Sub.lean", "import LeanSwe.Demo.SysBridge\n", "Layer 2 Model file forbids importing"),
    ("l2_model_imports_proofs", "proofs/LeanSwe/Demo/Model.lean", "import LeanSwe.Demo.Proofs\n", "Layer 2 Model file forbids importing"),
    ("l2_model_imports_spectests", "proofs/LeanSwe/Demo/Model.lean", "import LeanSwe.Demo.SpecTests\n", "Layer 2 Model file forbids importing"),
    ("l2_model_imports_specmutants", "proofs/LeanSwe/Demo/Model.lean", "import LeanSwe.Demo.SpecMutants\n", "Layer 2 Model file forbids importing"),
    ("l2_model_imports_verified", "proofs/LeanSwe/Demo/Model.lean", "import LeanSwe.Demo.Verified\n", "Layer 2 Model file forbids importing"),
    ("l2_model_imports_aeneas_funs", "proofs/LeanSwe/Demo/Model.lean", "import LeanSwe.Demo.Aeneas.Funs\n", "Layer 2 Model file forbids importing"),
    ("l2_proofs_cross_impl", "proofs/LeanSwe/Demo/Proofs.lean", "import LeanSwe.Other.Impl\n", "Layer 2 Proofs file forbids cross-package"),
    ("l2_proofs_cross_sysbridge", "proofs/LeanSwe/Demo/Proofs/Sub.lean", "import LeanSwe.Other.SysBridge\n", "Layer 2 Proofs file forbids cross-package"),
    ("l2_proofs_cross_aeneas", "proofs/LeanSwe/Demo/Proofs.lean", "import LeanSwe.Other.Aeneas.Types\n", "Layer 2 Proofs file forbids cross-package"),
    ("l2_proofs_cross_spectests", "proofs/LeanSwe/Demo/Proofs.lean", "import LeanSwe.Other.SpecTests\n", "Layer 2 Proofs file forbids cross-package"),
    ("l2_proofs_cross_specmutants", "proofs/LeanSwe/Demo/Proofs.lean", "import LeanSwe.Other.SpecMutants\n", "Layer 2 Proofs file forbids cross-package"),
    ("l2_proofs_cross_verified", "proofs/LeanSwe/Demo/Proofs.lean", "import LeanSwe.Other.Verified\n", "Layer 2 Proofs file forbids cross-package"),
    ("l2_proofs_cross_proofs", "proofs/LeanSwe/Demo/Proofs.lean", "import LeanSwe.Other.Proofs\n", "Layer 2 Proofs file forbids cross-package"),
    ("l2_properties_cross_properties", "proofs/LeanSwe/Demo/Properties.lean", "import LeanSwe.Other.Properties\n", "Layer 2 Properties file forbids cross-package"),
    ("l2_parent_vs_raw_cross_impl", "proofs/LeanSwe/Demo/Proofs.lean", "import LeanSwe.Demo.Raw.Impl\n", "Layer 2 Proofs file forbids cross-package"),
    ("l3_fuzz_spectests", "harness/Fuzz/Demo/Suite.lean", "import LeanSwe.Demo.SpecTests\n", "Layer 3 harness forbids importing"),
    ("l3_fuzz_specmutants", "harness/Fuzz/Demo/Suite.lean", "import LeanSwe.Demo.SpecMutants\n", "Layer 3 harness forbids importing"),
    ("l3_fuzz_proofs", "harness/Fuzz/Demo/Suite.lean", "import LeanSwe.Demo.Proofs\n", "Layer 3 harness forbids importing"),
    ("l3_fuzz_verified", "harness/Fuzz/Demo/Suite.lean", "import LeanSwe.Demo.Verified\n", "Layer 3 harness forbids importing"),
    ("l3_fuzz_sysbridge", "harness/Fuzz/Demo/Suite.lean", "import LeanSwe.Demo.SysBridge\n", "Layer 3 harness forbids importing"),
    ("l3_fuzz_umbrella_proofs", "harness/Fuzz/Demo/Suite.lean", "import LeanSweProofs\n", "Layer 3 harness forbids importing umbrella"),
    ("l3_fuzz_cross_suite_impl", "harness/Fuzz/Demo/Suite.lean", "import LeanSwe.Other.Impl\n", "Layer 3 Fuzz forbids importing"),
    ("l3_fuzz_impl_submodule", "harness/Fuzz/Demo/Suite.lean", "import LeanSwe.Demo.Impl.Sub\n", "Layer 3 Fuzz forbids importing"),
    ("l3_fuzz_common_impl", "harness/Fuzz/Common/Helper.lean", "import LeanSwe.Demo.Impl\n", "Layer 3 Fuzz forbids importing"),
    ("l3_fuzz_aeneas_api", "harness/Fuzz/Demo/Suite.lean", "import LeanSwe.Demo.Aeneas.Api\n", "Layer 3 Fuzz forbids importing"),
    ("l3_fuzz_cross_aeneas", "harness/Fuzz/Demo/Suite.lean", "import LeanSwe.Other.Aeneas.Funs\n", "Layer 3 Fuzz forbids importing"),
    ("l3_model_mutants_impl", "harness/ModelMutants/Demo.lean", "import LeanSwe.Demo.Impl\n", "Layer 3 ModelMutants/UnitTests forbids importing"),
    ("l3_unit_tests_impl", "harness/UnitTests/Demo.lean", "import LeanSwe.Demo.Impl\n", "Layer 3 ModelMutants/UnitTests forbids importing"),
    ("l3_unit_tests_aeneas", "harness/UnitTests/Demo.lean", "import LeanSwe.Demo.Aeneas.Model\n", "Layer 3 ModelMutants/UnitTests forbids importing")
  ]
  for (label, path, src, needle) in layerRejectedCases do
    let (_, errs) ← checkSourceText path src
    assertTrue s!"layer_reject:{label}"
      (!errs.isEmpty && errs.any (containsSubstr · needle))
      s!"got {errs}"
    checks := checks + 1

  let mkOut ← IO.Process.output { cmd := "mktemp", args := #["-d", "/tmp/leanswe-checkimports-layer.XXXXXX"] }
  assertTrue "mktemp_layer_subdir" (mkOut.exitCode == 0) mkOut.stderr
  let layerSubdirRepo : System.FilePath := mkOut.stdout.trimAscii.toString
  try
    runCmdOk layerSubdirRepo "git" #["init", "-q"]
    writeFileCreatingParents (layerSubdirRepo / "LeanSwe.lean") "import LeanSwe.Demo.Types\n"
    writeFileCreatingParents (layerSubdirRepo / "LeanSwe/Demo/Types.lean") "def t : Nat := 0\n"
    writeFileCreatingParents (layerSubdirRepo / "LeanSwe/Demo/Impl.lean") "import LeanSwe.Demo.Model\n"
    writeFileCreatingParents (layerSubdirRepo / "proofs/LeanSwe/Demo/Model.lean") "import LeanSwe.Demo.Types\n"
    writeFileCreatingParents (layerSubdirRepo / "proofs/LeanSwe/Demo/Proofs.lean") "import LeanSwe.Demo.Model\n"
    writeFileCreatingParents (layerSubdirRepo / "harness/UnitTests/Demo.lean") "import LeanSwe.Demo.Impl\n"

    let proofsSubRes ← checkTargetPath (layerSubdirRepo / "proofs")
    assertTrue "subdir_target_proofs_clean"
      (proofsSubRes.checked == 2 && proofsSubRes.violations.isEmpty && proofsSubRes.errors.isEmpty)
      s!"got checked={proofsSubRes.checked} viols={proofsSubRes.violations} errs={proofsSubRes.errors}"
    checks := checks + 1

    let harnessSubRes ← checkTargetPath (layerSubdirRepo / "harness")
    assertTrue "subdir_target_harness_enforced"
      (harnessSubRes.violations.any (containsSubstr · "Layer 3 ModelMutants/UnitTests forbids importing"))
      s!"got {harnessSubRes.violations}"
    checks := checks + 1

    let l1SubRes ← checkTargetPath (layerSubdirRepo / "LeanSwe/Demo")
    assertTrue "subdir_target_l1_enforced"
      (l1SubRes.violations.any (containsSubstr · "Layer 1 forbids importing Layer 2"))
      s!"got {l1SubRes.violations}"
    checks := checks + 1

    let absL1FileRes ← checkTargetPath (layerSubdirRepo / "LeanSwe/Demo/Impl.lean")
    assertTrue "abs_file_target_l1_enforced"
      (absL1FileRes.violations.any (containsSubstr · "Layer 1 forbids importing Layer 2"))
      s!"got {absL1FileRes.violations}"
    checks := checks + 1

    let absL2FileRes ← checkTargetPath (layerSubdirRepo / "proofs/LeanSwe/Demo/Proofs.lean")
    assertTrue "abs_file_target_l2_clean"
      (absL2FileRes.checked == 1 && absL2FileRes.violations.isEmpty && absL2FileRes.errors.isEmpty)
      s!"got {absL2FileRes.violations} / {absL2FileRes.errors}"
    checks := checks + 1
  finally
    removeDirForce layerSubdirRepo

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
