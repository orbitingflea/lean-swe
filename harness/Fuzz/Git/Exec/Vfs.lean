import Fuzz.Git.Exec.Core

namespace Fuzz.Git

open Fuzz.Common
open LeanSwe.Git
open LeanSwe.Git.Model

/-- Helper `hasNulByte`. -/
def hasNulByte (bs : ByteArray) : Bool :=
  bs.data.any (· == 0)

/-- Helper `isSafeRelBytes`. -/
def isSafeRelBytes (bs : ByteArray) : Bool :=
  if bs.isEmpty || hasNulByte bs then false
  else
    let parts := splitByteSlash bs
    !parts.isEmpty && !parts.any (fun seg =>
      seg == ".".toUTF8 || seg == "..".toUTF8 || seg == ".git".toUTF8)

/-- Helper `isLiveSlotDir`. -/
def isLiveSlotDir (st : EpisodeState) (slot : SlotId) : Bool :=
  let slotParts := splitByteSlash s!"{st.rootDir}/{slot.relPath}".toUTF8
  match resolveVfsFuel 41 st.model.vfs [] slotParts true with
  | .ok (.dir _ true true _) => true
  | _ => false

/-- Helper `isLiveSearchableDir`. -/
def isLiveSearchableDir (vfs : VfsNode) (parts : List ByteArray) : Bool :=
  match resolveVfsFuel 41 vfs [] parts true with
  | .ok (.dir _ true _ _) => true
  | _ => false

/-- Helper `bumpSlotRegularFileMtimes`. -/
def bumpSlotRegularFileMtimes (slotPath : String) : IO Unit := do
  let py :=
    "import os, stat, sys\n" ++
    "base = sys.argv[1].encode('utf-8')\n" ++
    "for cur, dirs, files in os.walk(base):\n" ++
    "    dirs[:] = [d for d in dirs if d != b'.git']\n" ++
    "    for fn in files:\n" ++
    "        if fn == b'.git':\n" ++
    "            continue\n" ++
    "        fp = os.path.join(cur, fn)\n" ++
    "        try:\n" ++
    "            st = os.lstat(fp)\n" ++
    "            if stat.S_ISREG(st.st_mode):\n" ++
    "                os.utime(fp, ns=(st.st_atime_ns, st.st_mtime_ns + 2000000000))\n" ++
    "        except OSError:\n" ++
    "            pass\n"
  let _ ← runPythonFs py #[slotPath]

/-- Helper `execVfsWriteFile`. -/
def execVfsWriteFile (st : EpisodeState) (slot : SlotId) (relBytes content : ByteArray)
    (executable : Bool) : IO (EpisodeState × Bool) := do
  if !isSafeRelBytes relBytes || !isLiveSlotDir st slot then
    return (st, false)
  let slotPath := s!"{st.rootDir}/{slot.relPath}"
  let slotParts := splitByteSlash slotPath.toUTF8
  let canonSlotParts :=
    match resolveVfsFuel 41 st.model.vfs [] slotParts true with
    | .ok (.dir cp _ _ _) => cp
    | _ => []
  if canonSlotParts.isEmpty then
    return (st, false)
  let relParts := splitByteSlash relBytes
  match relParts.reverse with
  | [] => return (st, false)
  | leaf :: revDirs =>
    let dirParts := revDirs.reverse
    match mkdirPVfsFuel 41 st.model.vfs canonSlotParts dirParts with
    | .error _ => return (st, false)
    | .ok (vAfterDirs, parentParts) =>
      match lookupNodeAtParts vAfterDirs (parentParts ++ [leaf]) with
      | some (.dir _ _ _) | some (.symlink _) => return (st, false)
      | _ =>
        match String.fromUTF8? relBytes with
        | some relStr =>
          let fullPath := s!"{slotPath}/{relStr}"
          let parentDirStr :=
            if dirParts.isEmpty then slotPath
            else s!"{slotPath}/{"/".intercalate (dirParts.map fun b => (String.fromUTF8? b).getD "")}"
          match ← LeanSwe.Fs.mkdir parentDirStr true true with
          | .error _ => return (st, false)
          | .ok () =>
            match ← LeanSwe.Fs.writeBytes fullPath content with
            | .error _ => return (st, false)
            | .ok () =>
              let mode := if executable then 0o755 else 0o644
              match ← LeanSwe.Fs.chmod fullPath mode with
              | .error _ => return (st, false)
              | .ok () =>
                if leaf == ".gitattributes".toUTF8 then
                  bumpSlotRegularFileMtimes slotPath
                let vFinal := vfsPutChild vAfterDirs parentParts leaf (.file executable content)
                return ({ st with model := { st.model with vfs := vFinal } }, true)
        | none =>
          let py :=
            "import os, sys\n" ++
            "base = sys.argv[1].encode('utf-8')\n" ++
            "rel = bytes.fromhex(sys.argv[2])\n" ++
            "body = bytes.fromhex(sys.argv[3])\n" ++
            "mode = int(sys.argv[4], 8)\n" ++
            "full = os.path.join(base, rel)\n" ++
            "os.makedirs(os.path.dirname(full), exist_ok=True)\n" ++
            "with open(full, 'wb') as f:\n" ++
            "    f.write(body)\n" ++
            "os.chmod(full, mode)\n"
          let modeStr := if executable then "755" else "644"
          match ← runPythonFs py #[slotPath, byteArrayToHex relBytes, byteArrayToHex content, modeStr] with
          | .error _ => return (st, false)
          | .ok () =>
            if leaf == ".gitattributes".toUTF8 then
              bumpSlotRegularFileMtimes slotPath
            let vFinal := vfsPutChild vAfterDirs parentParts leaf (.file executable content)
            return ({ st with model := { st.model with vfs := vFinal }, hasNonUtf8OnDisk := true }, true)

/-- Helper `execVfsMkdir`. -/
def execVfsMkdir (st : EpisodeState) (slot : SlotId) (relBytes : ByteArray) : IO (EpisodeState × Bool) := do
  if !isSafeRelBytes relBytes || !isLiveSlotDir st slot then
    return (st, false)
  let slotPath := s!"{st.rootDir}/{slot.relPath}"
  let slotParts := splitByteSlash slotPath.toUTF8
  match resolveVfsFuel 41 st.model.vfs [] slotParts true with
  | .ok (.dir canonSlotParts _ _ _) =>
    match mkdirPVfsFuel 41 st.model.vfs canonSlotParts (splitByteSlash relBytes) with
    | .error _ => return (st, false)
    | .ok (v', _) =>
      match String.fromUTF8? relBytes with
      | some relStr =>
        match ← LeanSwe.Fs.mkdir s!"{slotPath}/{relStr}" true true with
        | .error _ => return (st, false)
        | .ok () => return ({ st with model := { st.model with vfs := v' } }, true)
      | none =>
        let py :=
          "import os, sys\n" ++
          "base = sys.argv[1].encode('utf-8')\n" ++
          "rel = bytes.fromhex(sys.argv[2])\n" ++
          "os.makedirs(os.path.join(base, rel), exist_ok=True)\n"
        match ← runPythonFs py #[slotPath, byteArrayToHex relBytes] with
        | .error _ => return (st, false)
        | .ok () => return ({ st with model := { st.model with vfs := v' }, hasNonUtf8OnDisk := true }, true)
  | _ => return (st, false)

/-- Helper `execVfsSymlink`. -/
def execVfsSymlink (st : EpisodeState) (slot : SlotId) (relBytes targetBytes : ByteArray) :
    IO (EpisodeState × Bool) := do
  if !isSafeRelBytes relBytes || hasNulByte targetBytes || targetBytes.isEmpty || !isLiveSlotDir st slot then
    return (st, false)
  let slotPath := s!"{st.rootDir}/{slot.relPath}"
  let slotParts := splitByteSlash slotPath.toUTF8
  match resolveVfsFuel 41 st.model.vfs [] slotParts true with
  | .ok (.dir canonSlotParts _ _ _) =>
    match (splitByteSlash relBytes).reverse with
    | [] => return (st, false)
    | leaf :: revDirs =>
      let dirParts := revDirs.reverse
      match mkdirPVfsFuel 41 st.model.vfs canonSlotParts dirParts with
      | .error _ => return (st, false)
      | .ok (vAfterDirs, parentParts) =>
        match lookupNodeAtParts vAfterDirs (parentParts ++ [leaf]) with
        | some _ => return (st, false)
        | none =>
          match String.fromUTF8? relBytes, String.fromUTF8? targetBytes with
          | some relStr, some targetStr =>
            let parentDirStr :=
              if dirParts.isEmpty then slotPath
              else s!"{slotPath}/{"/".intercalate (dirParts.map fun b => (String.fromUTF8? b).getD "")}"
            match ← LeanSwe.Fs.mkdir parentDirStr true true with
            | .error _ => return (st, false)
            | .ok () =>
              match ← LeanSwe.Fs.symlink targetStr s!"{slotPath}/{relStr}" with
              | .error _ => return (st, false)
              | .ok () =>
                let vFinal := vfsPutChild vAfterDirs parentParts leaf (.symlink targetBytes)
                return ({ st with model := { st.model with vfs := vFinal } }, true)
          | _, _ =>
            let py :=
              "import os, sys\n" ++
              "base = sys.argv[1].encode('utf-8')\n" ++
              "rel = bytes.fromhex(sys.argv[2])\n" ++
              "tgt = bytes.fromhex(sys.argv[3])\n" ++
              "full = os.path.join(base, rel)\n" ++
              "os.makedirs(os.path.dirname(full), exist_ok=True)\n" ++
              "if os.path.lexists(full):\n" ++
              "    sys.exit(1)\n" ++
              "os.symlink(tgt, full)\n"
            match ← runPythonFs py #[slotPath, byteArrayToHex relBytes, byteArrayToHex targetBytes] with
            | .error _ => return (st, false)
            | .ok () =>
              let vFinal := vfsPutChild vAfterDirs parentParts leaf (.symlink targetBytes)
              return ({ st with model := { st.model with vfs := vFinal }, hasNonUtf8OnDisk := true }, true)
  | _ => return (st, false)

/-- Helper `execVfsRemoveFile`. -/
def execVfsRemoveFile (st : EpisodeState) (slot : SlotId) (relBytes : ByteArray) : IO (EpisodeState × Bool) := do
  if !isSafeRelBytes relBytes then
    return (st, false)
  let slotPath := s!"{st.rootDir}/{slot.relPath}"
  let slotParts := splitByteSlash slotPath.toUTF8
  match resolveVfsFuel 41 st.model.vfs [] slotParts true with
  | .ok (.dir canonSlotParts true true _) =>
    match (splitByteSlash relBytes).reverse with
    | [] => return (st, false)
    | leaf :: revDirs =>
      let parentParts := canonSlotParts ++ revDirs.reverse
      match lookupNodeAtParts st.model.vfs (parentParts ++ [leaf]) with
      | some (.file _ _) | some (.symlink _) =>
        match String.fromUTF8? relBytes with
        | some relStr =>
          match ← LeanSwe.Fs.unlink s!"{slotPath}/{relStr}" false with
          | .error _ => return (st, false)
          | .ok () =>
            if leaf == ".gitattributes".toUTF8 then
              bumpSlotRegularFileMtimes slotPath
            let v' := vfsDropChild st.model.vfs parentParts leaf
            return ({ st with model := { st.model with vfs := v' } }, true)
        | none =>
          let py :=
            "import os, sys\n" ++
            "os.unlink(os.path.join(sys.argv[1].encode('utf-8'), bytes.fromhex(sys.argv[2])))\n"
          match ← runPythonFs py #[slotPath, byteArrayToHex relBytes] with
          | .error _ => return (st, false)
          | .ok () =>
            if leaf == ".gitattributes".toUTF8 then
              bumpSlotRegularFileMtimes slotPath
            let v' := vfsDropChild st.model.vfs parentParts leaf
            return ({ st with model := { st.model with vfs := v' } }, true)
      | _ => return (st, false)
  | _ => return (st, false)

/-- Helper `execVfsRemoveDir`. -/
def execVfsRemoveDir (st : EpisodeState) (slot : SlotId) (relBytes : ByteArray) : IO (EpisodeState × Bool) := do
  if !isSafeRelBytes relBytes then
    return (st, false)
  let slotPath := s!"{st.rootDir}/{slot.relPath}"
  let slotParts := splitByteSlash slotPath.toUTF8
  match resolveVfsFuel 41 st.model.vfs [] slotParts true with
  | .ok (.dir canonSlotParts true true _) =>
    match (splitByteSlash relBytes).reverse with
    | [] => return (st, false)
    | leaf :: revDirs =>
      let parentParts := canonSlotParts ++ revDirs.reverse
      match lookupNodeAtParts st.model.vfs (parentParts ++ [leaf]) with
      | some (.dir _ _ []) =>
        match String.fromUTF8? relBytes with
        | some relStr =>
          match ← LeanSwe.Fs.rmdir s!"{slotPath}/{relStr}" with
          | .error _ => return (st, false)
          | .ok () =>
            let v' := vfsDropChild st.model.vfs parentParts leaf
            return ({ st with model := { st.model with vfs := v' } }, true)
        | none =>
          let py :=
            "import os, sys\n" ++
            "os.rmdir(os.path.join(sys.argv[1].encode('utf-8'), bytes.fromhex(sys.argv[2])))\n"
          match ← runPythonFs py #[slotPath, byteArrayToHex relBytes] with
          | .error _ => return (st, false)
          | .ok () =>
            let v' := vfsDropChild st.model.vfs parentParts leaf
            return ({ st with model := { st.model with vfs := v' } }, true)
      | _ => return (st, false)
  | _ => return (st, false)

/-- Helper `execVfsRemoveTree`. -/
def execVfsRemoveTree (st : EpisodeState) (slot : SlotId) : IO (EpisodeState × Bool) := do
  if slot != .wt1 && slot != .wt2 && slot != .bareWt then
    return (st, false)
  let slotPath := s!"{st.rootDir}/{slot.relPath}"
  let slotParts := splitByteSlash slotPath.toUTF8
  match lookupNodeAtParts st.model.vfs slotParts with
  | some (.dir _ _ _) =>
    let py :=
      "import os, shutil, sys\n" ++
      "p = sys.argv[1].encode('utf-8')\n" ++
      "if not os.path.isdir(p) or os.path.islink(p):\n" ++
      "    sys.exit(1)\n" ++
      "os.chmod(p, 0o755)\n" ++
      "for cur, dirs, _ in os.walk(p):\n" ++
      "    for d in dirs:\n" ++
      "        dp = os.path.join(cur, d)\n" ++
      "        if not os.path.islink(dp):\n" ++
      "            try:\n" ++
      "                os.chmod(dp, 0o755)\n" ++
      "            except OSError:\n" ++
      "                pass\n" ++
      "shutil.rmtree(p)\n"
    match ← runPythonFs py #[slotPath] with
    | .error _ => return (st, false)
    | .ok () =>
      let rootParts := splitByteSlash st.rootDir.toUTF8
      let v' := vfsDropChild st.model.vfs rootParts slot.relPath.toUTF8
      return ({ st with model := { st.model with vfs := v' } }, true)
  | _ => return (st, false)

/-- Helper `execVfsChmodDir`. -/
def execVfsChmodDir (st : EpisodeState) (slot : SlotId) (searchable : Bool) : IO (EpisodeState × Bool) := do
  if slot != .repoB && slot != .subDir && slot != .wt2 then
    return (st, false)
  let dirPath := s!"{st.rootDir}/{slot.relPath}"
  let parts := splitByteSlash dirPath.toUTF8
  match lookupNodeAtParts st.model.vfs parts with
  | some (.dir _ _ cs) =>
    let mode := if searchable then 0o755 else 0o000
    match ← LeanSwe.Fs.chmod dirPath mode with
    | .error _ => return (st, false)
    | .ok () =>
      let v' := updateNodeAtParts st.model.vfs parts fun _ => .dir searchable searchable cs
      let dirs :=
        if searchable || st.chmodDirs.contains dirPath then st.chmodDirs
        else st.chmodDirs.push dirPath
      return ({ st with model := { st.model with vfs := v' }, chmodDirs := dirs }, true)
  | _ => return (st, false)

/-- Helper `execVfsChmodSubDir`. -/
def execVfsChmodSubDir (st : EpisodeState) (slot : SlotId) (relBytes : ByteArray)
    (searchable : Bool) : IO (EpisodeState × Bool) := do
  if !isSafeRelBytes relBytes then
    return (st, false)
  if slot != .repoA && slot != .repoB && slot != .wt1 && slot != .wt2 && slot != .bareWt && slot != .cloneRepo then
    return (st, false)
  let slotPath := s!"{st.rootDir}/{slot.relPath}"
  let slotParts := splitByteSlash slotPath.toUTF8
  match resolveVfsFuel 41 st.model.vfs [] slotParts true with
  | .ok (.dir canonSlotParts true _ _) =>
    let relParts := splitByteSlash relBytes
    let fullParts := canonSlotParts ++ relParts
    match lookupNodeAtParts st.model.vfs fullParts with
    | some (.dir _ _ cs) =>
      let mode := if searchable then 0o755 else 0o000
      match String.fromUTF8? relBytes with
      | some relStr =>
        let fullPath := s!"{slotPath}/{relStr}"
        match ← LeanSwe.Fs.chmod fullPath mode with
        | .error _ => return (st, false)
        | .ok () =>
          let v' := updateNodeAtParts st.model.vfs fullParts fun _ => .dir searchable searchable cs
          let dirs :=
            if searchable || st.chmodDirs.contains fullPath then st.chmodDirs
            else st.chmodDirs.push fullPath
          return ({ st with model := { st.model with vfs := v' }, chmodDirs := dirs }, true)
      | none =>
        let rawFull := (slotPath ++ "/").toUTF8 ++ relBytes
        let py :=
          "import os, sys\n" ++
          "os.chmod(bytes.fromhex(sys.argv[1]), int(sys.argv[2], 8))\n"
        match ← runPythonFs py #[byteArrayToHex rawFull, if searchable then "755" else "000"] with
        | .error _ => return (st, false)
        | .ok () =>
          let v' := updateNodeAtParts st.model.vfs fullParts fun _ => .dir searchable searchable cs
          let rDirs :=
            if searchable || st.chmodRawDirs.contains rawFull then st.chmodRawDirs
            else st.chmodRawDirs.push rawFull
          return ({ st with model := { st.model with vfs := v' }, chmodRawDirs := rDirs }, true)
    | _ => return (st, false)
  | _ => return (st, false)

/-- Helper `execVfsSetFileExecutable`. -/
def execVfsSetFileExecutable (st : EpisodeState) (slot : SlotId) (relBytes : ByteArray)
    (executable : Bool) : IO (EpisodeState × Bool) := do
  if !isSafeRelBytes relBytes then
    return (st, false)
  if slot != .repoA && slot != .repoB && slot != .wt1 && slot != .wt2 && slot != .bareWt && slot != .cloneRepo then
    return (st, false)
  let slotPath := s!"{st.rootDir}/{slot.relPath}"
  let slotParts := splitByteSlash slotPath.toUTF8
  match resolveVfsFuel 41 st.model.vfs [] slotParts true with
  | .ok (.dir canonSlotParts true true _) =>
    let relParts := splitByteSlash relBytes
    if relParts.head? == some ".git".toUTF8 then
      return (st, false)
    let fullParts := canonSlotParts ++ relParts
    match lookupNodeAtParts st.model.vfs fullParts with
    | some (.file _ bytes) =>
      let mode := if executable then 0o755 else 0o644
      match String.fromUTF8? relBytes with
      | some relStr =>
        let fullPath := s!"{slotPath}/{relStr}"
        match ← LeanSwe.Fs.chmod fullPath mode with
        | .error _ => return (st, false)
        | .ok () =>
          let v' := updateNodeAtParts st.model.vfs fullParts fun _ => .file executable bytes
          return ({ st with model := { st.model with vfs := v' } }, true)
      | none =>
        let rawFull := (slotPath ++ "/").toUTF8 ++ relBytes
        let py :=
          "import os, sys\n" ++
          "os.chmod(bytes.fromhex(sys.argv[1]), int(sys.argv[2], 8))\n"
        match ← runPythonFs py #[byteArrayToHex rawFull, if executable then "755" else "644"] with
        | .error _ => return (st, false)
        | .ok () =>
          let v' := updateNodeAtParts st.model.vfs fullParts fun _ => .file executable bytes
          return ({ st with model := { st.model with vfs := v' } }, true)
    | _ => return (st, false)
  | _ => return (st, false)

/-- Helper `execGitRawLockWorktree`. -/
def execGitRawLockWorktree (st : EpisodeState) (repoSlot wtSlot : SlotId) (lock : Bool)
    (reason? : Option String) : IO (EpisodeState × Bool) := do
  let repoPath := s!"{st.rootDir}/{repoSlot.relPath}"
  let wtPath := s!"{st.rootDir}/{wtSlot.relPath}"
  let args :=
    if lock then
      match reason? with
      | some r =>
        if r.isEmpty then #["worktree", "lock", "--", wtPath]
        else #["worktree", "lock", "--reason", r, "--", wtPath]
      | none => #["worktree", "lock", "--", wtPath]
    else
      #["worktree", "unlock", "--", wtPath]
  let rawOps := scopedRawOps st.rootDir st.cwdDir false
  let envPairs ← rawOps.listEnv
  let overrides :=
    match envPairs with
    | .ok e => cleanGitEnv e
    | .error _ => cleanGitEnv #[]
  match ← rawOps.execGit overrides { cwd := some repoPath, args := args } with
  | .error _ => return (st, false)
  | .ok out =>
    if out.exitCode != 0 then
      return (st, false)
    let wtCanon := wtPath.toUTF8
    let repos' := st.model.repos.map fun repo =>
      { repo with
        worktrees := repo.worktrees.map fun slot =>
          if slot.rootPath == wtCanon then
            let rsn? :=
              if lock then
                reason?.bind fun s =>
                  let trimmed := Impl.trimAsciiWhitespace s
                  if trimmed.isEmpty then none else some trimmed
              else none
            { slot with isLocked := lock, lockReason := rsn? }
          else slot }
    return ({ st with model := { st.model with repos := repos' } }, true)

/-- Helper `execGitRawCreateTag`. -/
def execGitRawCreateTag (st : EpisodeState) (repoSlot : SlotId) (tagName : RefName)
    (targetRev : FuzzRevSpec) : IO (EpisodeState × Bool) := do
  if !isValidRefNameStr tagName.raw then
    return (st, false)
  let repoPath := s!"{st.rootDir}/{repoSlot.relPath}"
  let revStr := resolveRevSpec st targetRev
  match resolveCwdAndDiscover st.model repoPath with
  | .error _ => return (st, false)
  | .ok (repo, _, _, _) =>
    let fullRef := "refs/tags/" ++ tagName.raw
    if hasRefDFConflict repo fullRef then
      return (st, false)
    match (stepRevParseCommit st.model repoPath revStr).1 with
    | .error _ => return (st, false)
    | .ok cid =>
      let rawOps := scopedRawOps st.rootDir st.cwdDir false
      let envPairs ← rawOps.listEnv
      let overrides := match envPairs with | .ok e => cleanGitEnv e | .error _ => cleanGitEnv #[]
      match ← rawOps.execGit overrides { cwd := some repoPath, args := #["update-ref", fullRef, cid.hex] } with
      | .error _ => return (st, false)
      | .ok out =>
        if out.exitCode != 0 then
          return (st, false)
        let repos' := st.model.repos.map fun r =>
          if r.commonDir != repo.commonDir then r
          else { r with refs := setRefInList r.refs fullRef cid }
        return ({ st with model := { st.model with repos := repos' } }, true)

/-- Helper `addKnownCommit`. -/
def addKnownCommit (st : EpisodeState) (cid : CommitId) : EpisodeState :=
  if st.knownCommits.contains cid then st else { st with knownCommits := st.knownCommits.push cid }

/-- Helper `writeFileBoth`. -/
def writeFileBoth (st : EpisodeState) (repoSlot : SlotId) (relName : String) (content : ByteArray) :
    IO (Except String EpisodeState) := do
  let (st', ok) ← execVfsWriteFile st repoSlot relName.toUTF8 content false
  if ok then return .ok st'
  else return .error s!"writeFileBoth failed on {relName}"


end Fuzz.Git
