import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Fs.Interface
import LeanSwe.Process.Interface
import LeanSwe.TempDir.Interface
import Fuzz.Common.Coverage
import Fuzz.Common.Shrink
import Fuzz.Git.Gen

namespace Fuzz.Git

open Fuzz.Common
open LeanSwe.Git
open LeanSwe.Git.Model

/-- Structured failure result separating real semantic mismatches from infrastructure errors. -/
inductive TraceError where
  /-- Differential discrepancy between real `git` and `GitRepoState`, tagged for shrink stability. -/
  | mismatch (tag : String) (msg : String)
  /-- Harness or OS infrastructure failure (never shrunk as a semantic bug). -/
  | infra (msg : String)
  deriving Repr, BEq

/-- Execution state maintained alongside `GitRepoState` during one fuzzing episode. -/
structure EpisodeState where
  /-- Canonical real path of the temporary episode directory root. -/
  rootDir : String
  /-- Canonical empty non-repository working directory scoped inside `rootDir` (`rootDir/sandbox/cwd`). -/
  cwdDir : String
  /-- Pure reference model state mirroring the episode directory and repositories. -/
  model : GitRepoState
  /-- Commit IDs observed from real `git` during the episode for DAG queries. -/
  knownCommits : Array CommitId := #[]
  /-- Directories whose permissions were changed (`chmod 0000`) and must be restored before cleanup. -/
  chmodDirs : Array String := #[]
  /-- Non-UTF-8 directories whose permissions were changed (`chmod 0000`) stored as raw bytes. -/
  chmodRawDirs : Array ByteArray := #[]
  /-- Regular files whose permissions were changed (`chmod 0000`) and must be restored before cleanup. -/
  chmodFiles : Array String := #[]
  /-- Non-UTF-8 regular files whose permissions were changed (`chmod 0000`) stored as raw bytes. -/
  chmodRawFiles : Array ByteArray := #[]
  /-- Whether non-UTF-8 paths or symlinks were created on disk inside `rootDir`. -/
  hasNonUtf8OnDisk : Bool := false
  /-- Whether the `badUtf8Dir` fixture has been lazily created in this episode. -/
  hasBadUtf8Fixture : Bool := false
  /-- Whether this episode has introduced a quote/newline path or lock reason that can perturb English `git` stderr text. -/
  hasSpoofablePath : Bool := false

private def stripTrailingSlash (p : String) : String :=
  if p.length > 1 && p.endsWith "/" then p.dropEnd 1 |>.toString else p

private def poisonEnvPairs : Array (String × String) := #[
  ("GIT_DIR", "/nonexistent/gitdir"),
  ("GIT_WORK_TREE", "/nonexistent/worktree"),
  ("GIT_INDEX_FILE", "/nonexistent/index"),
  ("GIT_COMMON_DIR", "/nonexistent/commondir"),
  ("GIT_OBJECT_DIRECTORY", "/nonexistent/objects"),
  ("GIT_ALTERNATE_OBJECT_DIRECTORIES", "/nonexistent/alt_objects"),
  ("GIT_CONFIG_GLOBAL", "/nonexistent/gitconfig"),
  ("GIT_CONFIG_NOSYSTEM", "0"),
  ("GIT_CONFIG_PARAMETERS", "'core.bare=true' 'status.showUntrackedFiles=no'"),
  ("GIT_CONFIG_COUNT", "1"),
  ("LC_ALL", "fr_FR.UTF-8"),
  ("LANG", "fr_FR.UTF-8"),
  ("LANGUAGE", "fr_FR:fr")
]

private def scopedRawOps (rootDir cwdDir : String) (poison : Bool) : RawGitOps :=
  let fuzzHome := s!"{rootDir}/_fuzz_home"
  let fuzzXdg := s!"{rootDir}/_fuzz_xdg"
  let extraPoison := poisonEnvPairs
  { listEnv := do
      match ← defaultRawOps.listEnv with
      | .error e => return .error e
      | .ok env =>
        let cleanHost := env.filter fun (k, _) => k != "HOME" && k != "XDG_CONFIG_HOME"
        let base := cleanHost ++ #[("HOME", fuzzHome), ("XDG_CONFIG_HOME", fuzzXdg)]
        if poison then return .ok (base ++ extraPoison)
        else return .ok base
    execGit := fun envOverrides req => do
      let effectiveCwd :=
        match req.cwd with
        | none => some cwdDir
        | some d =>
          if d.isEmpty || d.startsWith "/" || d.toList.contains '\x00' then some d
          else some s!"{cwdDir}/{d}"
      let baseEnv := #[("HOME", some fuzzHome), ("XDG_CONFIG_HOME", some fuzzXdg)]
      let effectiveEnv :=
        baseEnv ++
        (if poison then extraPoison.map fun (k, v) => (k, some v) else #[]) ++
        envOverrides
      defaultRawOps.execGit effectiveEnv { req with cwd := effectiveCwd } }

private def hangGitRawOps (rootDir cwdDir : String) (ms : Nat) : RawGitOps :=
  let base := scopedRawOps rootDir cwdDir false
  { listEnv := base.listEnv
    execGit := fun envOverrides req =>
      base.execGit envOverrides
        { req with
          args := #["-c", "alias.fuzzhang=!sleep 5", "fuzzhang"]
          timeoutMs := some ms } }

private def pickApi (st : EpisodeState) (poison : Bool) : GitApi :=
  Impl.mkApiM (scopedRawOps st.rootDir st.cwdDir poison)

private def resolveTarget (root : String) : PathTarget → String
  | .slot s => s!"{root}/{s.relPath}"
  | .raw p => p
  | .subRel parent rel => s!"{root}/{parent.relPath}/{rel}"
  | .fileUrl s => s!"file://{root}/{s.relPath}"
  | .fileUrlLocalhost s => s!"file://localhost{root}/{s.relPath}"

private def resolveRevSpec (st : EpisodeState) : FuzzRevSpec → String
  | .raw s => s
  | .commitIdx idx fallback =>
    if st.knownCommits.isEmpty then fallback
    else st.knownCommits[idx % st.knownCommits.size]!.hex
  | .shortCommitIdx idx len fallback =>
    if st.knownCommits.isEmpty then fallback
    else
      let full := st.knownCommits[idx % st.knownCommits.size]!.hex
      let takeLen := max 7 (min 12 len)
      String.ofList (full.toList.take takeLen)

private def resolveCommitIdx (st : EpisodeState) (idx : Nat) (raw? : Option String) : CommitId :=
  match raw? with
  | some hex =>
    match mkCommitId hex with
    | .ok cid => cid
    | .error _ => { hex := String.ofList (List.replicate 40 '0') }
  | none =>
    if st.knownCommits.isEmpty then
      { hex := String.ofList (List.replicate 40 '0') }
    else
      st.knownCommits[idx % st.knownCommits.size]!

private def resolveCheckoutTarget (st : EpisodeState) : FuzzCheckoutTarget → CheckoutTarget
  | .branch b => .branch b
  | .commitIdx idx raw? => .commit (resolveCommitIdx st idx raw?)
  | .ref spec => .ref (resolveRevSpec st spec)

private def upsertChildInListAux (seg : ByteArray) (node : VfsNode)
    (revAcc : List (ByteArray × VfsNode)) :
    List (ByteArray × VfsNode) → List (ByteArray × VfsNode)
  | [] => ((seg, node) :: revAcc).reverse
  | (k, v) :: rest =>
    if k == seg then revAcc.reverse ++ ((seg, node) :: rest)
    else upsertChildInListAux seg node ((k, v) :: revAcc) rest

private def upsertChildInList (seg : ByteArray) (node : VfsNode)
    (xs : List (ByteArray × VfsNode)) : List (ByteArray × VfsNode) :=
  upsertChildInListAux seg node [] xs

private def eraseChildInListAux (seg : ByteArray) (revAcc : List (ByteArray × VfsNode)) :
    List (ByteArray × VfsNode) → List (ByteArray × VfsNode)
  | [] => revAcc.reverse
  | (k, v) :: rest =>
    if k == seg then eraseChildInListAux seg revAcc rest
    else eraseChildInListAux seg ((k, v) :: revAcc) rest

private def eraseChildInList (seg : ByteArray) (xs : List (ByteArray × VfsNode)) :
    List (ByteArray × VfsNode) :=
  eraseChildInListAux seg [] xs

private def vfsPutChild (vfs : VfsNode) (parentParts : List ByteArray) (seg : ByteArray) (child : VfsNode) :
    VfsNode :=
  updateNodeAtParts vfs parentParts fun
    | .dir s w cs => .dir s w (upsertChildInList seg child cs)
    | other => other

private def vfsDropChild (vfs : VfsNode) (parentParts : List ByteArray) (seg : ByteArray) : VfsNode :=
  updateNodeAtParts vfs parentParts fun
    | .dir s w cs => .dir s w (eraseChildInList seg cs)
    | other => other

private def byteArrayToHex (bs : ByteArray) : String := Id.run do
  let hexDigits : Array Char := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  let mut out := ""
  for i in List.range bs.size do
    let b := bs[i]!.toNat
    out := out.push hexDigits[b / 16]! |>.push hexDigits[b % 16]!
  return out

private def runPythonFs (script : String) (args : Array String) : IO (Except String Unit) := do
  let res ← LeanSwe.Process.run { program := "python3", args := #["-c", script] ++ args }
  match res with
  | .error e => return .error e.message
  | .ok out =>
    if out.exitCode == 0 then return .ok ()
    else return .error ((String.fromUTF8? out.stderr).getD s!"python exited {out.exitCode}")

private def hasBadUtf8Target : PathTarget → Bool
  | .slot .badUtf8Dir => true
  | .subRel .badUtf8Dir _ => true
  | .fileUrl .badUtf8Dir => true
  | .fileUrlLocalhost .badUtf8Dir => true
  | _ => false

mutual
private def stepMentionsBadUtf8 : GitFuzzStep → Bool
  | .vfsWriteFile s _ _ _ => s == .badUtf8Dir
  | .vfsMkdir s _ => s == .badUtf8Dir
  | .vfsSymlink s _ _ => s == .badUtf8Dir
  | .vfsRemoveFile s _ => s == .badUtf8Dir
  | .vfsRemoveDir s _ => s == .badUtf8Dir
  | .vfsRemoveTree s => s == .badUtf8Dir
  | .vfsChmodDir s _ => s == .badUtf8Dir
  | .vfsChmodSubDir s _ _ => s == .badUtf8Dir
  | .vfsSetFileExecutable s _ _ => s == .badUtf8Dir
  | .gitRawLockWorktree r w _ _ => r == .badUtf8Dir || w == .badUtf8Dir
  | .gitRawCreateTag r _ _ => r == .badUtf8Dir
  | .gitRawCreateMergeConflict r _ _ _ _ => r == .badUtf8Dir
  | .gitRawCreateCrissCrossMerge r => r == .badUtf8Dir
  | .opIsRepo t _ => hasBadUtf8Target t
  | .opRepoRoot t _ => hasBadUtf8Target t
  | .opCommonDir t _ => hasBadUtf8Target t
  | .opHeadCommit t _ => hasBadUtf8Target t
  | .opHeadBranch t _ => hasBadUtf8Target t
  | .opHeadState t _ => hasBadUtf8Target t
  | .opRevParseCommit t _ _ => hasBadUtf8Target t
  | .opIsAncestor t _ _ _ _ _ => hasBadUtf8Target t
  | .opMergeBase t _ _ _ _ _ => hasBadUtf8Target t
  | .opStatus t _ => hasBadUtf8Target t
  | .opDiffNameStatus t _ _ _ _ => hasBadUtf8Target t
  | .opListWorktrees t _ => hasBadUtf8Target t
  | .opShowFile t _ _ _ => hasBadUtf8Target t
  | .opInit t _ _ _ => hasBadUtf8Target t
  | .opClone s t _ _ => hasBadUtf8Target s || hasBadUtf8Target t
  | .opAdd t _ _ _ => hasBadUtf8Target t
  | .opCommit t _ _ => hasBadUtf8Target t
  | .opCreateBranch t _ _ _ _ => hasBadUtf8Target t
  | .opDeleteBranch t _ _ _ => hasBadUtf8Target t
  | .opCheckout t _ _ _ => hasBadUtf8Target t
  | .opSwitch t _ _ _ _ _ => hasBadUtf8Target t
  | .opReset t _ _ _ => hasBadUtf8Target t
  | .opFetch t _ _ _ _ => hasBadUtf8Target t
  | .opWorktreeAdd t wt _ _ _ _ _ => hasBadUtf8Target t || hasBadUtf8Target wt
  | .opWorktreeRemove t wt _ _ => hasBadUtf8Target t || hasBadUtf8Target wt
  | .opWithWorktree t wt _ _ _ _ ins _ _ =>
    hasBadUtf8Target t || hasBadUtf8Target wt || stepsMentionBadUtf8 ins
  | .opTimeoutProbe t _ => hasBadUtf8Target t

private def stepsMentionBadUtf8 : List GitFuzzStep → Bool
  | [] => false
  | s :: rest => stepMentionsBadUtf8 s || stepsMentionBadUtf8 rest
end

mutual
private def stepMayCreateNonUtf8 : GitFuzzStep → Bool
  | .vfsWriteFile s rel _ _ => s == .badUtf8Dir || (String.fromUTF8? rel).isNone
  | .vfsMkdir s rel => s == .badUtf8Dir || (String.fromUTF8? rel).isNone
  | .vfsSymlink s rel tgt =>
    s == .badUtf8Dir || (String.fromUTF8? rel).isNone || (String.fromUTF8? tgt).isNone
  | .vfsRemoveFile s rel => s == .badUtf8Dir || (String.fromUTF8? rel).isNone
  | .vfsRemoveDir s rel => s == .badUtf8Dir || (String.fromUTF8? rel).isNone
  | .vfsChmodSubDir s rel _ => s == .badUtf8Dir || (String.fromUTF8? rel).isNone
  | .vfsSetFileExecutable s rel _ => s == .badUtf8Dir || (String.fromUTF8? rel).isNone
  | .opWithWorktree t wt _ _ _ _ ins _ _ =>
    hasBadUtf8Target t || hasBadUtf8Target wt || stepsMayCreateNonUtf8 ins
  | other => stepMentionsBadUtf8 other

private def stepsMayCreateNonUtf8 : List GitFuzzStep → Bool
  | [] => false
  | s :: rest => stepMayCreateNonUtf8 s || stepsMayCreateNonUtf8 rest
end

mutual
private def stepMayChmod : GitFuzzStep → Bool
  | .vfsChmodDir _ false => true
  | .vfsChmodSubDir _ _ false => true
  | .opWithWorktree _ _ _ _ _ _ ins _ _ => stepsMayChmod ins
  | _ => false

private def stepsMayChmod : List GitFuzzStep → Bool
  | [] => false
  | s :: rest => stepMayChmod s || stepsMayChmod rest
end

private def ensureBadUtf8Fixture (st : EpisodeState) : IO (Except String EpisodeState) := do
  if st.hasBadUtf8Fixture then
    return .ok st
  let rawSeg := ByteArray.mk #[0x72, 0x61, 0x77, 0xff, 0x64, 0x69, 0x72]
  let linkSeg := SlotId.badUtf8Dir.relPath.toUTF8
  let rootParts := splitByteSlash st.rootDir.toUTF8
  let py :=
    "import os, sys\n" ++
    "root = sys.argv[1].encode('utf-8')\n" ++
    "raw_seg = bytes.fromhex(sys.argv[2])\n" ++
    "link_seg = sys.argv[3].encode('utf-8')\n" ++
    "os.makedirs(os.path.join(root, raw_seg), exist_ok=True)\n" ++
    "lp = os.path.join(root, link_seg)\n" ++
    "if not os.path.lexists(lp):\n" ++
    "    os.symlink(raw_seg, lp)\n"
  match ← runPythonFs py #[st.rootDir, byteArrayToHex rawSeg, SlotId.badUtf8Dir.relPath] with
  | .error msg => return .error s!"ensureBadUtf8Fixture failed: {msg}"
  | .ok () =>
    let v1 := vfsPutChild st.model.vfs rootParts rawSeg (.dir true true [])
    let v2 := vfsPutChild v1 rootParts linkSeg (.symlink rawSeg)
    return .ok { st with model := { st.model with vfs := v2 }, hasBadUtf8Fixture := true }

private def initEpisodeState (rawDir : String) : IO (Except String EpisodeState) := do
  let realRoot ← IO.FS.realPath rawDir
  let rootDir := stripTrailingSlash realRoot.toString
  let rootParts := splitByteSlash rootDir.toUTF8
  let cwdDir := s!"{rootDir}/sandbox/cwd"
  let baseVfs ←
    match mkdirPVfsFuel 41 VfsNode.emptyDir [] (splitByteSlash cwdDir.toUTF8) with
    | .ok (v, _) => pure v
    | .error e => return .error s!"mkdirPVfsFuel failed on {cwdDir}: {e.message}"
  match ← LeanSwe.Fs.mkdir cwdDir true true with
  | .error e => return .error s!"init sandbox/cwd failed: {e.message}"
  | .ok () => pure ()
  let plainPath := s!"{rootDir}/{SlotId.plainFile.relPath}"
  match ← LeanSwe.Fs.writeBytes plainPath "plain-file\n".toUTF8 with
  | .error e => return .error s!"init plainFile failed: {e.message}"
  | .ok () => pure ()
  let symPath := s!"{rootDir}/{SlotId.symLinkDir.relPath}"
  match ← LeanSwe.Fs.symlink SlotId.repoA.relPath symPath with
  | .error e => return .error s!"init symLinkDir failed: {e.message}"
  | .ok () => pure ()
  let dangPath := s!"{rootDir}/{SlotId.danglingSym.relPath}"
  match ← LeanSwe.Fs.symlink "missing_target" dangPath with
  | .error e => return .error s!"init danglingSym failed: {e.message}"
  | .ok () => pure ()
  let loopAPath := s!"{rootDir}/{SlotId.symLoopA.relPath}"
  match ← LeanSwe.Fs.symlink SlotId.symLoopB.relPath loopAPath with
  | .error e => return .error s!"init symLoopA failed: {e.message}"
  | .ok () => pure ()
  let loopBPath := s!"{rootDir}/{SlotId.symLoopB.relPath}"
  match ← LeanSwe.Fs.symlink SlotId.symLoopA.relPath loopBPath with
  | .error e => return .error s!"init symLoopB failed: {e.message}"
  | .ok () => pure ()
  let xdgDir := s!"{rootDir}/_fuzz_xdg"
  match ← LeanSwe.Fs.mkdir xdgDir true true with
  | .error e => return .error s!"init _fuzz_xdg failed: {e.message}"
  | .ok () => pure ()
  let homeDir := s!"{rootDir}/_fuzz_home"
  match ← LeanSwe.Fs.mkdir homeDir true true with
  | .error e => return .error s!"init _fuzz_home failed: {e.message}"
  | .ok () => pure ()
  match ← LeanSwe.Fs.writeBytes s!"{homeDir}/.gitconfig"
      "[user]\n\tname = LeanSwe\n\temail = leanswe@localhost\n".toUTF8 with
  | .error e => return .error s!"init _fuzz_home .gitconfig failed: {e.message}"
  | .ok () => pure ()
  let probeRes ← LeanSwe.TempDir.withTempDir none "leanswe-git-init-probe-" fun probeDir => do
    let probeOps := scopedRawOps rootDir cwdDir false
    let probeApi := Impl.mkApiM probeOps
    match ← probeApi.init probeDir false none with
    | .error _ => return .ok "main"
    | .ok () =>
      match ← probeApi.headBranch? probeDir with
      | .ok (some br) => return .ok (if isValidRefNameStr br.raw then br.raw else "main")
      | _ => return .ok "main"
  let defaultBr : RefName :=
    match probeRes with
    | .ok br => { raw := br }
    | .error _ => { raw := "main" }
  let v1 := vfsPutChild baseVfs rootParts SlotId.plainFile.relPath.toUTF8 (.file false "plain-file\n".toUTF8)
  let v2 := vfsPutChild v1 rootParts SlotId.symLinkDir.relPath.toUTF8 (.symlink SlotId.repoA.relPath.toUTF8)
  let v3 := vfsPutChild v2 rootParts SlotId.danglingSym.relPath.toUTF8 (.symlink "missing_target".toUTF8)
  let v4 := vfsPutChild v3 rootParts SlotId.symLoopA.relPath.toUTF8 (.symlink SlotId.symLoopB.relPath.toUTF8)
  let v5 := vfsPutChild v4 rootParts SlotId.symLoopB.relPath.toUTF8 (.symlink SlotId.symLoopA.relPath.toUTF8)
  return .ok {
    rootDir := rootDir
    cwdDir := cwdDir
    model := { vfs := v5, repos := [], processCwd := cwdDir.toUTF8, defaultInitBranch := defaultBr }
  }

private def hasNulByte (bs : ByteArray) : Bool :=
  bs.data.any (· == 0)

private def isSafeRelBytes (bs : ByteArray) : Bool :=
  if bs.isEmpty || hasNulByte bs then false
  else
    let parts := splitByteSlash bs
    !parts.isEmpty && !parts.any (fun seg =>
      seg == ".".toUTF8 || seg == "..".toUTF8 || seg == ".git".toUTF8)

private def isLiveSlotDir (st : EpisodeState) (slot : SlotId) : Bool :=
  let slotParts := splitByteSlash s!"{st.rootDir}/{slot.relPath}".toUTF8
  match resolveVfsFuel 41 st.model.vfs [] slotParts true with
  | .ok (.dir _ true true _) => true
  | _ => false

private def isLiveSearchableDir (vfs : VfsNode) (parts : List ByteArray) : Bool :=
  match resolveVfsFuel 41 vfs [] parts true with
  | .ok (.dir _ true _ _) => true
  | _ => false

private def bumpSlotRegularFileMtimes (slotPath : String) : IO Unit := do
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

private def execVfsWriteFile (st : EpisodeState) (slot : SlotId) (relBytes content : ByteArray)
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

private def execVfsMkdir (st : EpisodeState) (slot : SlotId) (relBytes : ByteArray) : IO (EpisodeState × Bool) := do
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

private def execVfsSymlink (st : EpisodeState) (slot : SlotId) (relBytes targetBytes : ByteArray) :
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

private def execVfsRemoveFile (st : EpisodeState) (slot : SlotId) (relBytes : ByteArray) : IO (EpisodeState × Bool) := do
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

private def execVfsRemoveDir (st : EpisodeState) (slot : SlotId) (relBytes : ByteArray) : IO (EpisodeState × Bool) := do
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

private def execVfsRemoveTree (st : EpisodeState) (slot : SlotId) : IO (EpisodeState × Bool) := do
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

private def execVfsChmodDir (st : EpisodeState) (slot : SlotId) (searchable : Bool) : IO (EpisodeState × Bool) := do
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

private def execVfsChmodSubDir (st : EpisodeState) (slot : SlotId) (relBytes : ByteArray)
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

private def execVfsSetFileExecutable (st : EpisodeState) (slot : SlotId) (relBytes : ByteArray)
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

private def execGitRawLockWorktree (st : EpisodeState) (repoSlot wtSlot : SlotId) (lock : Bool)
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

private def execGitRawCreateTag (st : EpisodeState) (repoSlot : SlotId) (tagName : RefName)
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

private def addKnownCommit (st : EpisodeState) (cid : CommitId) : EpisodeState :=
  if st.knownCommits.contains cid then st else { st with knownCommits := st.knownCommits.push cid }

private def writeFileBoth (st : EpisodeState) (repoSlot : SlotId) (relName : String) (content : ByteArray) :
    IO (Except String EpisodeState) := do
  let (st', ok) ← execVfsWriteFile st repoSlot relName.toUTF8 content false
  if ok then return .ok st'
  else return .error s!"writeFileBoth failed on {relName}"

/-- Short canonical bucket label for a `GitErrorKind`. -/
def errorKindLabel : GitErrorKind → String
  | .notARepo => "notARepo"
  | .invalidRef => "invalidRef"
  | .invalidPath => "invalidPath"
  | .invalidInput => "invalidInput"
  | .dirtyWorktree => "dirtyWorktree"
  | .nothingToCommit => "nothingToCommit"
  | .branchInUse => "branchInUse"
  | .alreadyExists => "alreadyExists"
  | .notFound => "notFound"
  | .conflict => "conflict"
  | .timeout => "timeout"
  | .commandFailed => "commandFailed"
  | .parseError => "parseError"

private def compareExceptTagged {α : Type} [BEq α] [Repr α] (label : String)
    (real : Except GitError α) (model : Except GitError α) (spoofable : Bool := false) :
    Except (String × String) Unit :=
  match real, model with
  | .ok a, .ok b =>
    if a == b then .ok ()
    else .error (s!"{label}:ok", s!"{label} ok mismatch: real={repr a} model={repr b}")
  | .error e1, .error e2 =>
    if allowsCliErrorKind spoofable e2.kind e1.kind && !e1.message.isEmpty && !e2.message.isEmpty then .ok ()
    else
      .error (s!"{label}:err:{errorKindLabel e1.kind}:{errorKindLabel e2.kind}",
        s!"{label} error mismatch: real={repr e1} model={repr e2}")
  | .ok a, .error e2 =>
    .error (s!"{label}:ok_vs_err:{errorKindLabel e2.kind}",
      s!"{label} ok/err mismatch: real=.ok({repr a}) model=.error({repr e2})")
  | .error e1, .ok b =>
    .error (s!"{label}:err_vs_ok:{errorKindLabel e1.kind}",
      s!"{label} err/ok mismatch: real=.error({repr e1}) model=.ok({repr b})")

private def formatByteArrayShort (bs : ByteArray) : String :=
  let previewLen := min bs.size 48
  let previewHex := byteArrayToHex (bs.extract 0 previewLen)
  if bs.size <= 48 then s!"ByteArray(len={bs.size}, hex={previewHex})"
  else s!"ByteArray(len={bs.size}, headHex={previewHex}...)"

private def formatShowOutcome : Except GitError (Option ByteArray) → String
  | .ok none => "ok(none)"
  | .ok (some bs) => s!"ok(some {formatByteArrayShort bs})"
  | .error e => s!"error({repr e})"

private def compareShowFileTagged (label : String)
    (real model : Except GitError (Option ByteArray)) : Except (String × String) Unit :=
  match real, model with
  | .ok a, .ok b =>
    if a == b then .ok ()
    else .error (s!"{label}:ok", s!"{label} ok mismatch: real={formatShowOutcome (.ok a)} model={formatShowOutcome (.ok b)}")
  | .error e1, .error e2 =>
    if e1.kind == e2.kind && !e1.message.isEmpty && !e2.message.isEmpty then .ok ()
    else
      .error (s!"{label}:err:{errorKindLabel e1.kind}:{errorKindLabel e2.kind}",
        s!"{label} error mismatch: real={repr e1} model={repr e2}")
  | .ok a, .error e2 =>
    .error (s!"{label}:ok_vs_err:{errorKindLabel e2.kind}",
      s!"{label} ok/err mismatch: real={formatShowOutcome (.ok a)} model=.error({repr e2})")
  | .error e1, .ok b =>
    .error (s!"{label}:err_vs_ok:{errorKindLabel e1.kind}",
      s!"{label} err/ok mismatch: real=.error({repr e1}) model={formatShowOutcome (.ok b)}")

private def normalizeWorktrees (xs : Array WorktreeInfo) : Array WorktreeInfo :=
  if xs.size <= 2 then xs
  else
    let head := xs.extract 0 1
    let tail := (xs.extract 1 xs.size).qsort (fun a b => a.path < b.path)
    head ++ tail

private def compareWorktreesTagged (label : String) (real model : Except GitError (Array WorktreeInfo)) :
    Except (String × String) Unit :=
  compareExceptTagged label (real.map normalizeWorktrees) (model.map normalizeWorktrees)

private def execGitRawCreateMergeConflict (st : EpisodeState) (repoSlot : SlotId) (branchA branchB : RefName)
    (relPath : String) (dropMergeHead : Bool) : IO (EpisodeState × Bool) := do
  if branchA == branchB || !isValidRefNameStr branchA.raw || !isValidRefNameStr branchB.raw then
    return (st, false)
  if relPath.isEmpty || relPath == ".git" || relPath.startsWith ".git/" then
    return (st, false)
  match validateRelRepoPath relPath with
  | .error _ => return (st, false)
  | .ok () => pure ()
  let repoPath := s!"{st.rootDir}/{repoSlot.relPath}"
  let api := pickApi st false
  let rawOps := scopedRawOps st.rootDir st.cwdDir false
  match resolveCwdAndDiscover st.model repoPath with
  | .error _ => return (st, false)
  | .ok (repo, wt?, _, _) =>
    if repo.isBare then return (st, false)
    match wt? with
    | none => return (st, false)
    | some wt =>
      if wt.index.hasMergeHead || !wt.index.conflicts.isEmpty then return (st, false)
      match (stepStatus st.model repoPath).1 with
      | .error _ => return (st, false)
      | .ok entries =>
        if !entries.isEmpty then return (st, false)
        if (findBranchCommit? repo branchA).isSome || (findBranchCommit? repo branchB).isSome then
          return (st, false)
        let fullA := "refs/heads/" ++ branchA.raw
        let fullB := "refs/heads/" ++ branchB.raw
        if hasRefDFConflict repo fullA || hasRefDFConflict repo fullB then
          return (st, false)
        let curHeadBr := match wt.head with | .symbolic b => some b | .detached _ => none
        if curHeadBr == some branchA || curHeadBr == some branchB then
          return (st, false)
        let mut cur := st
        match ← writeFileBoth cur repoSlot relPath "base\n".toUTF8 with
        | .error _ => return (st, false)
        | .ok st1 => cur := st1
        match ← api.add repoPath #[relPath] false with
        | .error _ => return (cur, true)
        | .ok () =>
          match (evalGitApi.add repoPath #[relPath] false).run cur.model with
          | (.ok (), sAdd) => cur := { cur with model := sAdd }
          | (.error _, _) => return (cur, true)
        let cOpts : CommitOptions := {
          message := "mc base"
          allowEmpty := true
          authorName := some "Fuzz"
          authorEmail := some "fuzz@example.com"
        }
        match ← api.commit repoPath cOpts with
        | .error _ => return (cur, true)
        | .ok cidBase =>
          let (_, sCBase) := stepCommitWithId cur.model repoPath cOpts (some cidBase)
          cur := addKnownCommit { cur with model := sCBase } cidBase
        match ← api.createBranch repoPath branchA none false,
              (evalGitApi.createBranch repoPath branchA none false).run cur.model with
        | .ok (), (.ok (), sBrA) => cur := { cur with model := sBrA }
        | _, _ => return (cur, true)
        match ← api.createBranch repoPath branchB none false,
              (evalGitApi.createBranch repoPath branchB none false).run cur.model with
        | .ok (), (.ok (), sBrB) => cur := { cur with model := sBrB }
        | _, _ => return (cur, true)
        match ← api.switch repoPath branchA false none false,
              (evalGitApi.switch repoPath branchA false none false).run cur.model with
        | .ok (), (.ok (), sSwA) => cur := { cur with model := sSwA }
        | _, _ => return (cur, true)
        match ← writeFileBoth cur repoSlot relPath "ours\n".toUTF8 with
        | .error _ => return (cur, true)
        | .ok st2 => cur := st2
        match ← api.add repoPath #[relPath] false,
              (evalGitApi.add repoPath #[relPath] false).run cur.model with
        | .ok (), (.ok (), sAddA) => cur := { cur with model := sAddA }
        | _, _ => return (cur, true)
        let cOptsA : CommitOptions := { message := "mc ours", authorName := some "Fuzz", authorEmail := some "fuzz@example.com" }
        match ← api.commit repoPath cOptsA with
        | .error _ => return (cur, true)
        | .ok cidA =>
          let (_, sCA) := stepCommitWithId cur.model repoPath cOptsA (some cidA)
          cur := addKnownCommit { cur with model := sCA } cidA
        match ← api.switch repoPath branchB false none false,
              (evalGitApi.switch repoPath branchB false none false).run cur.model with
        | .ok (), (.ok (), sSwB) => cur := { cur with model := sSwB }
        | _, _ => return (cur, true)
        match ← writeFileBoth cur repoSlot relPath "theirs\n".toUTF8 with
        | .error _ => return (cur, true)
        | .ok st3 => cur := st3
        match ← api.add repoPath #[relPath] false,
              (evalGitApi.add repoPath #[relPath] false).run cur.model with
        | .ok (), (.ok (), sAddB) => cur := { cur with model := sAddB }
        | _, _ => return (cur, true)
        let cOptsB : CommitOptions := { message := "mc theirs", authorName := some "Fuzz", authorEmail := some "fuzz@example.com" }
        let cidB ← match ← api.commit repoPath cOptsB with
          | .error _ => return (cur, true)
          | .ok c =>
            let (_, sCB) := stepCommitWithId cur.model repoPath cOptsB (some c)
            cur := addKnownCommit { cur with model := sCB } c
            pure c
        match ← api.switch repoPath branchA false none false,
              (evalGitApi.switch repoPath branchA false none false).run cur.model with
        | .ok (), (.ok (), sSwA2) => cur := { cur with model := sSwA2 }
        | _, _ => return (cur, true)
        let envPairs ← rawOps.listEnv
        let overrides := match envPairs with | .ok e => cleanGitEnv e | .error _ => cleanGitEnv #[]
        let _ ← rawOps.execGit overrides { cwd := some repoPath, args := #["merge", "--no-edit", branchB.raw] }
        if dropMergeHead then
          match ← rawOps.execGit overrides
              { cwd := some repoPath, args := #["rev-parse", "--path-format=absolute", "--git-path", "MERGE_HEAD"] } with
          | .ok mhOut =>
            if mhOut.exitCode == 0 then
              let mhPath := (String.fromUTF8? mhOut.stdout).getD "" |>.trimAscii.toString
              if !mhPath.isEmpty then
                let _ ← LeanSwe.Fs.unlink mhPath true
          | .error _ => pure ()
        let diskBytes ←
          match ← LeanSwe.Fs.readBytes s!"{repoPath}/{relPath}" with
          | .ok b => pure b
          | .error _ => pure "ours\n".toUTF8
        match ← writeFileBoth cur repoSlot relPath diskBytes with
        | .error _ => return (cur, true)
        | .ok st4 => cur := st4
        let relBytes := relPath.toUTF8
        let repos' := cur.model.repos.map fun r =>
          if r.commonDir != repo.commonDir then r
          else
            updateWorktreeInRepo r wt.rootPath fun slot =>
              { slot with
                index :=
                  { entries := slot.index.entries.filter (fun p => p.1 != relBytes)
                    conflicts := [{ path := relBytes, oursStatus := .unmerged, theirsStatus := .unmerged }]
                    hasMergeHead := !dropMergeHead
                    mergeParents := if dropMergeHead then [] else [cidB] } }
        return ({ cur with model := { cur.model with repos := repos' } }, true)

private def execGitRawCreateCrissCrossMerge (st : EpisodeState) (repoSlot : SlotId) : IO (EpisodeState × Bool) := do
  let repoPath := s!"{st.rootDir}/{repoSlot.relPath}"
  let api := pickApi st false
  let rawOps := scopedRawOps st.rootDir st.cwdDir false
  let brA : RefName := { raw := "cc_a" }
  let brB : RefName := { raw := "cc_b" }
  match resolveCwdAndDiscover st.model repoPath with
  | .error _ => return (st, false)
  | .ok (repo, wt?, _, _) =>
    if repo.isBare then return (st, false)
    match wt? with
    | none => return (st, false)
    | some wt =>
      if wt.index.hasMergeHead || !wt.index.conflicts.isEmpty then return (st, false)
      match (stepStatus st.model repoPath).1 with
      | .error _ => return (st, false)
      | .ok entries =>
        if !entries.isEmpty then return (st, false)
        if (findBranchCommit? repo brA).isSome || (findBranchCommit? repo brB).isSome then
          return (st, false)
        if hasRefDFConflict repo "refs/heads/cc_a" || hasRefDFConflict repo "refs/heads/cc_b" then
          return (st, false)
        let mut cur := st
        match ← writeFileBoth cur repoSlot "cc_base.txt" "0\n".toUTF8 with
        | .error _ => return (st, false)
        | .ok st1 => cur := st1
        match ← api.add repoPath #["cc_base.txt"] false,
              (evalGitApi.add repoPath #["cc_base.txt"] false).run cur.model with
        | .ok (), (.ok (), sAdd0) => cur := { cur with model := sAdd0 }
        | _, _ => return (cur, true)
        let opts0 : CommitOptions := { message := "cc0", authorName := some "Fuzz", authorEmail := some "fuzz@example.com" }
        let cid0 ← match ← api.commit repoPath opts0 with
          | .error _ => return (cur, true)
          | .ok c =>
            let (_, s0) := stepCommitWithId cur.model repoPath opts0 (some c)
            cur := addKnownCommit { cur with model := s0 } c
            pure c
        let _ := cid0
        match ← api.createBranch repoPath brA none false,
              (evalGitApi.createBranch repoPath brA none false).run cur.model with
        | .ok (), (.ok (), sA) => cur := { cur with model := sA }
        | _, _ => return (cur, true)
        match ← api.createBranch repoPath brB none false,
              (evalGitApi.createBranch repoPath brB none false).run cur.model with
        | .ok (), (.ok (), sB) => cur := { cur with model := sB }
        | _, _ => return (cur, true)
        match ← api.switch repoPath brA false none false,
              (evalGitApi.switch repoPath brA false none false).run cur.model with
        | .ok (), (.ok (), sSwA) => cur := { cur with model := sSwA }
        | _, _ => return (cur, true)
        match ← writeFileBoth cur repoSlot "cc_a.txt" "a1\n".toUTF8 with
        | .error _ => return (cur, true)
        | .ok st2 => cur := st2
        match ← api.add repoPath #["cc_a.txt"] false,
              (evalGitApi.add repoPath #["cc_a.txt"] false).run cur.model with
        | .ok (), (.ok (), sAddA) => cur := { cur with model := sAddA }
        | _, _ => return (cur, true)
        let optsA : CommitOptions := { message := "ccA1", authorName := some "Fuzz", authorEmail := some "fuzz@example.com" }
        let cidA1 ← match ← api.commit repoPath optsA with
          | .error _ => return (cur, true)
          | .ok c =>
            let (_, sCA) := stepCommitWithId cur.model repoPath optsA (some c)
            cur := addKnownCommit { cur with model := sCA } c
            pure c
        match ← api.switch repoPath brB false none false,
              (evalGitApi.switch repoPath brB false none false).run cur.model with
        | .ok (), (.ok (), sSwB) => cur := { cur with model := sSwB }
        | _, _ => return (cur, true)
        match ← writeFileBoth cur repoSlot "cc_b.txt" "b1\n".toUTF8 with
        | .error _ => return (cur, true)
        | .ok st3 => cur := st3
        match ← api.add repoPath #["cc_b.txt"] false,
              (evalGitApi.add repoPath #["cc_b.txt"] false).run cur.model with
        | .ok (), (.ok (), sAddB) => cur := { cur with model := sAddB }
        | _, _ => return (cur, true)
        let optsB : CommitOptions := { message := "ccB1", authorName := some "Fuzz", authorEmail := some "fuzz@example.com" }
        let cidB1 ← match ← api.commit repoPath optsB with
          | .error _ => return (cur, true)
          | .ok c =>
            let (_, sCB) := stepCommitWithId cur.model repoPath optsB (some c)
            cur := addKnownCommit { cur with model := sCB } c
            pure c
        match ← api.switch repoPath brA false none false,
              (evalGitApi.switch repoPath brA false none false).run cur.model with
        | .ok (), (.ok (), sSwA2) => cur := { cur with model := sSwA2 }
        | _, _ => return (cur, true)
        let envPairs ← rawOps.listEnv
        let overrides := match envPairs with | .ok e => cleanGitEnv e | .error _ => cleanGitEnv #[]
        match ← rawOps.execGit overrides { cwd := some repoPath, args := #["merge", "--no-edit", cidB1.hex] } with
        | .ok outM1 =>
          if outM1.exitCode != 0 then return (cur, true)
        | .error _ => return (cur, true)
        let cidM1 ← match ← api.revParseCommit repoPath "HEAD" with
          | .error _ => return (cur, true)
          | .ok c => pure c
        let slotParts := splitByteSlash wt.rootPath
        let v1 := vfsPutChild cur.model.vfs slotParts "cc_b.txt".toUTF8 (.file false "b1\n".toUTF8)
        let mergeTree1 :=
          match cur.model.repos.find? (·.commonDir == repo.commonDir) with
          | some rCur =>
            sortByBytes (·.1) (treeOfCommit rCur cidA1 ++ [("cc_b.txt".toUTF8, { kind := .regular false, bytes := "b1\n".toUTF8 })])
          | none => []
        let repos1 := cur.model.repos.map fun r =>
          if r.commonDir != repo.commonDir then r
          else
            let r1 := { r with
              commits := r.commits ++ [{ id := cidM1, parents := [cidA1, cidB1], tree := mergeTree1, message := "ccM1" }]
              refs := setRefInList r.refs "refs/heads/cc_a" cidM1 }
            updateWorktreeInRepo r1 wt.rootPath fun slot =>
              { slot with index := { entries := mergeTree1, conflicts := [], hasMergeHead := false } }
        cur := addKnownCommit { cur with model := { cur.model with vfs := v1, repos := repos1 } } cidM1
        match ← api.switch repoPath brB false none false,
              (evalGitApi.switch repoPath brB false none false).run cur.model with
        | .ok (), (.ok (), sSwB2) => cur := { cur with model := sSwB2 }
        | _, _ => return (cur, true)
        match ← rawOps.execGit overrides { cwd := some repoPath, args := #["merge", "--no-edit", cidA1.hex] } with
        | .ok outM2 =>
          if outM2.exitCode != 0 then return (cur, true)
        | .error _ => return (cur, true)
        let cidM2 ← match ← api.revParseCommit repoPath "HEAD" with
          | .error _ => return (cur, true)
          | .ok c => pure c
        let v2 := vfsPutChild cur.model.vfs slotParts "cc_a.txt".toUTF8 (.file false "a1\n".toUTF8)
        let mergeTree2 :=
          match cur.model.repos.find? (·.commonDir == repo.commonDir) with
          | some rCur =>
            sortByBytes (·.1) (treeOfCommit rCur cidB1 ++ [("cc_a.txt".toUTF8, { kind := .regular false, bytes := "a1\n".toUTF8 })])
          | none => []
        let repos2 := cur.model.repos.map fun r =>
          if r.commonDir != repo.commonDir then r
          else
            let r1 := { r with
              commits := r.commits ++ [{ id := cidM2, parents := [cidB1, cidA1], tree := mergeTree2, message := "ccM2" }]
              refs := setRefInList r.refs "refs/heads/cc_b" cidM2 }
            updateWorktreeInRepo r1 wt.rootPath fun slot =>
              { slot with index := { entries := mergeTree2, conflicts := [], hasMergeHead := false } }
        return (addKnownCommit { cur with model := { cur.model with vfs := v2, repos := repos2 } } cidM2, true)

private def recordOutcome {α : Type} (tr : CoverageTracker) (op : String) (res : Except GitError α) :
    CoverageTracker :=
  match res with
  | .ok _ => tr.record op "ok"
  | .error e => tr.record op s!"err.{errorKindLabel e.kind}"

private def runRawOpChecked {α : Type} [BEq α] [Repr α] (st : EpisodeState) (tr : CoverageTracker)
    (opName : String) (realAct : IO (Except GitError α)) (modelAct : GitRepoState → Except GitError α × GitRepoState)
    (onBothOk : EpisodeState → α → α → EpisodeState := fun s _ _ => s) :
    IO (Except TraceError (EpisodeState × CoverageTracker)) := do
  let realRes ← realAct
  let (modelRes, modelNext) := modelAct st.model
  let tr' := recordOutcome tr opName realRes
  match compareExceptTagged opName realRes modelRes st.hasSpoofablePath with
  | .error (tag, msg) => return .error (.mismatch tag msg)
  | .ok () =>
    let st1 := { st with model := modelNext }
    let st2 :=
      match realRes, modelRes with
      | .ok v1, .ok v2 => onBothOk st1 v1 v2
      | _, _ => st1
    return .ok (st2, tr')

private def isGitHeaderCrudStrip (c : Char) : Bool :=
  c ≤ ' ' || c == ',' || c == ':' || c == ';' ||
  c == '<' || c == '>' || c == '"' || c == '\'' || c == '\\'

private def trimGitIdentField (s : String) : String :=
  let dropL := s.toList.dropWhile isGitHeaderCrudStrip
  String.ofList (dropL.reverse.dropWhile isGitHeaderCrudStrip).reverse

private def findDoubleLfIdx (bs : ByteArray) : Option Nat := Id.run do
  if bs.size < 2 then
    return none
  for i in List.range (bs.size - 1) do
    if bs[i]! == 0x0a && bs[i + 1]! == 0x0a then
      return some i
  return none

private def verifyCommitObject (st : EpisodeState) (repoPath : String) (cid : CommitId)
    (opts : CommitOptions) : IO (Except TraceError Unit) := do
  let rawOps := scopedRawOps st.rootDir st.cwdDir false
  let envPairs ← rawOps.listEnv
  let overrides := match envPairs with | .ok e => cleanGitEnv e | .error _ => cleanGitEnv #[]
  match ← rawOps.execGit overrides { cwd := some repoPath, args := #["cat-file", "commit", cid.hex] } with
  | .error e =>
    return .error (.mismatch "commit:metadata" s!"cat-file commit failed: {repr e}")
  | .ok out =>
    if out.exitCode != 0 then
      return .error (.mismatch "commit:metadata" s!"cat-file commit exited {out.exitCode}")
    match findDoubleLfIdx out.stdout with
    | none =>
      return .error (.mismatch "commit:metadata" "commit object missing header/body blank line")
    | some sepIdx =>
      let hdrBytes := out.stdout.extract 0 sepIdx
      let bodyBytes := out.stdout.extract (sepIdx + 2) out.stdout.size
      let expectedBody := (cleanCommitMessageWhitespace opts.message).toUTF8
      if bodyBytes != expectedBody then
        return .error (.mismatch "commit:metadata"
          s!"commit message mismatch: got {formatByteArrayShort bodyBytes}, expected {formatByteArrayShort expectedBody}")
      match String.fromUTF8? hdrBytes with
      | none =>
        return .error (.mismatch "commit:metadata" "commit object header is not valid UTF-8")
      | some hdrText =>
        let lines := hdrText.splitOn "\n"
        let expName := trimGitIdentField (opts.authorName.getD "LeanSwe")
        let expEmail := trimGitIdentField (opts.authorEmail.getD "leanswe@localhost")
        let expAuthorPfx := s!"author {expName} <{expEmail}> "
        let expCommitterPfx := s!"committer {expName} <{expEmail}> "
        let hasAuthor := lines.any (·.startsWith expAuthorPfx)
        let hasCommitter := lines.any (·.startsWith expCommitterPfx)
        if !hasAuthor || !hasCommitter then
          return .error (.mismatch "commit:metadata"
            s!"commit ident mismatch: expected '{expAuthorPfx}' and '{expCommitterPfx}', header='{hdrText}'")
        return .ok ()

private def resolveWitnessRev? (st : EpisodeState) (repoPath rev : String) : IO (Option CommitId) := do
  match ← (pickApi st false).revParseCommit repoPath rev with
  | .ok cid => return some cid
  | .error _ => return none

private def resolveWitnessHead? (st : EpisodeState) (repoPath : String) : IO (Option CommitId) := do
  match ← (pickApi st false).headCommit? repoPath with
  | .ok (some cid) => return some cid
  | _ => return none

private def resolveWitnessBranch? (st : EpisodeState) (repoPath : String) (br : RefName) : IO (Option CommitId) := do
  match ← (pickApi st false).revParseCommit repoPath ("refs/heads/" ++ br.raw) with
  | .ok cid => return some cid
  | .error _ => resolveWitnessRev? st repoPath br.raw

private def resolveWitnessHeadBranch? (st : EpisodeState) (repoPath : String) : IO (Option RefName) := do
  match ← (pickApi st false).headBranch? repoPath with
  | .ok br? => return br?
  | .error _ => return none

private def resolveWitnessSymbolicBranch? (st : EpisodeState) (repoPath spec : String) : IO (Option RefName) := do
  let rawOps := scopedRawOps st.rootDir st.cwdDir false
  let envPairs ← rawOps.listEnv
  let overrides := match envPairs with | .ok e => cleanGitEnv e | .error _ => cleanGitEnv #[]
  match ← rawOps.execGit overrides { cwd := some repoPath, args := #["rev-parse", "-q", "--verify", "--symbolic-full-name", spec] } with
  | .ok out =>
    if out.exitCode != 0 then return none
    match String.fromUTF8? out.stdout with
    | none => return none
    | some s =>
      let trimmed := Impl.trimAsciiWhitespace s
      if trimmed.startsWith "refs/heads/" then
        return some { raw := String.ofList (trimmed.toList.drop 11) }
      else
        return none
  | .error _ => return none

private def splitBytesOn (sep : UInt8) (bs : ByteArray) : List ByteArray := Id.run do
  let mut out : List ByteArray := []
  let mut start := 0
  for i in List.range bs.size do
    if bs[i]! == sep then
      out := out ++ [bs.extract start i]
      start := i + 1
  if start < bs.size then
    out := out ++ [bs.extract start bs.size]
  return out

private def findByteIdx? (target : UInt8) (bs : ByteArray) : Option Nat := Id.run do
  for i in List.range bs.size do
    if bs[i]! == target then
      return some i
  return none

private def resolveWitnessIndex? (st : EpisodeState) (repoPath : String) : IO (Option IndexState) := do
  let curIdx : IndexState :=
    match resolveCwdAndDiscover st.model repoPath with
    | .ok (_, some wt, _, _) => wt.index
    | _ => {}
  let rawOps := scopedRawOps st.rootDir st.cwdDir false
  let envPairs ← rawOps.listEnv
  let overrides := match envPairs with | .ok e => cleanGitEnv e | .error _ => cleanGitEnv #[]
  match ← rawOps.execGit overrides { cwd := some repoPath, args := #["ls-files", "--stage", "-z"] } with
  | .error _ => return none
  | .ok out =>
    if out.exitCode != 0 then
      return none
    let mut entries : List (ByteArray × GitTreeEntry) := []
    let mut unmergedPaths : List ByteArray := []
    for recBytes in splitBytesOn 0x00 out.stdout do
      if recBytes.isEmpty then continue
      match findByteIdx? 0x09 recBytes with
      | none => return none
      | some tabIdx =>
        let hdrBytes := recBytes.extract 0 tabIdx
        let pathBytes := recBytes.extract (tabIdx + 1) recBytes.size
        match String.fromUTF8? hdrBytes with
        | none => return none
        | some hdr =>
          match hdr.splitOn " " with
          | [modeStr, shaStr, stageStr] =>
            if stageStr == "0" then
              if modeStr == "160000" then
                entries := entries ++ [(pathBytes, { kind := .gitlink, bytes := shaStr.toUTF8 })]
              else
                match ← rawOps.execGit overrides { cwd := some repoPath, args := #["cat-file", "blob", shaStr] } with
                | .error _ => return none
                | .ok blobOut =>
                  if blobOut.exitCode != 0 then return none
                  let kind := if modeStr == "120000" then GitBlobKind.symlink else GitBlobKind.regular (modeStr == "100755")
                  entries := entries ++ [(pathBytes, { kind := kind, bytes := blobOut.stdout })]
            else
              unmergedPaths := pathBytes :: unmergedPaths
          | _ => return none
    let keptConflicts := curIdx.conflicts.filter fun c => unmergedPaths.contains c.path
    return some { curIdx with entries := sortByBytes (·.1) entries, conflicts := keptConflicts }

private def syncWorktreeTrackedDiskBytes (st : EpisodeState) (repoPath : String) : IO EpisodeState := do
  match resolveCwdAndDiscover st.model repoPath with
  | .ok (repo, some wt, _, _) =>
    let rootParts := splitByteSlash wt.rootPath
    let some rootStr := String.fromUTF8? wt.rootPath | return st
    let mut vfs := st.model.vfs
    for (relBytes, entry) in wt.index.entries do
      match entry.kind with
      | .regular ex =>
        if let some relStr := String.fromUTF8? relBytes then
          let fullPath := s!"{rootStr}/{relStr}"
          match ← LeanSwe.Fs.readBytes fullPath with
          | .ok diskBs =>
            if diskBs != entry.bytes then
              let segs := splitByteSlash relBytes
              match segs.reverse with
              | leaf :: revParent =>
                let parentParts := rootParts ++ revParent.reverse
                if (lookupNodeAtParts vfs (parentParts ++ [leaf])).isSome then
                  vfs := vfsPutChild vfs parentParts leaf (.file ex diskBs)
              | [] => pure ()
          | .error _ => pure ()
      | _ => pure ()
    let _ := repo
    return { st with model := { st.model with vfs := vfs } }
  | _ => return st

private def syncWorktreeIndexFromWitness (st : EpisodeState) (repoPath : String) : IO EpisodeState := do
  match resolveCwdAndDiscover st.model repoPath with
  | .ok (repo, some wt, _, _) =>
    match ← resolveWitnessIndex? st repoPath with
    | some idx' =>
      let repo' := updateWorktreeInRepo repo wt.rootPath fun slot => { slot with index := idx' }
      return { st with model := { st.model with repos := updateRepoInList st.model.repos repo.commonDir (fun _ => repo') } }
    | none => return st
  | _ => return st

private def targetTreeHasSpecial (st : EpisodeState) (repoPath : String) : Bool :=
  match resolveCwdAndDiscover st.model repoPath with
  | .ok (repo, some wt, _, _) =>
    let anyCommitSpecial := repo.commits.any fun c =>
      c.tree.any fun (p, e) =>
        e.kind == .gitlink ||
        basenameBytes p == ".gitignore".toUTF8 ||
        basenameBytes p == ".gitattributes".toUTF8
    worktreeHasSpecialMetadata st.model repo wt || anyCommitSpecial
  | _ => false

private def bytesHasSpoofChar (bs : ByteArray) : Bool :=
  bs.data.any fun b => b == 0x27 || b == 0x22 || b == 0x0a || b == 0x0d

private def targetHasSpoofChar : PathTarget → Bool
  | .subRel _ rel => hasStderrSpoofChar rel
  | .raw s => hasStderrSpoofChar s
  | _ => false

private def stepIntroducesSpoof : GitFuzzStep → Bool
  | .vfsWriteFile _ rel _ _ => bytesHasSpoofChar rel
  | .vfsMkdir _ rel => bytesHasSpoofChar rel
  | .vfsSymlink _ rel tgt => bytesHasSpoofChar rel || bytesHasSpoofChar tgt
  | .gitRawLockWorktree _ _ _ rsn? => rsn?.any hasStderrSpoofChar
  | .opAdd t ps _ _ => targetHasSpoofChar t || ps.any hasStderrSpoofChar
  | .opInit t _ _ _ => targetHasSpoofChar t
  | .opClone s t _ _ => targetHasSpoofChar s || targetHasSpoofChar t
  | .opWorktreeAdd t wt _ _ _ _ _ => targetHasSpoofChar t || targetHasSpoofChar wt
  | .opWorktreeRemove t wt _ _ => targetHasSpoofChar t || targetHasSpoofChar wt
  | .opDiffNameStatus t _ _ ps _ => targetHasSpoofChar t || ps.any hasStderrSpoofChar
  | .opShowFile t _ p _ => targetHasSpoofChar t || hasStderrSpoofChar p
  | .opStatus t _ => targetHasSpoofChar t
  | .opCheckout t _ _ _ => targetHasSpoofChar t
  | .opSwitch t _ _ _ _ _ => targetHasSpoofChar t
  | .opFetch t r rf? _ _ => targetHasSpoofChar t || hasStderrSpoofChar r || rf?.any hasStderrSpoofChar
  | _ => false

private def execStepFuel (fuel : Nat) (st0 : EpisodeState) (tr : CoverageTracker) (step : GitFuzzStep) :
    IO (Except TraceError (EpisodeState × CoverageTracker)) := do
  match fuel with
  | 0 => return .error (.infra "execStepFuel depth exceeded")
  | fuel' + 1 =>
    let st0' := if stepIntroducesSpoof step then { st0 with hasSpoofablePath := true } else st0
    let st ←
      if stepMentionsBadUtf8 step then
        match ← ensureBadUtf8Fixture st0' with
        | .ok s' => pure s'
        | .error msg => return .error (.infra msg)
      else pure st0'
    match step with
    | .vfsWriteFile sl rel content ex =>
      let (st', okMut) ← execVfsWriteFile st sl rel content ex
      return .ok (st', tr.record step.opName (if okMut then "ok" else "noop"))
    | .vfsMkdir sl rel =>
      let (st', okMut) ← execVfsMkdir st sl rel
      return .ok (st', tr.record step.opName (if okMut then "ok" else "noop"))
    | .vfsSymlink sl rel tgt =>
      let (st', okMut) ← execVfsSymlink st sl rel tgt
      return .ok (st', tr.record step.opName (if okMut then "ok" else "noop"))
    | .vfsRemoveFile sl rel =>
      let (st', okMut) ← execVfsRemoveFile st sl rel
      return .ok (st', tr.record step.opName (if okMut then "ok" else "noop"))
    | .vfsRemoveDir sl rel =>
      let (st', okMut) ← execVfsRemoveDir st sl rel
      return .ok (st', tr.record step.opName (if okMut then "ok" else "noop"))
    | .vfsRemoveTree sl =>
      let (st', okMut) ← execVfsRemoveTree st sl
      return .ok (st', tr.record step.opName (if okMut then "ok" else "noop"))
    | .vfsChmodDir sl searchable =>
      let (st', okMut) ← execVfsChmodDir st sl searchable
      return .ok (st', tr.record step.opName (if okMut then "ok" else "noop"))
    | .vfsChmodSubDir sl rel searchable =>
      let (st', okMut) ← execVfsChmodSubDir st sl rel searchable
      return .ok (st', tr.record step.opName (if okMut then "ok" else "noop"))
    | .vfsSetFileExecutable sl rel executable =>
      let (st', okMut) ← execVfsSetFileExecutable st sl rel executable
      return .ok (st', tr.record step.opName (if okMut then "ok" else "noop"))
    | .gitRawLockWorktree rSl wtSl lock rsn? =>
      let (st', okMut) ← execGitRawLockWorktree st rSl wtSl lock rsn?
      return .ok (st', tr.record step.opName (if okMut then "ok" else "noop"))
    | .gitRawCreateTag rSl tagName targetRev =>
      let (st', okMut) ← execGitRawCreateTag st rSl tagName targetRev
      return .ok (st', tr.record step.opName (if okMut then "ok" else "noop"))
    | .gitRawCreateMergeConflict rSl bA bB relPath dropMH =>
      let (st', okMut) ← execGitRawCreateMergeConflict st rSl bA bB relPath dropMH
      return .ok (st', tr.record step.opName (if okMut then "ok" else "noop"))
    | .gitRawCreateCrissCrossMerge rSl =>
      let (st', okMut) ← execGitRawCreateCrissCrossMerge st rSl
      return .ok (st', tr.record step.opName (if okMut then "ok" else "noop"))
    | .opIsRepo t poison =>
      let p := resolveTarget st.rootDir t
      runRawOpChecked st tr step.opName ((pickApi st poison).isRepo p) (evalGitApi.isRepo p)
    | .opRepoRoot t poison =>
      let p := resolveTarget st.rootDir t
      runRawOpChecked st tr step.opName ((pickApi st poison).repoRoot p) (evalGitApi.repoRoot p)
    | .opCommonDir t poison =>
      let p := resolveTarget st.rootDir t
      runRawOpChecked st tr step.opName ((pickApi st poison).commonDir p) (evalGitApi.commonDir p)
    | .opHeadCommit t poison =>
      let p := resolveTarget st.rootDir t
      runRawOpChecked st tr step.opName ((pickApi st poison).headCommit? p) (evalGitApi.headCommit? p)
    | .opHeadBranch t poison =>
      let p := resolveTarget st.rootDir t
      runRawOpChecked st tr step.opName ((pickApi st poison).headBranch? p) (evalGitApi.headBranch? p)
    | .opHeadState t poison =>
      let p := resolveTarget st.rootDir t
      runRawOpChecked st tr step.opName ((pickApi st poison).headState p) (evalGitApi.headState p)
    | .opRevParseCommit t rev poison =>
      let p := resolveTarget st.rootDir t
      let revStr := resolveRevSpec st rev
      if !isExtendedRevSpec revStr then
        runRawOpChecked st tr step.opName ((pickApi st poison).revParseCommit p revStr) (evalGitApi.revParseCommit p revStr)
          fun s c _ => addKnownCommit s c
      else
        let realRes ← (pickApi st poison).revParseCommit p revStr
        let tr' := recordOutcome tr step.opName realRes
        if !allowsRevParseCommit st.model p revStr realRes then
          let (mRes, _) := evalGitApi.revParseCommit p revStr st.model
          return .error (.mismatch s!"{step.opName}:relational"
            s!"revParseCommit relational mismatch for rev='{revStr}': real={repr realRes} model={repr mRes}")
        let st' :=
          match realRes with
          | .ok cid => addKnownCommit st cid
          | .error _ => st
        return .ok (st', tr')
    | .opIsAncestor t aIdx bIdx rawA? rawB? poison =>
      let p := resolveTarget st.rootDir t
      let cA := resolveCommitIdx st aIdx rawA?
      let cB := resolveCommitIdx st bIdx rawB?
      runRawOpChecked st tr step.opName ((pickApi st poison).isAncestor p cA cB) (evalGitApi.isAncestor p cA cB)
    | .opMergeBase t aIdx bIdx rawA? rawB? poison =>
      let p := resolveTarget st.rootDir t
      let cA := resolveCommitIdx st aIdx rawA?
      let cB := resolveCommitIdx st bIdx rawB?
      let realRes ← (pickApi st poison).mergeBase? p cA cB
      let tr' := recordOutcome tr step.opName realRes
      let okRel :=
        allowsMergeBase st.model p cA cB realRes ||
        match realRes, (evalGitApi.mergeBase? p cA cB st.model).1 with
        | .error er, .error em => allowsCliErrorKind st.hasSpoofablePath em.kind er.kind && !er.message.isEmpty
        | _, _ => false
      if !okRel then
        let (mRes, _) := evalGitApi.mergeBase? p cA cB st.model
        let tag := match realRes, mRes with
          | .ok _, .ok _ => s!"{step.opName}:ok"
          | .error _, .error _ => s!"{step.opName}:errKind"
          | .ok _, .error _ => s!"{step.opName}:realOkModelErr"
          | .error _, .ok _ => s!"{step.opName}:realErrModelOk"
        return .error (.mismatch tag
          s!"mergeBase? mismatch for a='{cA.hex}' b='{cB.hex}': real={repr realRes} model={repr mRes}")
      return .ok (st, tr')
    | .opStatus t poison =>
      let p := resolveTarget st.rootDir t
      let realRes ← (pickApi st poison).status p
      let tr' := recordOutcome tr step.opName realRes
      let okRel :=
        allowsStatus st.model p realRes ||
        match realRes, (evalGitApi.status p st.model).1 with
        | .error er, .error em => allowsCliErrorKind st.hasSpoofablePath em.kind er.kind && !er.message.isEmpty
        | _, _ => false
      if !okRel then
        let (mRes, _) := evalGitApi.status p st.model
        let tag := match realRes, mRes with
          | .ok _, .ok _ => s!"{step.opName}:ok"
          | .error _, .error _ => s!"{step.opName}:errKind"
          | .ok _, .error _ => s!"{step.opName}:realOkModelErr"
          | .error _, .ok _ => s!"{step.opName}:realErrModelOk"
        return .error (.mismatch tag
          s!"status mismatch for path='{p}': real={repr realRes} model={repr mRes}")
      return .ok (st, tr')
    | .opDiffNameStatus t revA revB? ps poison =>
      let p := resolveTarget st.rootDir t
      let revAStr := resolveRevSpec st revA
      let revBStr? := revB?.map (resolveRevSpec st)
      let realRes ← (pickApi st poison).diffNameStatus p revAStr revBStr? ps
      let tr' := recordOutcome tr step.opName realRes
      let okRel :=
        allowsDiffNameStatus st.model p revAStr revBStr? ps realRes ||
        match realRes, (evalGitApi.diffNameStatus p revAStr revBStr? ps st.model).1 with
        | .error er, .error em => allowsCliErrorKind st.hasSpoofablePath em.kind er.kind && !er.message.isEmpty
        | _, _ => false
      if !okRel then
        let (mRes, _) := evalGitApi.diffNameStatus p revAStr revBStr? ps st.model
        let tag := match realRes, mRes with
          | .ok _, .ok _ => s!"{step.opName}:ok"
          | .error _, .error _ => s!"{step.opName}:errKind"
          | .ok _, .error _ => s!"{step.opName}:realOkModelErr"
          | .error _, .ok _ => s!"{step.opName}:realErrModelOk"
        return .error (.mismatch tag
          s!"diffNameStatus relational mismatch for revA='{revAStr}' revB={repr revBStr?} ps={repr ps}: real={repr realRes} model={repr mRes}")
      return .ok (st, tr')
    | .opListWorktrees t poison =>
      let p := resolveTarget st.rootDir t
      let realRes ← (pickApi st poison).listWorktrees p
      let (modelRes, modelNext) := evalGitApi.listWorktrees p st.model
      let tr' := recordOutcome tr step.opName realRes
      match compareWorktreesTagged step.opName realRes modelRes with
      | .error (tag, msg) => return .error (.mismatch tag msg)
      | .ok () => return .ok ({ st with model := modelNext }, tr')
    | .opShowFile t rev relPath poison =>
      let p := resolveTarget st.rootDir t
      let revStr := resolveRevSpec st rev
      let realRes ← (pickApi st poison).showFile? p revStr relPath
      let tr' := recordOutcome tr step.opName realRes
      if !isExtendedRevSpec revStr then
        let (modelRes, modelNext) := (evalGitApi.showFile? p revStr relPath).run st.model
        match compareShowFileTagged step.opName realRes modelRes with
        | .error (tag, msg) => return .error (.mismatch tag msg)
        | .ok () => return .ok ({ st with model := modelNext }, tr')
      else
        let witnessCid? ←
          if isValidStrictRevSpec revStr then resolveWitnessRev? st p revStr else pure none
        if !allowsShowFile st.model p revStr relPath witnessCid? realRes then
          let (mRes, _) := stepShowFileWithWitness st.model p revStr relPath witnessCid?
          return .error (.mismatch s!"{step.opName}:relational"
            s!"showFile? relational mismatch for rev='{revStr}' path='{relPath}' witness={repr witnessCid?}: real={repr realRes} model={repr mRes}")
        return .ok (st, tr')
    | .opInit t bare initBr? poison =>
      let p := resolveTarget st.rootDir t
      runRawOpChecked st tr step.opName
        ((pickApi st poison).init p bare initBr?)
        (evalGitApi.init p bare initBr?)
    | .opClone s t opts poison =>
      let sp := resolveTarget st.rootDir s
      let tp := resolveTarget st.rootDir t
      match ← runRawOpChecked st tr step.opName
        ((pickApi st poison).clone sp tp opts)
        (evalGitApi.clone sp tp opts) with
      | .error e => return .error e
      | .ok (st1, tr1) =>
        if !opts.bare && pathHasSpecialMetadata st1.model tp then
          let st2 ← syncWorktreeTrackedDiskBytes st1 tp
          return .ok (st2, tr1)
        else
          return .ok (st1, tr1)
    | .opAdd t ps all poison =>
      let p := resolveTarget st.rootDir t
      let hasExtPath := ps.any isExtendedPathspec || (ps.foldl (fun n s => n + s.utf8ByteSize + 1) 0) > 65536
      let hasSpecial := !canNormalizeAddPathspecs st.model p ps all
      if !hasExtPath && !hasSpecial then
        runRawOpChecked st tr step.opName
          ((pickApi st poison).add p ps all)
          (evalGitApi.add p ps all)
      else
        let realRes ← (pickApi st poison).add p ps all
        let tr' := recordOutcome tr step.opName realRes
        let witnessIdx? ←
          if !hasSpecial then pure none
          else
            match realRes with
            | .ok () => resolveWitnessIndex? st p
            | .error _ =>
              if pathHasSpecialMetadata st.model p then resolveWitnessIndex? st p else pure none
        let (ok0, modelNext) := allowsAdd st.model p ps all witnessIdx? realRes
        let ok :=
          ok0 ||
          match realRes, (evalGitApi.add p ps all st.model).1 with
          | .error er, .error em => allowsCliErrorKind st.hasSpoofablePath em.kind er.kind && !er.message.isEmpty
          | _, _ => false
        if !ok then
          let (mRes, _) := stepAddWithWitness st.model p ps all witnessIdx?
          return .error (.mismatch s!"{step.opName}:relational"
            s!"add relational mismatch ps={repr ps} all={all}: real={repr realRes} model={repr mRes}")
        return .ok ({ st with model := modelNext }, tr')
    | .opCommit t opts poison =>
      let p := resolveTarget st.rootDir t
      let realRes ← (pickApi st poison).commit p opts
      let tr' := recordOutcome tr step.opName realRes
      match realRes with
      | .error eReal =>
        let (modelRes, modelNext) := stepCommitWithId st.model p opts none
        match compareExceptTagged step.opName (.error eReal : Except GitError CommitId) modelRes with
        | .error (tag, msg) => return .error (.mismatch tag msg)
        | .ok () => return .ok ({ st with model := modelNext }, tr')
      | .ok cidReal =>
        if !isValidCommitIdStr cidReal.hex then
          return .error (.mismatch "commit:invalid_cid" s!"commit returned invalid CommitId: '{cidReal.hex}'")
        let (modelRes, modelNext) := stepCommitWithId st.model p opts (some cidReal)
        match compareExceptTagged step.opName (.ok cidReal) modelRes with
        | .error (tag, msg) => return .error (.mismatch tag msg)
        | .ok () =>
          let realHead ← (pickApi st false).headCommit? p
          match realHead with
          | .ok (some c) =>
            if c != cidReal then
              return .error (.mismatch "commit:post_commit_head"
                s!"post-commit headCommit? mismatch: got {repr realHead}, expected some {cidReal.hex}")
            match ← verifyCommitObject st p cidReal opts with
            | .error terr => return .error terr
            | .ok () => return .ok (addKnownCommit { st with model := modelNext } cidReal, tr')
          | _ =>
            return .error (.mismatch "commit:post_commit_head"
              s!"post-commit headCommit? mismatch: got {repr realHead}, expected some {cidReal.hex}")
    | .opCreateBranch t br sp? force poison =>
      let p := resolveTarget st.rootDir t
      let spStr? := sp?.map (resolveRevSpec st)
      if !(spStr?.any isExtendedRevSpec) then
        runRawOpChecked st tr step.opName
          ((pickApi st poison).createBranch p br spStr? force)
          (evalGitApi.createBranch p br spStr? force)
      else
        let realRes ← (pickApi st poison).createBranch p br spStr? force
        let tr' := recordOutcome tr step.opName realRes
        let witnessCid? ←
          match realRes with
          | .ok () => resolveWitnessBranch? st p br
          | .error _ =>
            match spStr? with
            | some sp => if isValidStrictRevSpec sp then resolveWitnessRev? st p sp else pure none
            | none => pure none
        let (ok, modelNext) := allowsCreateBranch st.model p br spStr? force witnessCid? realRes
        if !ok then
          let (mRes, _) := stepCreateBranchWithWitness st.model p br spStr? force witnessCid?
          return .error (.mismatch s!"{step.opName}:relational"
            s!"createBranch relational mismatch sp={repr spStr?} witness={repr witnessCid?}: real={repr realRes} model={repr mRes}")
        let st' :=
          match witnessCid? with
          | some c => addKnownCommit { st with model := modelNext } c
          | none => { st with model := modelNext }
        return .ok (st', tr')
    | .opDeleteBranch t br force poison =>
      let p := resolveTarget st.rootDir t
      runRawOpChecked st tr step.opName
        ((pickApi st poison).deleteBranch p br force)
        (evalGitApi.deleteBranch p br force)
    | .opCheckout t coTgt force poison =>
      let p := resolveTarget st.rootDir t
      let tgt := resolveCheckoutTarget st coTgt
      let ext := match tgt with | .ref spec => isExtendedRevSpec spec | _ => false
      let special := targetTreeHasSpecial st p
      if !ext then
        let realRes ← (pickApi st poison).checkout p tgt force
        let (modelRes, modelNext) := evalGitApi.checkout p tgt force st.model
        let tr' := recordOutcome tr step.opName realRes
        match realRes, modelRes with
        | .ok (), .ok () =>
          let st1 := { st with model := modelNext }
          let st2 ← if special then syncWorktreeTrackedDiskBytes st1 p else pure st1
          return .ok (st2, tr')
        | .ok (), .error em =>
          if special && !force && em.kind == .dirtyWorktree then
            let (_, mForce) := evalGitApi.checkout p tgt true st.model
            let st1 ← syncWorktreeIndexFromWitness { st with model := mForce } p
            let st2 ← syncWorktreeTrackedDiskBytes st1 p
            return .ok (st2, tr')
          else
            match compareExceptTagged step.opName realRes modelRes st.hasSpoofablePath with
            | .error (tag, msg) => return .error (.mismatch tag msg)
            | .ok () => return .ok ({ st with model := modelNext }, tr')
        | .error er, .ok () =>
          if special && !force && er.kind == .dirtyWorktree && !er.message.isEmpty then
            return .ok (st, tr')
          else
            match compareExceptTagged step.opName realRes modelRes st.hasSpoofablePath with
            | .error (tag, msg) => return .error (.mismatch tag msg)
            | .ok () => return .ok ({ st with model := modelNext }, tr')
        | .error _, .error _ =>
          match compareExceptTagged step.opName realRes modelRes st.hasSpoofablePath with
          | .error (tag, msg) => return .error (.mismatch tag msg)
          | .ok () => return .ok ({ st with model := modelNext }, tr')
      else
        let realRes ← (pickApi st poison).checkout p tgt force
        let tr' := recordOutcome tr step.opName realRes
        let witnessCid? ←
          match realRes with
          | .ok () => resolveWitnessHead? st p
          | .error _ =>
            match tgt with
            | .ref spec => if isValidStrictRevSpec spec then resolveWitnessRev? st p spec else pure none
            | _ => pure none
        let witnessBr? ←
          match realRes with
          | .ok () => resolveWitnessHeadBranch? st p
          | .error _ =>
            match tgt with
            | .ref spec => if isValidStrictRevSpec spec then resolveWitnessSymbolicBranch? st p spec else pure none
            | _ => pure none
        let (ok, modelNext) := allowsCheckout st.model p tgt force witnessCid? realRes witnessBr?
        if ok then
          let st0 :=
            match witnessCid? with
            | some c => addKnownCommit { st with model := modelNext } c
            | none => { st with model := modelNext }
          let st1 ← if special && realRes.isOk then syncWorktreeTrackedDiskBytes st0 p else pure st0
          return .ok (st1, tr')
        else if special && !force then
          match realRes, (stepCheckoutWithWitness st.model p tgt force witnessCid? witnessBr?).1 with
          | .ok (), .error em =>
            if em.kind == .dirtyWorktree then
              let (_, mForce) := stepCheckoutWithWitness st.model p tgt true witnessCid? witnessBr?
              let st1 ← syncWorktreeIndexFromWitness { st with model := mForce } p
              let st2 ← syncWorktreeTrackedDiskBytes st1 p
              return .ok (match witnessCid? with | some c => addKnownCommit st2 c | none => st2, tr')
            else
              return .error (.mismatch s!"{step.opName}:relational"
                s!"checkout relational mismatch tgt={repr tgt} witness={repr witnessCid?} br={repr witnessBr?}: real={repr realRes} model={repr em}")
          | .error er, .ok () =>
            if er.kind == .dirtyWorktree && !er.message.isEmpty then
              return .ok (st, tr')
            else
              return .error (.mismatch s!"{step.opName}:relational"
                s!"checkout relational mismatch tgt={repr tgt} witness={repr witnessCid?} br={repr witnessBr?}: real={repr realRes} model=ok")
          | _, mRes =>
            return .error (.mismatch s!"{step.opName}:relational"
              s!"checkout relational mismatch tgt={repr tgt} witness={repr witnessCid?} br={repr witnessBr?}: real={repr realRes} model={repr mRes}")
        else
          let (mRes, _) := stepCheckoutWithWitness st.model p tgt force witnessCid? witnessBr?
          return .error (.mismatch s!"{step.opName}:relational"
            s!"checkout relational mismatch tgt={repr tgt} witness={repr witnessCid?} br={repr witnessBr?}: real={repr realRes} model={repr mRes}")
    | .opSwitch t br create sp? force poison =>
      let p := resolveTarget st.rootDir t
      let spStr? := sp?.map (resolveRevSpec st)
      let special := targetTreeHasSpecial st p
      if !(spStr?.any isExtendedRevSpec) then
        let realRes ← (pickApi st poison).switch p br create spStr? force
        let (modelRes, modelNext) := evalGitApi.switch p br create spStr? force st.model
        let tr' := recordOutcome tr step.opName realRes
        match realRes, modelRes with
        | .ok (), .ok () =>
          let st1 := { st with model := modelNext }
          let st2 ← if special then syncWorktreeTrackedDiskBytes st1 p else pure st1
          return .ok (st2, tr')
        | .ok (), .error em =>
          if special && !force && em.kind == .dirtyWorktree then
            let (_, mForce) := evalGitApi.switch p br create spStr? true st.model
            let st1 ← syncWorktreeIndexFromWitness { st with model := mForce } p
            let st2 ← syncWorktreeTrackedDiskBytes st1 p
            return .ok (st2, tr')
          else
            match compareExceptTagged step.opName realRes modelRes st.hasSpoofablePath with
            | .error (tag, msg) => return .error (.mismatch tag msg)
            | .ok () => return .ok ({ st with model := modelNext }, tr')
        | .error er, .ok () =>
          if special && !force && er.kind == .dirtyWorktree && !er.message.isEmpty then
            return .ok (st, tr')
          else
            match compareExceptTagged step.opName realRes modelRes st.hasSpoofablePath with
            | .error (tag, msg) => return .error (.mismatch tag msg)
            | .ok () => return .ok ({ st with model := modelNext }, tr')
        | .error _, .error _ =>
          match compareExceptTagged step.opName realRes modelRes st.hasSpoofablePath with
          | .error (tag, msg) => return .error (.mismatch tag msg)
          | .ok () => return .ok ({ st with model := modelNext }, tr')
      else
        let realRes ← (pickApi st poison).switch p br create spStr? force
        let tr' := recordOutcome tr step.opName realRes
        let witnessCid? ←
          match realRes with
          | .ok () => resolveWitnessHead? st p
          | .error _ =>
            match spStr? with
            | some sp => if create && isValidStrictRevSpec sp then resolveWitnessRev? st p sp else pure none
            | none => pure none
        let (ok, modelNext) := allowsSwitch st.model p br create spStr? force witnessCid? realRes
        if ok then
          let st0 :=
            match witnessCid? with
            | some c => addKnownCommit { st with model := modelNext } c
            | none => { st with model := modelNext }
          let st1 ← if special && realRes.isOk then syncWorktreeTrackedDiskBytes st0 p else pure st0
          return .ok (st1, tr')
        else if special && !force then
          match realRes, (stepSwitchWithWitness st.model p br create spStr? force witnessCid?).1 with
          | .ok (), .error em =>
            if em.kind == .dirtyWorktree then
              let (_, mForce) := stepSwitchWithWitness st.model p br create spStr? true witnessCid?
              let st1 ← syncWorktreeIndexFromWitness { st with model := mForce } p
              let st2 ← syncWorktreeTrackedDiskBytes st1 p
              return .ok (match witnessCid? with | some c => addKnownCommit st2 c | none => st2, tr')
            else
              return .error (.mismatch s!"{step.opName}:relational"
                s!"switch relational mismatch sp={repr spStr?} witness={repr witnessCid?}: real={repr realRes} model={repr em}")
          | .error er, .ok () =>
            if er.kind == .dirtyWorktree && !er.message.isEmpty then
              return .ok (st, tr')
            else
              return .error (.mismatch s!"{step.opName}:relational"
                s!"switch relational mismatch sp={repr spStr?} witness={repr witnessCid?}: real={repr realRes} model=ok")
          | _, mRes =>
            return .error (.mismatch s!"{step.opName}:relational"
              s!"switch relational mismatch sp={repr spStr?} witness={repr witnessCid?}: real={repr realRes} model={repr mRes}")
        else
          let (mRes, _) := stepSwitchWithWitness st.model p br create spStr? force witnessCid?
          return .error (.mismatch s!"{step.opName}:relational"
            s!"switch relational mismatch sp={repr spStr?} witness={repr witnessCid?}: real={repr realRes} model={repr mRes}")
    | .opReset t mode rev poison =>
      let p := resolveTarget st.rootDir t
      let revStr := resolveRevSpec st rev
      let special := targetTreeHasSpecial st p
      if !isExtendedRevSpec revStr then
        match ← runRawOpChecked st tr step.opName
          ((pickApi st poison).reset p mode revStr)
          (evalGitApi.reset p mode revStr) with
        | .error e => return .error e
        | .ok (st1, tr1) =>
          if special && mode == .hard then
            let st2 ← syncWorktreeTrackedDiskBytes st1 p
            return .ok (st2, tr1)
          else
            return .ok (st1, tr1)
      else
        let realRes ← (pickApi st poison).reset p mode revStr
        let tr' := recordOutcome tr step.opName realRes
        let witnessCid? ←
          match realRes with
          | .ok () => resolveWitnessHead? st p
          | .error _ => if isValidStrictRevSpec revStr then resolveWitnessRev? st p revStr else pure none
        let (ok, modelNext) := allowsReset st.model p mode revStr witnessCid? realRes
        if !ok then
          let (mRes, _) := stepResetWithWitness st.model p mode revStr witnessCid?
          return .error (.mismatch s!"{step.opName}:relational"
            s!"reset relational mismatch rev='{revStr}' witness={repr witnessCid?}: real={repr realRes} model={repr mRes}")
        let st0 :=
          match witnessCid? with
          | some c => addKnownCommit { st with model := modelNext } c
          | none => { st with model := modelNext }
        let st1 ← if special && mode == .hard && realRes.isOk then syncWorktreeTrackedDiskBytes st0 p else pure st0
        return .ok (st1, tr')
    | .opFetch t rem rs? prune poison =>
      let p := resolveTarget st.rootDir t
      runRawOpChecked st tr step.opName
        ((pickApi st poison).fetch p rem rs? prune)
        (evalGitApi.fetch p rem rs? prune)
    | .opWorktreeAdd t wtTgt rev? nb? detach force poison =>
      let p := resolveTarget st.rootDir t
      let wtP := resolveTarget st.rootDir wtTgt
      let opts : WorktreeAddOptions := {
        path := wtP
        target? := rev?.map (resolveRevSpec st)
        newBranch? := nb?
        detach := detach
        force := force
      }
      if !(opts.target?.any isExtendedRevSpec) && !isAmbiguousHexBranchTarget st.model p opts then
        match ← runRawOpChecked st tr step.opName
          ((pickApi st poison).worktreeAdd p opts)
          (evalGitApi.worktreeAdd p opts) with
        | .error e => return .error e
        | .ok (st1, tr1) =>
          if pathHasSpecialMetadata st1.model wtP then
            let st2 ← syncWorktreeTrackedDiskBytes st1 wtP
            return .ok (st2, tr1)
          else
            return .ok (st1, tr1)
      else
        let realRes ← (pickApi st poison).worktreeAdd p opts
        let tr' := recordOutcome tr step.opName realRes
        let witnessCid? ←
          match realRes with
          | .ok () => resolveWitnessHead? st wtP
          | .error _ =>
            match opts.target? with
            | some tgt => if isValidStrictRevSpec tgt then resolveWitnessRev? st p tgt else pure none
            | none => pure none
        let witnessBr? ←
          match realRes with
          | .ok () => resolveWitnessHeadBranch? st wtP
          | .error _ =>
            match opts.target? with
            | some tgt => if isValidStrictRevSpec tgt then resolveWitnessSymbolicBranch? st p tgt else pure none
            | none => pure none
        let (ok, modelNext) := allowsWorktreeAdd st.model p opts witnessCid? realRes witnessBr?
        if !ok then
          let (mRes, _) := stepWorktreeAddWithWitness st.model p opts witnessCid? witnessBr?
          return .error (.mismatch s!"{step.opName}:relational"
            s!"worktreeAdd relational mismatch target={repr opts.target?} witness={repr witnessCid?} br={repr witnessBr?}: real={repr realRes} model={repr mRes}")
        let st0 :=
          match witnessCid? with
          | some c => addKnownCommit { st with model := modelNext } c
          | none => { st with model := modelNext }
        let st' ← if realRes.isOk && pathHasSpecialMetadata st0.model wtP then syncWorktreeTrackedDiskBytes st0 wtP else pure st0
        return .ok (st', tr')
    | .opWorktreeRemove t wtTgt force poison =>
      let p := resolveTarget st.rootDir t
      let wtP := resolveTarget st.rootDir wtTgt
      let realRes ← (pickApi st poison).worktreeRemove p wtP force
      let (modelRes, modelNext) := evalGitApi.worktreeRemove p wtP force st.model
      let tr' := recordOutcome tr step.opName realRes
      let special := pathHasSpecialMetadata st.model wtP
      match realRes, modelRes with
      | .ok (), .error em =>
        if !force && special && em.kind == .dirtyWorktree then
          let (_, mForce) := evalGitApi.worktreeRemove p wtP true st.model
          return .ok ({ st with model := mForce }, tr')
        else
          match compareExceptTagged step.opName realRes modelRes st.hasSpoofablePath with
          | .error (tag, msg) => return .error (.mismatch tag msg)
          | .ok () => return .ok ({ st with model := modelNext }, tr')
      | .error er, .ok () =>
        if !force && special && er.kind == .dirtyWorktree && !er.message.isEmpty then
          return .ok (st, tr')
        else
          match compareExceptTagged step.opName realRes modelRes st.hasSpoofablePath with
          | .error (tag, msg) => return .error (.mismatch tag msg)
          | .ok () => return .ok ({ st with model := modelNext }, tr')
      | _, _ =>
        match compareExceptTagged step.opName realRes modelRes st.hasSpoofablePath with
        | .error (tag, msg) => return .error (.mismatch tag msg)
        | .ok () => return .ok ({ st with model := modelNext }, tr')
    | .opWithWorktree t wtTgt rev? nb? detach force ins retErr poison =>
      let p := resolveTarget st.rootDir t
      let wtP := resolveTarget st.rootDir wtTgt
      let opts : WorktreeAddOptions := {
        path := wtP
        target? := rev?.map (resolveRevSpec st)
        newBranch? := nb?
        detach := detach
        force := force
      }
      let ext := opts.target?.any isExtendedRevSpec
      let wtWitness? ←
        if ext then
          match opts.target? with
          | some tgt => if isValidStrictRevSpec tgt then resolveWitnessRev? st p tgt else pure none
          | none => pure none
        else pure none
      let wtBrWitness? ←
        if ext then
          match opts.target? with
          | some tgt => if isValidStrictRevSpec tgt then resolveWitnessSymbolicBranch? st p tgt else pure none
          | none => pure none
        else pure none
      let (modelAddRes, sAfterAdd) := stepWorktreeAddWithWitness st.model p opts wtWitness? wtBrWitness?
      let stRef ← IO.mkRef { st with model := sAfterAdd }
      let trRef ← IO.mkRef tr
      let innerErrRef ← IO.mkRef (none : Option TraceError)
      let realRes ← (pickApi st poison).withWorktree p opts fun _ => do
        match modelAddRes with
        | .error e =>
          innerErrRef.set (some (.mismatch "withWorktree:ok_vs_err_add"
            s!"withWorktree entered action on real git while model rejected worktreeAdd: {repr e}"))
          return .error { kind := .commandFailed, message := "model rejected worktreeAdd" }
        | .ok () =>
          for inner in ins do
            let curSt ← stRef.get
            let curTr ← trRef.get
            match ← execStepFuel fuel' curSt curTr inner with
            | .error terr =>
              innerErrRef.set (some terr)
              return .error { kind := .commandFailed, message := s!"inner error: {repr terr}" }
            | .ok (nxtSt, nxtTr) =>
              stRef.set nxtSt
              trRef.set nxtTr
          if retErr then
            return .error { kind := .invalidInput, message := "injected inner error" }
          else
            return .ok ()
      let innerErr? ← innerErrRef.get
      if let some terr := innerErr? then
        return .error terr
      let curSt ← stRef.get
      let curTr ← trRef.get
      let modelFinal : Except GitError Unit × GitRepoState :=
        match modelAddRes with
        | .error e => (.error e, sAfterAdd)
        | .ok () =>
          let sBase := { curSt.model with vfs := curSt.model.vfs, repos := curSt.model.repos }
          let (cleanRes, sAfterRem) := evalGitApi.worktreeRemove p wtP force sBase
          let actRes : Except GitError Unit :=
            if retErr then .error { kind := .invalidInput, message := "injected inner error" } else .ok ()
          match actRes, cleanRes with
          | .ok (), .ok () => (.ok (), sAfterRem)
          | .ok (), .error ce => (.error ce, sAfterRem)
          | .error ae, _ => (.error ae, sAfterRem)
      let tr' := recordOutcome curTr step.opName realRes
      if (ext || isAmbiguousHexBranchTarget st.model p opts) && !modelAddRes.isOk then
        let (ok, sFin) := allowsWorktreeAdd st.model p opts wtWitness? realRes wtBrWitness?
        if !ok then
          return .error (.mismatch s!"{step.opName}:relational"
            s!"withWorktree add relational mismatch: real={repr realRes} model={repr modelFinal.1}")
        return .ok ({ curSt with model := sFin }, tr')
      else if modelAddRes.isOk && !force && !retErr && pathHasSpecialMetadata curSt.model wtP then
        match realRes, modelFinal.1 with
        | .ok (), .error em =>
          if em.kind == .dirtyWorktree then
            let (_, mForce) := evalGitApi.worktreeRemove p wtP true curSt.model
            return .ok ({ curSt with model := mForce }, tr')
          else
            match compareExceptTagged step.opName realRes modelFinal.1 curSt.hasSpoofablePath with
            | .error (tag, msg) => return .error (.mismatch tag msg)
            | .ok () => return .ok ({ curSt with model := modelFinal.2 }, tr')
        | .error er, .ok () =>
          if er.kind == .dirtyWorktree && !er.message.isEmpty then
            return .ok (curSt, tr')
          else
            match compareExceptTagged step.opName realRes modelFinal.1 curSt.hasSpoofablePath with
            | .error (tag, msg) => return .error (.mismatch tag msg)
            | .ok () => return .ok ({ curSt with model := modelFinal.2 }, tr')
        | _, _ =>
          match compareExceptTagged step.opName realRes modelFinal.1 curSt.hasSpoofablePath with
          | .error (tag, msg) => return .error (.mismatch tag msg)
          | .ok () => return .ok ({ curSt with model := modelFinal.2 }, tr')
      else
        match compareExceptTagged step.opName realRes modelFinal.1 curSt.hasSpoofablePath with
        | .error (tag, msg) => return .error (.mismatch tag msg)
        | .ok () => return .ok ({ curSt with model := modelFinal.2 }, tr')
    | .opTimeoutProbe t probeOp =>
      let candPath := resolveTarget st.rootDir t
      let probeDir :=
        if !candPath.isEmpty && !candPath.toList.contains '\x00' && candPath.startsWith "/" &&
            isLiveSearchableDir st.model.vfs (splitByteSlash candPath.toUTF8) then
          candPath
        else
          st.cwdDir
      let hangApi := Impl.mkApiM (hangGitRawOps st.rootDir st.cwdDir 25)
      let res : Except GitError Unit ←
        match probeOp % 4 with
        | 0 => (hangApi.status probeDir).map fun r => r.map (fun _ => ())
        | 1 => (hangApi.headState probeDir).map fun r => r.map (fun _ => ())
        | 2 => (hangApi.listWorktrees probeDir).map fun r => r.map (fun _ => ())
        | _ => (hangApi.revParseCommit probeDir "HEAD").map fun r => r.map (fun _ => ())
      let tr' := recordOutcome tr step.opName res
      match res with
      | .error e =>
        if e.kind == .timeout && !e.message.isEmpty then
          return .ok (st, tr')
        else
          return .error (.mismatch s!"timeoutProbe:err:{errorKindLabel e.kind}"
            s!"timeoutProbe expected .timeout on {probeDir} (op={probeOp % 4}), got {repr e}")
      | .ok () =>
        return .error (.mismatch "timeoutProbe:ok_vs_timeout"
          s!"timeoutProbe unexpectedly succeeded on {probeDir} (op={probeOp % 4})")

/-- Execute one `GitFuzzStep` against both real `LeanSwe.Git` and `GitRepoState`, returning any mismatch or infra error. -/
def execStep (st0 : EpisodeState) (tr : CoverageTracker) (step : GitFuzzStep) :
    IO (Except TraceError (EpisodeState × CoverageTracker)) :=
  execStepFuel 8 st0 tr step

/-- Cross-check `headState`, `headBranch?`, `status`, and `listWorktrees` across every live `RepoInstance` (including bare-repo linked worktrees). -/
def auditLiveState (st : EpisodeState) : IO (Except TraceError Unit) := do
  let api := pickApi st false
  for repo in st.model.repos do
    let repoTarget? :=
      if repo.isBare then String.fromUTF8? repo.commonDir
      else repo.worktrees.head?.bind (fun w => String.fromUTF8? w.rootPath)
    if let some repoPath := repoTarget? then
      let realWt ← api.listWorktrees repoPath
      let (modWt, _) := evalGitApi.listWorktrees repoPath st.model
      match compareWorktreesTagged "audit.listWorktrees" realWt modWt with
      | .error (tag, msg) => return .error (.mismatch s!"audit:{tag}" msg)
      | .ok () => pure ()
      if repo.isBare then
        let realHs ← api.headState repoPath
        let (modHs, _) := evalGitApi.headState repoPath st.model
        match compareExceptTagged "audit.bare.headState" realHs modHs with
        | .error (tag, msg) => return .error (.mismatch s!"audit:{tag}" msg)
        | .ok () => pure ()
        for wt in repo.worktrees.drop 1 do
          if !wt.isPrunable && isLiveDirAtParts st.model.vfs (splitByteSlash wt.rootPath) then
            if let some wtStr := String.fromUTF8? wt.rootPath then
              let realHs ← api.headState wtStr
              let (modHs, _) := evalGitApi.headState wtStr st.model
              match compareExceptTagged "audit.bare.wt.headState" realHs modHs with
              | .error (tag, msg) => return .error (.mismatch s!"audit:{tag}" msg)
              | .ok () => pure ()
              let realBr ← api.headBranch? wtStr
              let (modBr, _) := evalGitApi.headBranch? wtStr st.model
              match compareExceptTagged "audit.bare.wt.headBranch" realBr modBr with
              | .error (tag, msg) => return .error (.mismatch s!"audit:{tag}" msg)
              | .ok () => pure ()
              let realSt ← api.status wtStr
              if !allowsStatus st.model wtStr realSt then
                let (modSt, _) := evalGitApi.status wtStr st.model
                match compareExceptTagged "audit.bare.wt.status" realSt modSt with
                | .error (tag, msg) => return .error (.mismatch s!"audit:{tag}" msg)
                | .ok () => return .error (.mismatch "audit:audit.bare.wt.status:ok" s!"audit.bare.wt.status relational mismatch: real={repr realSt} model={repr modSt}")
      else
        for wt in repo.worktrees do
          if !wt.isPrunable && isLiveDirAtParts st.model.vfs (splitByteSlash wt.rootPath) then
            if let some wtStr := String.fromUTF8? wt.rootPath then
              let realHs ← api.headState wtStr
              let (modHs, _) := evalGitApi.headState wtStr st.model
              match compareExceptTagged "audit.headState" realHs modHs with
              | .error (tag, msg) => return .error (.mismatch s!"audit:{tag}" msg)
              | .ok () => pure ()
              let realSt ← api.status wtStr
              if !allowsStatus st.model wtStr realSt then
                let (modSt, _) := evalGitApi.status wtStr st.model
                match compareExceptTagged "audit.status" realSt modSt with
                | .error (tag, msg) => return .error (.mismatch s!"audit:{tag}" msg)
                | .ok () => return .error (.mismatch "audit:audit.status:ok" s!"audit.status relational mismatch: real={repr realSt} model={repr modSt}")
  return .ok ()

private def restoreAllChmodDirs (rootDir : String) (dirs : Array String) (rawDirs : Array ByteArray)
    (files : Array String) (rawFiles : Array ByteArray) (cleanNonUtf8 : Bool) : IO Unit := do
  let sorted := dirs.qsort (fun a b => a.length < b.length)
  let sortedRaw := rawDirs.qsort (fun a b => a.size < b.size)
  for sl in [SlotId.repoA, SlotId.repoB, SlotId.subDir, SlotId.wt2, SlotId.wt1, SlotId.bareWt, SlotId.cloneRepo] do
    let _ ← LeanSwe.Fs.chmod s!"{rootDir}/{sl.relPath}" 0o755
  for d in sorted do
    let _ ← LeanSwe.Fs.chmod d 0o755
  for rawD in sortedRaw do
    let py :=
      "import os, sys\n" ++
      "p = bytes.fromhex(sys.argv[1])\n" ++
      "try:\n" ++
      "    os.chmod(p, 0o755)\n" ++
      "except OSError:\n" ++
      "    pass\n"
    let _ ← runPythonFs py #[byteArrayToHex rawD]
  for f in files do
    let _ ← LeanSwe.Fs.chmod f 0o644
  for rawF in rawFiles do
    let py :=
      "import os, sys\n" ++
      "p = bytes.fromhex(sys.argv[1])\n" ++
      "try:\n" ++
      "    os.chmod(p, 0o644)\n" ++
      "except OSError:\n" ++
      "    pass\n"
    let _ ← runPythonFs py #[byteArrayToHex rawF]
  if cleanNonUtf8 then
    let pyClean :=
      "import os, shutil, sys\n" ++
      "root = sys.argv[1].encode('utf-8')\n" ++
      "def chmod_tree(d):\n" ++
      "    try:\n" ++
      "        os.chmod(d, 0o755)\n" ++
      "    except OSError:\n" ++
      "        return\n" ++
      "    try:\n" ++
      "        subs = os.listdir(d)\n" ++
      "    except OSError:\n" ++
      "        return\n" ++
      "    for s in subs:\n" ++
      "        sp = os.path.join(d, s)\n" ++
      "        if not os.path.islink(sp) and os.path.isdir(sp):\n" ++
      "            chmod_tree(sp)\n" ++
      "def clean(d):\n" ++
      "    try:\n" ++
      "        os.chmod(d, 0o755)\n" ++
      "    except OSError:\n" ++
      "        pass\n" ++
      "    try:\n" ++
      "        entries = os.listdir(d)\n" ++
      "    except OSError:\n" ++
      "        return\n" ++
      "    for name in entries:\n" ++
      "        full = os.path.join(d, name)\n" ++
      "        try:\n" ++
      "            name.decode('utf-8')\n" ++
      "            is_utf8 = True\n" ++
      "        except UnicodeDecodeError:\n" ++
      "            is_utf8 = False\n" ++
      "        if not is_utf8:\n" ++
      "            if os.path.islink(full) or not os.path.isdir(full):\n" ++
      "                try:\n" ++
      "                    os.unlink(full)\n" ++
      "                except OSError:\n" ++
      "                    pass\n" ++
      "            else:\n" ++
      "                chmod_tree(full)\n" ++
      "                shutil.rmtree(full, ignore_errors=True)\n" ++
      "        elif os.path.isdir(full) and not os.path.islink(full):\n" ++
      "            clean(full)\n" ++
      "clean(root)\n"
    let _ ← runPythonFs pyClean #[rootDir]

/-- Execute a full trace inside a fresh `TempDir`, running periodic and final readback audits. -/
def runTrace (tr : CoverageTracker) (trace : Array GitFuzzStep)
    (extraAuditEvery : Nat := 8) (pinnedAuditTag? : Option String := none) :
    IO (Except TraceError CoverageTracker) := do
  let runFinalAndPeriodicAudit :=
    match pinnedAuditTag? with
    | none => true
    | some want => want.startsWith "audit:"
  let innerRef ← IO.mkRef (none : Option (Except TraceError CoverageTracker))
  let res ← LeanSwe.TempDir.withTempDir none "leanswe-git-fuzz-" fun rawDir => do
    match ← initEpisodeState rawDir with
    | .error msg =>
      let errRes := Except.error (.infra msg)
      innerRef.set (some errRes)
      return .ok errRes
    | .ok st0 =>
      let chmodRef ← IO.mkRef (#[] : Array String)
      let chmodRawRef ← IO.mkRef (#[] : Array ByteArray)
      let chmodFileRef ← IO.mkRef (#[] : Array String)
      let chmodRawFileRef ← IO.mkRef (#[] : Array ByteArray)
      let nonUtf8Ref ← IO.mkRef false
      let walkChmodRef ← IO.mkRef false
      let mut cur := st0
      let mut curTr := tr
      try
        let mut idx := 0
        for step in trace do
          if stepMayCreateNonUtf8 step then
            nonUtf8Ref.set true
          if stepMayChmod step then
            walkChmodRef.set true
          match ← execStep cur curTr step with
          | .error (.infra msg) =>
            let errRes := Except.error (.infra s!"step[{idx}] ({step.opName}): {msg}")
            innerRef.set (some errRes)
            return .ok errRes
          | .error (.mismatch tag msg) =>
            let errRes := Except.error (.mismatch tag s!"step[{idx}] ({step.opName}): {msg}")
            innerRef.set (some errRes)
            return .ok errRes
          | .ok (nxt, nxtTr) =>
            cur := nxt
            chmodRef.set nxt.chmodDirs
            chmodRawRef.set nxt.chmodRawDirs
            chmodFileRef.set nxt.chmodFiles
            chmodRawFileRef.set nxt.chmodRawFiles
            if nxt.hasBadUtf8Fixture || nxt.hasNonUtf8OnDisk then
              nonUtf8Ref.set true
            curTr := nxtTr
            idx := idx + 1
            if runFinalAndPeriodicAudit && extraAuditEvery > 0 && idx % extraAuditEvery == 0 then
              match ← auditLiveState cur with
              | .error (.infra msg) =>
                let errRes := Except.error (.infra s!"step[{idx}] audit: {msg}")
                innerRef.set (some errRes)
                return .ok errRes
              | .error (.mismatch tag msg) =>
                let shouldStop :=
                  match pinnedAuditTag? with
                  | none => true
                  | some want => tag == want
                if shouldStop then
                  let errRes := Except.error (.mismatch tag s!"step[{idx}] audit: {msg}")
                  innerRef.set (some errRes)
                  return .ok errRes
              | .ok () => pure ()
        if runFinalAndPeriodicAudit then
          match ← auditLiveState cur with
          | .error (.infra msg) =>
            let errRes := Except.error (.infra s!"final audit: {msg}")
            innerRef.set (some errRes)
            return .ok errRes
          | .error (.mismatch tag msg) =>
            let errRes := Except.error (.mismatch tag s!"final audit: {msg}")
            innerRef.set (some errRes)
            return .ok errRes
          | .ok () =>
            let okRes := Except.ok curTr
            innerRef.set (some okRes)
            return .ok okRes
        else
          let okRes := Except.ok curTr
          innerRef.set (some okRes)
          return .ok okRes
      finally
        let dirs ← chmodRef.get
        let rawDirs ← chmodRawRef.get
        let files ← chmodFileRef.get
        let rawFiles ← chmodRawFileRef.get
        let hasNonUtf8 ← nonUtf8Ref.get
        let walkChmod ← walkChmodRef.get
        restoreAllChmodDirs st0.rootDir dirs rawDirs files rawFiles (hasNonUtf8 || walkChmod)
  match res with
  | .error e => return .error (.infra s!"TempDir failed: {e.message}")
  | .ok inner =>
    match ← innerRef.get with
    | some r => return r
    | none => return inner

/-- Execute a trace and assert success, shrinking semantic mismatches while preserving exact failure tag. -/
def runTraceOrShrink (seedVal : UInt64) (tr : CoverageTracker) (trace : Array GitFuzzStep) :
    IO CoverageTracker := do
  match ← runTrace tr trace 8 none with
  | .ok tr' => return tr'
  | .error (.infra msg) =>
    throw (IO.userError s!"GIT_FUZZ_INFRA_ERROR SEED={seedVal}: {msg}")
  | .error (.mismatch origTag msg) =>
    let shrinkAuditEvery := if origTag.startsWith "audit:" then 1 else 0
    let fails (cand : Array GitFuzzStep) : IO Bool := do
      match ← runTrace CoverageTracker.empty cand shrinkAuditEvery (some origTag) with
      | .ok _ => return false
      | .error (.infra _) => return false
      | .error (.mismatch tag' _) => return tag' == origTag
    let mut cur ← shrinkTrace fails trace
    for _ in List.range 6 do
      let mut spliced := cur
      for cand in spliceWithWorktreeSteps cur do
        if ← fails cand then
          spliced ← shrinkTrace fails cand
          break
      let elShrunk ← shrinkElements shrinkStep fails spliced
      let nxt ← shrinkTrace fails elShrunk
      if nxt == cur then
        break
      cur := nxt
    throw (IO.userError
      s!"GIT_FUZZ_MISMATCH SEED={seedVal} TAG={origTag}: {msg}\nMINIMAL_TRACE ({cur.size} steps): {repr cur}")

end Fuzz.Git
