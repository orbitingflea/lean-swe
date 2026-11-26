import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Fs.Interface
import LeanSwe.Process.Interface
import LeanSwe.TempDir.Interface
import Fuzz.Common.Coverage
import Fuzz.Common.Shrink
import Fuzz.Common.Suite
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
  /-- Whether observed real `LeanSwe.Git` errors should emit `ERR_HIT` coverage records. -/
  emitErrHits : Bool := false

/-- Helper `stripTrailingSlash`. -/
def stripTrailingSlash (p : String) : String :=
  if p.length > 1 && p.endsWith "/" then p.dropEnd 1 |>.toString else p

/-- Helper `poisonEnvPairs`. -/
def poisonEnvPairs : Array (String × String) := #[
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

/-- Helper `scopedRawOps`. -/
def scopedRawOps (rootDir cwdDir : String) (poison : Bool) : RawGitOps :=
  let fuzzHome := s!"{rootDir}/_fuzz_home"
  let fuzzXdg := s!"{rootDir}/_fuzz_xdg"
  let extraPoison := poisonEnvPairs
  { listEnv := do
      match ← defaultOps.listEnv with
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
      defaultOps.execGit effectiveEnv { req with cwd := effectiveCwd } }

/-- Helper `hangGitRawOps`. -/
def hangGitRawOps (rootDir cwdDir : String) (ms : Nat) : RawGitOps :=
  let base := scopedRawOps rootDir cwdDir false
  { listEnv := base.listEnv
    execGit := fun envOverrides req =>
      base.execGit envOverrides
        { req with
          args := #["-c", "alias.fuzzhang=!sleep 5", "fuzzhang"]
          timeoutMs := some ms } }

/-- Helper `pickApi`. -/
def pickApi (st : EpisodeState) (poison : Bool) : GitApi :=
  Impl.mkApiM (scopedRawOps st.rootDir st.cwdDir poison)

/-- Helper `resolveTarget`. -/
def resolveTarget (root : String) : PathTarget → String
  | .slot s => s!"{root}/{s.relPath}"
  | .raw p => p
  | .subRel parent rel => s!"{root}/{parent.relPath}/{rel}"
  | .fileUrl s => s!"file://{root}/{s.relPath}"
  | .fileUrlLocalhost s => s!"file://localhost{root}/{s.relPath}"

/-- Helper `resolveRevSpec`. -/
def resolveRevSpec (st : EpisodeState) : FuzzRevSpec → String
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

/-- Helper `resolveCommitIdx`. -/
def resolveCommitIdx (st : EpisodeState) (idx : Nat) (raw? : Option String) : CommitId :=
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

/-- Helper `resolveCheckoutTarget`. -/
def resolveCheckoutTarget (st : EpisodeState) : FuzzCheckoutTarget → CheckoutTarget
  | .branch b => .branch b
  | .commitIdx idx raw? => .commit (resolveCommitIdx st idx raw?)
  | .ref spec => .ref (resolveRevSpec st spec)

/-- Helper `upsertChildInListAux`. -/
def upsertChildInListAux (seg : ByteArray) (node : VfsNode)
    (revAcc : List (ByteArray × VfsNode)) :
    List (ByteArray × VfsNode) → List (ByteArray × VfsNode)
  | [] => ((seg, node) :: revAcc).reverse
  | (k, v) :: rest =>
    if k == seg then revAcc.reverse ++ ((seg, node) :: rest)
    else upsertChildInListAux seg node ((k, v) :: revAcc) rest

/-- Helper `upsertChildInList`. -/
def upsertChildInList (seg : ByteArray) (node : VfsNode)
    (xs : List (ByteArray × VfsNode)) : List (ByteArray × VfsNode) :=
  upsertChildInListAux seg node [] xs

/-- Helper `eraseChildInListAux`. -/
def eraseChildInListAux (seg : ByteArray) (revAcc : List (ByteArray × VfsNode)) :
    List (ByteArray × VfsNode) → List (ByteArray × VfsNode)
  | [] => revAcc.reverse
  | (k, v) :: rest =>
    if k == seg then eraseChildInListAux seg revAcc rest
    else eraseChildInListAux seg ((k, v) :: revAcc) rest

/-- Helper `eraseChildInList`. -/
def eraseChildInList (seg : ByteArray) (xs : List (ByteArray × VfsNode)) :
    List (ByteArray × VfsNode) :=
  eraseChildInListAux seg [] xs

/-- Helper `vfsPutChild`. -/
def vfsPutChild (vfs : VfsNode) (parentParts : List ByteArray) (seg : ByteArray) (child : VfsNode) :
    VfsNode :=
  updateNodeAtParts vfs parentParts fun
    | .dir s w cs => .dir s w (upsertChildInList seg child cs)
    | other => other

/-- Helper `vfsDropChild`. -/
def vfsDropChild (vfs : VfsNode) (parentParts : List ByteArray) (seg : ByteArray) : VfsNode :=
  updateNodeAtParts vfs parentParts fun
    | .dir s w cs => .dir s w (eraseChildInList seg cs)
    | other => other

/-- Helper `byteArrayToHex`. -/
def byteArrayToHex (bs : ByteArray) : String := Id.run do
  let hexDigits : Array Char := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  let mut out := ""
  for i in List.range bs.size do
    let b := bs[i]!.toNat
    out := out.push hexDigits[b / 16]! |>.push hexDigits[b % 16]!
  return out

/-- Helper `runPythonFs`. -/
def runPythonFs (script : String) (args : Array String) : IO (Except String Unit) := do
  let res ← LeanSwe.Process.run { program := "python3", args := #["-c", script] ++ args }
  match res with
  | .error e => return .error e.message
  | .ok out =>
    if out.exitCode == 0 then return .ok ()
    else return .error ((String.fromUTF8? out.stderr).getD s!"python exited {out.exitCode}")

/-- Helper `hasBadUtf8Target`. -/
def hasBadUtf8Target : PathTarget → Bool
  | .slot .badUtf8Dir => true
  | .subRel .badUtf8Dir _ => true
  | .fileUrl .badUtf8Dir => true
  | .fileUrlLocalhost .badUtf8Dir => true
  | _ => false

mutual
/-- Helper `stepMentionsBadUtf8`. -/
def stepMentionsBadUtf8 : GitFuzzStep → Bool
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

/-- Helper `stepsMentionBadUtf8`. -/
def stepsMentionBadUtf8 : List GitFuzzStep → Bool
  | [] => false
  | s :: rest => stepMentionsBadUtf8 s || stepsMentionBadUtf8 rest
end

mutual
/-- Helper `stepMayCreateNonUtf8`. -/
def stepMayCreateNonUtf8 : GitFuzzStep → Bool
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

/-- Helper `stepsMayCreateNonUtf8`. -/
def stepsMayCreateNonUtf8 : List GitFuzzStep → Bool
  | [] => false
  | s :: rest => stepMayCreateNonUtf8 s || stepsMayCreateNonUtf8 rest
end

mutual
/-- Helper `stepMayChmod`. -/
def stepMayChmod : GitFuzzStep → Bool
  | .vfsChmodDir _ false => true
  | .vfsChmodSubDir _ _ false => true
  | .opWithWorktree _ _ _ _ _ _ ins _ _ => stepsMayChmod ins
  | _ => false

/-- Helper `stepsMayChmod`. -/
def stepsMayChmod : List GitFuzzStep → Bool
  | [] => false
  | s :: rest => stepMayChmod s || stepsMayChmod rest
end

/-- Helper `ensureBadUtf8Fixture`. -/
def ensureBadUtf8Fixture (st : EpisodeState) : IO (Except String EpisodeState) := do
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

/-- Helper `initEpisodeState`. -/
def initEpisodeState (rawDir : String) : IO (Except String EpisodeState) := do
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


end Fuzz.Git
