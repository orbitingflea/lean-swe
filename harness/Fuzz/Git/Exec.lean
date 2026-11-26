import Fuzz.Git.Exec.Core
import Fuzz.Git.Exec.Vfs
import Fuzz.Git.Exec.Fixtures
import Fuzz.Git.Exec.Witness
import Fuzz.Git.Exec.StepA
import Fuzz.Git.Exec.StepB

namespace Fuzz.Git

open Fuzz.Common
open LeanSwe.Git
open LeanSwe.Git.Model

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
    match ← execStepPartA st tr step with
    | some res => return res
    | none => execStepPartB (execStepFuel fuel') st tr step

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
    (extraAuditEvery : Nat := 8) (pinnedAuditTag? : Option String := none)
    (emitErrHits : Bool := false) :
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
      let mut cur := { st0 with emitErrHits }
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
  match ← runTrace tr trace 8 none true with
  | .ok tr' => return tr'
  | .error (.infra msg) =>
    throw (IO.userError s!"GIT_FUZZ_INFRA_ERROR SEED={seedVal}: {msg}")
  | .error (.mismatch origTag msg) =>
    let shrinkAuditEvery := if origTag.startsWith "audit:" then 1 else 0
    let fails (cand : Array GitFuzzStep) : IO Bool := do
      match ← runTrace CoverageTracker.empty cand shrinkAuditEvery (some origTag) false with
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
