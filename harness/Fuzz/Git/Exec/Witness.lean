import Fuzz.Git.Exec.Core
import Fuzz.Git.Exec.Vfs
import Fuzz.Git.Exec.Fixtures

namespace Fuzz.Git

open Fuzz.Common
open LeanSwe.Git
open LeanSwe.Git.Model

/-- Helper `isGitHeaderCrudStrip`. -/
def isGitHeaderCrudStrip (c : Char) : Bool :=
  c ≤ ' ' || c == ',' || c == ':' || c == ';' ||
  c == '<' || c == '>' || c == '"' || c == '\'' || c == '\\'

/-- Helper `trimGitIdentField`. -/
def trimGitIdentField (s : String) : String :=
  let dropL := s.toList.dropWhile isGitHeaderCrudStrip
  String.ofList (dropL.reverse.dropWhile isGitHeaderCrudStrip).reverse

/-- Helper `findDoubleLfIdx`. -/
def findDoubleLfIdx (bs : ByteArray) : Option Nat := Id.run do
  if bs.size < 2 then
    return none
  for i in List.range (bs.size - 1) do
    if bs[i]! == 0x0a && bs[i + 1]! == 0x0a then
      return some i
  return none

/-- Helper `verifyCommitObject`. -/
def verifyCommitObject (st : EpisodeState) (repoPath : String) (cid : CommitId)
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

/-- Helper `resolveWitnessRev?`. -/
def resolveWitnessRev? (st : EpisodeState) (repoPath rev : String) : IO (Option CommitId) := do
  match ← (pickApi st false).revParseCommit repoPath rev with
  | .ok cid => return some cid
  | .error _ => return none

/-- Helper `resolveWitnessHead?`. -/
def resolveWitnessHead? (st : EpisodeState) (repoPath : String) : IO (Option CommitId) := do
  match ← (pickApi st false).headCommit? repoPath with
  | .ok (some cid) => return some cid
  | _ => return none

/-- Helper `resolveWitnessBranch?`. -/
def resolveWitnessBranch? (st : EpisodeState) (repoPath : String) (br : RefName) : IO (Option CommitId) := do
  match ← (pickApi st false).revParseCommit repoPath ("refs/heads/" ++ br.raw) with
  | .ok cid => return some cid
  | .error _ => resolveWitnessRev? st repoPath br.raw

/-- Helper `resolveWitnessHeadBranch?`. -/
def resolveWitnessHeadBranch? (st : EpisodeState) (repoPath : String) : IO (Option RefName) := do
  match ← (pickApi st false).headBranch? repoPath with
  | .ok br? => return br?
  | .error _ => return none

/-- Helper `resolveWitnessSymbolicBranch?`. -/
def resolveWitnessSymbolicBranch? (st : EpisodeState) (repoPath spec : String) : IO (Option RefName) := do
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

/-- Helper `splitBytesOn`. -/
def splitBytesOn (sep : UInt8) (bs : ByteArray) : List ByteArray := Id.run do
  let mut out : List ByteArray := []
  let mut start := 0
  for i in List.range bs.size do
    if bs[i]! == sep then
      out := out ++ [bs.extract start i]
      start := i + 1
  if start < bs.size then
    out := out ++ [bs.extract start bs.size]
  return out

/-- Helper `findByteIdx?`. -/
def findByteIdx? (target : UInt8) (bs : ByteArray) : Option Nat := Id.run do
  for i in List.range bs.size do
    if bs[i]! == target then
      return some i
  return none

/-- Helper `resolveWitnessIndex?`. -/
def resolveWitnessIndex? (st : EpisodeState) (repoPath : String) : IO (Option IndexState) := do
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

/-- Helper `syncWorktreeTrackedDiskBytes`. -/
def syncWorktreeTrackedDiskBytes (st : EpisodeState) (repoPath : String) : IO EpisodeState := do
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

/-- Helper `syncWorktreeIndexFromWitness`. -/
def syncWorktreeIndexFromWitness (st : EpisodeState) (repoPath : String) : IO EpisodeState := do
  match resolveCwdAndDiscover st.model repoPath with
  | .ok (repo, some wt, _, _) =>
    match ← resolveWitnessIndex? st repoPath with
    | some idx' =>
      let repo' := updateWorktreeInRepo repo wt.rootPath fun slot => { slot with index := idx' }
      return { st with model := { st.model with repos := updateRepoInList st.model.repos repo.commonDir (fun _ => repo') } }
    | none => return st
  | _ => return st

/-- Helper `targetTreeHasSpecial`. -/
def targetTreeHasSpecial (st : EpisodeState) (repoPath : String) : Bool :=
  match resolveCwdAndDiscover st.model repoPath with
  | .ok (repo, some wt, _, _) =>
    let anyCommitSpecial := repo.commits.any fun c =>
      c.tree.any fun (p, e) =>
        e.kind == .gitlink ||
        basenameBytes p == ".gitignore".toUTF8 ||
        basenameBytes p == ".gitattributes".toUTF8
    worktreeHasSpecialMetadata st.model repo wt || anyCommitSpecial
  | _ => false

/-- Helper `bytesHasSpoofChar`. -/
def bytesHasSpoofChar (bs : ByteArray) : Bool :=
  bs.data.any fun b => b == 0x27 || b == 0x22 || b == 0x0a || b == 0x0d

/-- Helper `targetHasSpoofChar`. -/
def targetHasSpoofChar : PathTarget → Bool
  | .subRel _ rel => hasStderrSpoofChar rel
  | .raw s => hasStderrSpoofChar s
  | _ => false

/-- Helper `stepIntroducesSpoof`. -/
def stepIntroducesSpoof : GitFuzzStep → Bool
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


end Fuzz.Git
