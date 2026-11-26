import Fuzz.Git.Exec.Core
import Fuzz.Git.Exec.Vfs
import Fuzz.Git.Exec.Fixtures
import Fuzz.Git.Exec.Witness

namespace Fuzz.Git

open Fuzz.Common
open LeanSwe.Git
open LeanSwe.Git.Model

/-- Execute VFS, fixture, query, and initial mutation fuzz steps, returning `none` for steps handled by `execStepPartB`. -/
def execStepPartA (st : EpisodeState) (tr : CoverageTracker) (step : GitFuzzStep) :
    IO (Option (Except TraceError (EpisodeState × CoverageTracker))) := do
  let run : IO (Except TraceError (EpisodeState × CoverageTracker)) := do
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
        logGitErr st.emitErrHits step.opName realRes
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
      logGitErr st.emitErrHits step.opName realRes
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
      logGitErr st.emitErrHits step.opName realRes
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
      logGitErr st.emitErrHits step.opName realRes
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
      logGitErr st.emitErrHits step.opName realRes
      let (modelRes, modelNext) := evalGitApi.listWorktrees p st.model
      let tr' := recordOutcome tr step.opName realRes
      match compareWorktreesTagged step.opName realRes modelRes with
      | .error (tag, msg) => return .error (.mismatch tag msg)
      | .ok () => return .ok ({ st with model := modelNext }, tr')
    | .opShowFile t rev relPath poison =>
      let p := resolveTarget st.rootDir t
      let revStr := resolveRevSpec st rev
      let realRes ← (pickApi st poison).showFile? p revStr relPath
      logGitErr st.emitErrHits step.opName realRes
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
        logGitErr st.emitErrHits step.opName realRes
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
      logGitErr st.emitErrHits step.opName realRes
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
    | _ => return .error (.infra "unhandled in execStepPartA")
  match step with
  | .vfsWriteFile .. | .vfsMkdir .. | .vfsSymlink .. | .vfsRemoveFile .. | .vfsRemoveDir ..
  | .vfsRemoveTree .. | .vfsChmodDir .. | .vfsChmodSubDir .. | .vfsSetFileExecutable ..
  | .gitRawLockWorktree .. | .gitRawCreateTag .. | .gitRawCreateMergeConflict .. | .gitRawCreateCrissCrossMerge ..
  | .opIsRepo .. | .opRepoRoot .. | .opCommonDir .. | .opHeadCommit .. | .opHeadBranch ..
  | .opHeadState .. | .opRevParseCommit .. | .opIsAncestor .. | .opMergeBase ..
  | .opStatus .. | .opDiffNameStatus .. | .opListWorktrees .. | .opShowFile ..
  | .opInit .. | .opClone .. | .opAdd .. | .opCommit .. =>
    return some (← run)
  | _ => return none

end Fuzz.Git
