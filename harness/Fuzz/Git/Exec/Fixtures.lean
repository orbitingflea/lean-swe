import Fuzz.Git.Exec.Core
import Fuzz.Git.Exec.Vfs

namespace Fuzz.Git

open Fuzz.Common
open LeanSwe.Git
open LeanSwe.Git.Model

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

/-- Helper `compareExceptTagged`. -/
def compareExceptTagged {α : Type} [BEq α] [Repr α] (label : String)
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

/-- Helper `formatByteArrayShort`. -/
def formatByteArrayShort (bs : ByteArray) : String :=
  let previewLen := min bs.size 48
  let previewHex := byteArrayToHex (bs.extract 0 previewLen)
  if bs.size <= 48 then s!"ByteArray(len={bs.size}, hex={previewHex})"
  else s!"ByteArray(len={bs.size}, headHex={previewHex}...)"

/-- Helper `formatShowOutcome`. -/
def formatShowOutcome : Except GitError (Option ByteArray) → String
  | .ok none => "ok(none)"
  | .ok (some bs) => s!"ok(some {formatByteArrayShort bs})"
  | .error e => s!"error({repr e})"

/-- Helper `compareShowFileTagged`. -/
def compareShowFileTagged (label : String)
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

/-- Helper `normalizeWorktrees`. -/
def normalizeWorktrees (xs : Array WorktreeInfo) : Array WorktreeInfo :=
  if xs.size <= 2 then xs
  else
    let head := xs.extract 0 1
    let tail := (xs.extract 1 xs.size).qsort (fun a b => a.path < b.path)
    head ++ tail

/-- Helper `compareWorktreesTagged`. -/
def compareWorktreesTagged (label : String) (real model : Except GitError (Array WorktreeInfo)) :
    Except (String × String) Unit :=
  compareExceptTagged label (real.map normalizeWorktrees) (model.map normalizeWorktrees)

/-- Helper `execGitRawCreateMergeConflict`. -/
def execGitRawCreateMergeConflict (st : EpisodeState) (repoSlot : SlotId) (branchA branchB : RefName)
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

/-- Helper `execGitRawCreateCrissCrossMerge`. -/
def execGitRawCreateCrissCrossMerge (st : EpisodeState) (repoSlot : SlotId) : IO (EpisodeState × Bool) := do
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

/-- Emit an `ERR_HIT` record when `emitErrHits` is enabled and `res` returned `.error`. -/
def logGitErr {α : Type} (emitErrHits : Bool) (opName : String) (res : Except GitError α)
    (mode : String := "real") : IO Unit := do
  if emitErrHits then
    if let .error e := res then
      Fuzz.Common.logErrHit s!"LeanSwe.Git.{opName}" s!"LeanSwe.Git.GitErrorKind.{errorKindLabel e.kind}" mode

/-- Helper `recordOutcome`. -/
def recordOutcome {α : Type} (tr : CoverageTracker) (op : String) (res : Except GitError α) :
    CoverageTracker :=
  match res with
  | .ok _ => tr.record op "ok"
  | .error e => tr.record op s!"err.{errorKindLabel e.kind}"

/-- Helper `runRawOpChecked`. -/
def runRawOpChecked {α : Type} [BEq α] [Repr α] (st : EpisodeState) (tr : CoverageTracker)
    (opName : String) (realAct : IO (Except GitError α)) (modelAct : GitRepoState → Except GitError α × GitRepoState)
    (onBothOk : EpisodeState → α → α → EpisodeState := fun s _ _ => s) :
    IO (Except TraceError (EpisodeState × CoverageTracker)) := do
  let realRes ← realAct
  logGitErr st.emitErrHits opName realRes
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


end Fuzz.Git
