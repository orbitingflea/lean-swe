import LeanSwe.Git.Types
import LeanSwe.Git.Model
import Fuzz.Common.Rng

namespace Fuzz.Git

open Fuzz.Common
open LeanSwe.Git
open LeanSwe.Git.Model

/-- Symbolic filesystem slot under an episode temporary directory root. -/
inductive SlotId where
  /-- Primary non-bare working repository slot (`repoA`). -/
  | repoA
  /-- Secondary non-bare working repository slot (`repoB`). -/
  | repoB
  /-- Bare repository slot (`bareRepo.git`). -/
  | bareRepo
  /-- Clone destination repository slot (`cloneRepo`). -/
  | cloneRepo
  /-- First linked worktree slot (`wt1`). -/
  | wt1
  /-- Second linked worktree slot (`wt2`). -/
  | wt2
  /-- Linked worktree slot attached to `bareRepo` (`bareWt`). -/
  | bareWt
  /-- Nested subdirectory inside `repoA` (`repoA/sub`). -/
  | subDir
  /-- Regular file occupying a top-level slot (`plainFile`). -/
  | plainFile
  /-- Absent directory path (`missingDir`). -/
  | missingDir
  /-- Symlink targeting a directory containing invalid UTF-8 bytes (`badUtf8Dir`). -/
  | badUtf8Dir
  /-- Symlink targeting `repoA` (`symLinkDir`). -/
  | symLinkDir
  /-- Dangling symlink targeting a missing path (`danglingSym`). -/
  | danglingSym
  /-- First half of an `ELOOP` symlink cycle (`symLoopA -> symLoopB`). -/
  | symLoopA
  /-- Second half of an `ELOOP` symlink cycle (`symLoopB -> symLoopA`). -/
  | symLoopB
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Relative path under the episode temporary root corresponding to a `SlotId`. -/
def SlotId.relPath : SlotId → String
  | .repoA => "repoA"
  | .repoB => "repoB"
  | .bareRepo => "bareRepo.git"
  | .cloneRepo => "cloneRepo"
  | .wt1 => "wt1"
  | .wt2 => "wt2"
  | .bareWt => "bareWt"
  | .subDir => "repoA/sub"
  | .plainFile => "plainFile"
  | .missingDir => "missingDir"
  | .badUtf8Dir => "badUtf8Dir"
  | .symLinkDir => "symLinkDir"
  | .danglingSym => "danglingSym"
  | .symLoopA => "symLoopA"
  | .symLoopB => "symLoopB"

/-- Target path specification resolved relative to the episode temporary root. -/
inductive PathTarget where
  /-- Standard path for a symbolic `SlotId`. -/
  | slot (s : SlotId)
  /-- Raw hostile or boundary path string passed verbatim (scoped to episode `cwd`). -/
  | raw (p : String)
  /-- Sub-path relative to a parent `SlotId` directory. -/
  | subRel (parent : SlotId) (rel : String)
  /-- Explicit `file://` URL pointing to a `SlotId` under the episode root. -/
  | fileUrl (s : SlotId)
  /-- Explicit `file://localhost/` URL pointing to a `SlotId` under the episode root. -/
  | fileUrlLocalhost (s : SlotId)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Revision specification supporting raw strings, observed 40-char SHAs, and abbreviated SHA prefixes. -/
inductive FuzzRevSpec where
  /-- Literal revision expression string. -/
  | raw (spec : String)
  /-- Reference to an observed real commit SHA indexed modulo `knownCommits.size`, falling back to `fallback`. -/
  | commitIdx (idx : Nat) (fallback : String)
  /-- Abbreviated prefix (`7..12` hex chars) of an observed commit SHA, falling back to `fallback`. -/
  | shortCommitIdx (idx len : Nat) (fallback : String)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Target specification for fuzzing `LeanSwe.Git.checkout` across branch, known commit, and ref forms. -/
inductive FuzzCheckoutTarget where
  /-- Check out a branch reference. -/
  | branch (name : RefName)
  /-- Check out a recorded commit index (or fallback unknown hex). -/
  | commitIdx (idx : Nat) (rawHex? : Option String)
  /-- Check out a raw revision specification or observed commit SHA. -/
  | ref (spec : FuzzRevSpec)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Stateful differential fuzzing trace step covering host VFS/fault setup and all 26 `LeanSwe.Git` operations. -/
inductive GitFuzzStep where
  /-- Create or overwrite a file under `slot` with exact byte contents and executable bit. -/
  | vfsWriteFile (slot : SlotId) (relBytes : ByteArray) (content : ByteArray) (executable : Bool)
  /-- Create a directory hierarchy under `slot` (supports raw non-UTF-8 paths). -/
  | vfsMkdir (slot : SlotId) (relBytes : ByteArray)
  /-- Create a symbolic link under `slot` pointing to `targetBytes` (supports raw non-UTF-8 paths/targets). -/
  | vfsSymlink (slot : SlotId) (relBytes : ByteArray) (targetBytes : ByteArray)
  /-- Remove a file or symlink under `slot`. -/
  | vfsRemoveFile (slot : SlotId) (relBytes : ByteArray)
  /-- Remove an empty directory under `slot`. -/
  | vfsRemoveDir (slot : SlotId) (relBytes : ByteArray)
  /-- Recursively delete a linked worktree slot directory on disk and in `vfs` without unregistering it. -/
  | vfsRemoveTree (slot : SlotId)
  /-- Toggle directory searchability (`0755` vs `0000`) on a top-level `slot`. -/
  | vfsChmodDir (slot : SlotId) (searchable : Bool)
  /-- Toggle directory searchability (`0755` vs `0000`) on a subdirectory inside `slot`. -/
  | vfsChmodSubDir (slot : SlotId) (relBytes : ByteArray) (searchable : Bool)
  /-- Toggle regular file executable bit (`0755` vs `0644`) on a file inside `slot`. -/
  | vfsSetFileExecutable (slot : SlotId) (relBytes : ByteArray) (executable : Bool)
  /-- Lock or unlock a linked worktree via raw `git worktree lock/unlock`. -/
  | gitRawLockWorktree (repoSlot wtSlot : SlotId) (lock : Bool) (reason? : Option String)
  /-- Create or update a lightweight tag (`refs/tags/<tagName>`) via raw `git update-ref`. -/
  | gitRawCreateTag (repoSlot : SlotId) (tagName : RefName) (targetRev : FuzzRevSpec)
  /-- Create a real diverged merge conflict at `relPath` in `repoSlot`, optionally removing `MERGE_HEAD`. -/
  | gitRawCreateMergeConflict (repoSlot : SlotId) (branchA branchB : RefName) (relPath : String) (dropMergeHead : Bool)
  /-- Build a true 2-LCA criss-cross merge DAG inside `repoSlot`. -/
  | gitRawCreateCrissCrossMerge (repoSlot : SlotId)
  /-- Invoke `LeanSwe.Git.isRepo`. -/
  | opIsRepo (target : PathTarget) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.repoRoot`. -/
  | opRepoRoot (target : PathTarget) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.commonDir`. -/
  | opCommonDir (target : PathTarget) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.headCommit?`. -/
  | opHeadCommit (target : PathTarget) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.headBranch?`. -/
  | opHeadBranch (target : PathTarget) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.headState`. -/
  | opHeadState (target : PathTarget) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.revParseCommit`. -/
  | opRevParseCommit (target : PathTarget) (rev : FuzzRevSpec) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.isAncestor`. -/
  | opIsAncestor (target : PathTarget) (ancIdx descIdx : Nat)
      (rawAnc? rawDesc? : Option String) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.mergeBase?`. -/
  | opMergeBase (target : PathTarget) (aIdx bIdx : Nat)
      (rawA? rawB? : Option String) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.status`. -/
  | opStatus (target : PathTarget) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.diffNameStatus`. -/
  | opDiffNameStatus (target : PathTarget) (revA : FuzzRevSpec) (revB? : Option FuzzRevSpec)
      (paths : Array String) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.listWorktrees`. -/
  | opListWorktrees (target : PathTarget) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.showFile?`. -/
  | opShowFile (target : PathTarget) (rev : FuzzRevSpec) (relPath : String) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.init`. -/
  | opInit (target : PathTarget) (bare : Bool) (initialBranch? : Option RefName) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.clone`. -/
  | opClone (source target : PathTarget) (opts : CloneOptions) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.add`. -/
  | opAdd (target : PathTarget) (paths : Array String) (all : Bool) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.commit`. -/
  | opCommit (target : PathTarget) (opts : CommitOptions) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.createBranch`. -/
  | opCreateBranch (target : PathTarget) (branch : RefName) (startPoint? : Option FuzzRevSpec)
      (force : Bool) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.deleteBranch`. -/
  | opDeleteBranch (target : PathTarget) (branch : RefName) (force : Bool) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.checkout`. -/
  | opCheckout (target : PathTarget) (coTarget : FuzzCheckoutTarget) (force : Bool) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.switch`. -/
  | opSwitch (target : PathTarget) (branch : RefName) (create : Bool) (startPoint? : Option FuzzRevSpec)
      (force : Bool) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.reset`. -/
  | opReset (target : PathTarget) (mode : ResetMode) (rev : FuzzRevSpec) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.fetch`. -/
  | opFetch (target : PathTarget) (remote : String) (refspec? : Option String)
      (prune : Bool) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.worktreeAdd`. -/
  | opWorktreeAdd (target wtTarget : PathTarget) (wtRev? : Option FuzzRevSpec)
      (newBranch? : Option RefName) (detach force : Bool) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.worktreeRemove`. -/
  | opWorktreeRemove (target wtTarget : PathTarget) (force : Bool) (poisonEnv : Bool)
  /-- Invoke `LeanSwe.Git.withWorktree` with nested inner subtrace steps. -/
  | opWithWorktree (target wtTarget : PathTarget) (wtRev? : Option FuzzRevSpec)
      (newBranch? : Option RefName) (detach force : Bool) (innerSteps : List GitFuzzStep)
      (returnErr : Bool) (poisonEnv : Bool)
  /-- Invoke a deterministic hanging-alias timeout probe verifying `.timeout` mapping on `target`. -/
  | opTimeoutProbe (target : PathTarget) (probeOp : Nat)
  deriving Repr, BEq

/-- Operation family label recorded into `Fuzz.Common.CoverageTracker`. -/
def GitFuzzStep.opName : GitFuzzStep → String
  | .vfsWriteFile _ _ _ _ => "vfsWriteFile"
  | .vfsMkdir _ _ => "vfsMkdir"
  | .vfsSymlink _ _ _ => "vfsSymlink"
  | .vfsRemoveFile _ _ => "vfsRemoveFile"
  | .vfsRemoveDir _ _ => "vfsRemoveDir"
  | .vfsRemoveTree _ => "vfsRemoveTree"
  | .vfsChmodDir _ _ => "vfsChmodDir"
  | .vfsChmodSubDir _ _ _ => "vfsChmodSubDir"
  | .vfsSetFileExecutable _ _ _ => "vfsSetFileExecutable"
  | .gitRawLockWorktree _ _ _ _ => "gitRawLockWorktree"
  | .gitRawCreateTag _ _ _ => "gitRawCreateTag"
  | .gitRawCreateMergeConflict _ _ _ _ _ => "gitRawCreateMergeConflict"
  | .gitRawCreateCrissCrossMerge _ => "gitRawCreateCrissCrossMerge"
  | .opIsRepo _ _ => "isRepo"
  | .opRepoRoot _ _ => "repoRoot"
  | .opCommonDir _ _ => "commonDir"
  | .opHeadCommit _ _ => "headCommit?"
  | .opHeadBranch _ _ => "headBranch?"
  | .opHeadState _ _ => "headState"
  | .opRevParseCommit _ _ _ => "revParseCommit"
  | .opIsAncestor _ _ _ _ _ _ => "isAncestor"
  | .opMergeBase _ _ _ _ _ _ => "mergeBase?"
  | .opStatus _ _ => "status"
  | .opDiffNameStatus _ _ _ _ _ => "diffNameStatus"
  | .opListWorktrees _ _ => "listWorktrees"
  | .opShowFile _ _ _ _ => "showFile?"
  | .opInit _ _ _ _ => "init"
  | .opClone _ _ _ _ => "clone"
  | .opAdd _ _ _ _ => "add"
  | .opCommit _ _ _ => "commit"
  | .opCreateBranch _ _ _ _ _ => "createBranch"
  | .opDeleteBranch _ _ _ _ => "deleteBranch"
  | .opCheckout _ _ _ _ => "checkout"
  | .opSwitch _ _ _ _ _ _ => "switch"
  | .opReset _ _ _ _ => "reset"
  | .opFetch _ _ _ _ _ => "fetch"
  | .opWorktreeAdd _ _ _ _ _ _ _ => "worktreeAdd"
  | .opWorktreeRemove _ _ _ _ => "worktreeRemove"
  | .opWithWorktree _ _ _ _ _ _ _ _ _ => "withWorktree"
  | .opTimeoutProbe _ _ => "timeoutProbe"

private def togglePoisonStep : GitFuzzStep → Option GitFuzzStep
  | .opIsRepo t true => some (.opIsRepo t false)
  | .opRepoRoot t true => some (.opRepoRoot t false)
  | .opCommonDir t true => some (.opCommonDir t false)
  | .opHeadCommit t true => some (.opHeadCommit t false)
  | .opHeadBranch t true => some (.opHeadBranch t false)
  | .opHeadState t true => some (.opHeadState t false)
  | .opRevParseCommit t r true => some (.opRevParseCommit t r false)
  | .opIsAncestor t a b ra rb true => some (.opIsAncestor t a b ra rb false)
  | .opMergeBase t a b ra rb true => some (.opMergeBase t a b ra rb false)
  | .opStatus t true => some (.opStatus t false)
  | .opDiffNameStatus t ra rb ps true => some (.opDiffNameStatus t ra rb ps false)
  | .opListWorktrees t true => some (.opListWorktrees t false)
  | .opShowFile t r p true => some (.opShowFile t r p false)
  | .opInit t b ib true => some (.opInit t b ib false)
  | .opClone s t o true => some (.opClone s t o false)
  | .opAdd t ps a true => some (.opAdd t ps a false)
  | .opCommit t o true => some (.opCommit t o false)
  | .opCreateBranch t b sp f true => some (.opCreateBranch t b sp f false)
  | .opDeleteBranch t b f true => some (.opDeleteBranch t b f false)
  | .opCheckout t c f true => some (.opCheckout t c f false)
  | .opSwitch t b c sp f true => some (.opSwitch t b c sp f false)
  | .opReset t m r true => some (.opReset t m r false)
  | .opFetch t rem rf pr true => some (.opFetch t rem rf pr false)
  | .opWorktreeAdd t wt wr nb dt f true => some (.opWorktreeAdd t wt wr nb dt f false)
  | .opWorktreeRemove t wt f true => some (.opWorktreeRemove t wt f false)
  | .opWithWorktree t wt wr nb dt f ins re true =>
    some (.opWithWorktree t wt wr nb dt f ins re false)
  | _ => none

/-- Return `true` when `step` currently enables hostile `poisonEnv` overrides. -/
def stepHasPoisonEnv (step : GitFuzzStep) : Bool :=
  (togglePoisonStep step).isSome

private def dedupNats (xs : List Nat) : List Nat :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

private def shrinkCommitIdxNat (idx : Nat) : List Nat :=
  dedupNats ([0, 1, 2, 3, idx / 2, idx - 1].filter (· < idx))

private def dropArrayIdx {α : Type} (xs : Array α) (idx : Nat) : Array α :=
  xs.extract 0 idx ++ xs.extract (idx + 1) xs.size

private def shrinkRevSpec : FuzzRevSpec → List FuzzRevSpec
  | .commitIdx idx fb =>
    let rawCands := if fb == "HEAD" then [.raw "HEAD"] else [.raw fb, .raw "HEAD"]
    rawCands ++ (shrinkCommitIdxNat idx).map (.commitIdx · fb)
  | .shortCommitIdx idx len fb =>
    let lenCands := if len > 7 then [.shortCommitIdx idx 7 fb] else []
    let idxCands := (shrinkCommitIdxNat idx).map (.shortCommitIdx · len fb)
    [.raw "dead"] ++ lenCands ++ idxCands
  | .raw s => if s != "HEAD" then [.raw "HEAD"] else []

private def shrinkPathTarget : PathTarget → List PathTarget
  | .subRel parent _ => [.slot parent]
  | .fileUrlLocalhost s => [.fileUrl s, .slot s]
  | .fileUrl s => [.slot s]
  | .raw s =>
    if s.isEmpty then [.slot .repoA]
    else if s == "\x00" then [.slot .repoA, .raw ""]
    else if s.toList.contains '\x00' then [.slot .repoA, .raw "", .raw "\x00"]
    else [.slot .repoA, .raw ""]
  | .slot s => if s != .repoA then [.slot .repoA] else []

private def shrinkRefName (br : RefName) : List RefName :=
  let s := br.raw
  if s.length > 8 then
    let half := String.ofList (s.toList.take (s.length / 2))
    ([{ raw := "main" }, { raw := "" }, { raw := "-bad" }, { raw := half }]).filter (· != br)
  else if s != "main" && s != "" then
    ([{ raw := "main" }, { raw := "" }]).filter (· != br)
  else []

private def shrinkRelPathStr (rp : String) : List String :=
  if rp == "a.txt" then []
  else if rp.isEmpty then ["a.txt"]
  else if rp.length > 16 then
    let half := String.ofList (rp.toList.take (rp.length / 2))
    (["a.txt", "", half]).filter (· != rp)
  else ["a.txt", ""]

private def shrinkCheckoutTarget : FuzzCheckoutTarget → List FuzzCheckoutTarget
  | .branch br => (shrinkRefName br).map .branch
  | .commitIdx idx (some _) =>
    (.commitIdx idx none) :: ((shrinkCommitIdxNat idx).map (.commitIdx · none))
  | .commitIdx idx none =>
    (shrinkCommitIdxNat idx).map (.commitIdx · none)
  | .ref rv => (shrinkRevSpec rv).map .ref

private def replacePathTarget (fromTgt toTgt cur : PathTarget) : PathTarget :=
  if cur == fromTgt then toTgt else cur

private def replaceSlotTarget (fromTgt toTgt : PathTarget) (sl : SlotId) : SlotId :=
  match fromTgt, toTgt with
  | .slot sFrom, .slot sTo => if sl == sFrom then sTo else sl
  | _, _ => sl

mutual
private def retargetStepPath (fromTgt toTgt : PathTarget) (step : GitFuzzStep) : GitFuzzStep :=
  let r := replacePathTarget fromTgt toTgt
  let rSlot := replaceSlotTarget fromTgt toTgt
  match step with
  | .vfsWriteFile sl rel c ex => .vfsWriteFile (rSlot sl) rel c ex
  | .vfsMkdir sl rel => .vfsMkdir (rSlot sl) rel
  | .vfsSymlink sl rel tgt => .vfsSymlink (rSlot sl) rel tgt
  | .vfsRemoveFile sl rel => .vfsRemoveFile (rSlot sl) rel
  | .vfsRemoveDir sl rel => .vfsRemoveDir (rSlot sl) rel
  | .vfsRemoveTree sl => .vfsRemoveTree (rSlot sl)
  | .vfsChmodDir sl sc => .vfsChmodDir (rSlot sl) sc
  | .vfsChmodSubDir sl rel sc => .vfsChmodSubDir (rSlot sl) rel sc
  | .vfsSetFileExecutable sl rel ex => .vfsSetFileExecutable (rSlot sl) rel ex
  | .gitRawLockWorktree rSl wtSl lk rsn? => .gitRawLockWorktree (rSlot rSl) (rSlot wtSl) lk rsn?
  | .gitRawCreateTag rSl tn rv => .gitRawCreateTag (rSlot rSl) tn rv
  | .gitRawCreateMergeConflict rSl a b rp dmh => .gitRawCreateMergeConflict (rSlot rSl) a b rp dmh
  | .gitRawCreateCrissCrossMerge rSl => .gitRawCreateCrissCrossMerge (rSlot rSl)
  | .opIsRepo t p => .opIsRepo (r t) p
  | .opRepoRoot t p => .opRepoRoot (r t) p
  | .opCommonDir t p => .opCommonDir (r t) p
  | .opHeadCommit t p => .opHeadCommit (r t) p
  | .opHeadBranch t p => .opHeadBranch (r t) p
  | .opHeadState t p => .opHeadState (r t) p
  | .opRevParseCommit t rv p => .opRevParseCommit (r t) rv p
  | .opIsAncestor t a b rA? rB? p => .opIsAncestor (r t) a b rA? rB? p
  | .opMergeBase t a b rA? rB? p => .opMergeBase (r t) a b rA? rB? p
  | .opStatus t p => .opStatus (r t) p
  | .opDiffNameStatus t ra rb? ps p => .opDiffNameStatus (r t) ra rb? ps p
  | .opListWorktrees t p => .opListWorktrees (r t) p
  | .opShowFile t rv rp p => .opShowFile (r t) rv rp p
  | .opInit t b ib? p => .opInit (r t) b ib? p
  | .opClone s t o p => .opClone (r s) (r t) o p
  | .opAdd t ps a p => .opAdd (r t) ps a p
  | .opCommit t o p => .opCommit (r t) o p
  | .opCreateBranch t b sp? f p => .opCreateBranch (r t) b sp? f p
  | .opDeleteBranch t b f p => .opDeleteBranch (r t) b f p
  | .opCheckout t c f p => .opCheckout (r t) c f p
  | .opSwitch t b c sp? f p => .opSwitch (r t) b c sp? f p
  | .opReset t m rv p => .opReset (r t) m rv p
  | .opFetch t rem rf? pr p => .opFetch (r t) rem rf? pr p
  | .opWorktreeAdd t wt wr? nb? dt f p => .opWorktreeAdd (r t) (r wt) wr? nb? dt f p
  | .opWorktreeRemove t wt f p => .opWorktreeRemove (r t) (r wt) f p
  | .opWithWorktree t wt wr? nb? dt f ins re p =>
    .opWithWorktree (r t) (r wt) wr? nb? dt f (retargetStepList fromTgt toTgt ins) re p
  | .opTimeoutProbe t k => .opTimeoutProbe (r t) k

private def retargetStepList (fromTgt toTgt : PathTarget) : List GitFuzzStep → List GitFuzzStep
  | [] => []
  | s :: rest => retargetStepPath fromTgt toTgt s :: retargetStepList fromTgt toTgt rest
end

/-- Produce candidate traces that splice a `withWorktree` subtrace directly into the outer trace. -/
def spliceWithWorktreeSteps (trace : Array GitFuzzStep) : List (Array GitFuzzStep) :=
  (List.range trace.size).flatMap fun i =>
    match (trace[i]? : Option GitFuzzStep) with
    | some (.opWithWorktree t wt wr? nb? dt f ins re p) =>
      let pre := trace.extract 0 i
      let post := trace.extract (i + 1) trace.size
      let lifted := pre ++ (retargetStepList wt t ins).toArray ++ post
      if ins.isEmpty then
        [pre ++ post]
      else if re then
        [lifted]
      else
        let expanded :=
          pre ++ #[.opWorktreeAdd t wt wr? nb? dt f p] ++ ins.toArray ++
          #[.opWorktreeRemove t wt f p] ++ post
        [lifted, expanded]
    | _ => []

private def shrinkInnerList (shrinkOne : GitFuzzStep → List GitFuzzStep) (ins : List GitFuzzStep) :
    List (List GitFuzzStep) :=
  let dropped :=
    if ins.isEmpty then []
    else if ins.length == 1 then [[]]
    else
      [] :: ((List.range ins.length).map fun i => ins.eraseIdx i)
  let elemShrunk :=
    (List.range ins.length).flatMap fun i =>
      match ins[i]? with
      | none => []
      | some elem =>
        (shrinkOne elem).map fun c => ins.set i c
  dropped ++ elemShrunk

private def shrinkStepFuel : Nat → GitFuzzStep → List GitFuzzStep
  | 0, _ => []
  | fuel + 1, step =>
  let base :=
    match togglePoisonStep step with
    | some s => [s]
    | none => []
  let cands : List GitFuzzStep :=
    match step with
    | .vfsWriteFile slot rel content ex =>
      (if ex then [.vfsWriteFile slot rel content false] else []) ++
      (if content.size > 1 then [.vfsWriteFile slot rel "x".toUTF8 ex, .vfsWriteFile slot rel ByteArray.empty ex]
       else if content.size == 1 then [.vfsWriteFile slot rel ByteArray.empty ex] else [])
    | .vfsSetFileExecutable sl rel ex =>
      if ex then [.vfsSetFileExecutable sl rel false] else []
    | .gitRawLockWorktree r wt lk rsn? =>
      if rsn?.isSome then [.gitRawLockWorktree r wt lk none] else []
    | .gitRawCreateTag r tn rv =>
      (shrinkRefName tn).map (.gitRawCreateTag r · rv) ++
      (shrinkRevSpec rv).map (.gitRawCreateTag r tn ·)
    | .gitRawCreateMergeConflict r a b rp dmh =>
      (if rp != "conflict.txt" then [.gitRawCreateMergeConflict r a b "conflict.txt" dmh] else []) ++
      (if dmh then [.gitRawCreateMergeConflict r a b rp false] else [])
    | .opIsRepo t p => base ++ (shrinkPathTarget t).map (.opIsRepo · p)
    | .opRepoRoot t p => base ++ (shrinkPathTarget t).map (.opRepoRoot · p)
    | .opCommonDir t p => base ++ (shrinkPathTarget t).map (.opCommonDir · p)
    | .opHeadCommit t p => base ++ (shrinkPathTarget t).map (.opHeadCommit · p)
    | .opHeadBranch t p => base ++ (shrinkPathTarget t).map (.opHeadBranch · p)
    | .opHeadState t p => base ++ (shrinkPathTarget t).map (.opHeadState · p)
    | .opStatus t p => base ++ (shrinkPathTarget t).map (.opStatus · p)
    | .opListWorktrees t p => base ++ (shrinkPathTarget t).map (.opListWorktrees · p)
    | .opShowFile t rv rp p =>
      base ++ (shrinkPathTarget t).map (.opShowFile · rv rp p) ++
      (shrinkRevSpec rv).map (.opShowFile t · rp p) ++
      (shrinkRelPathStr rp).map (.opShowFile t rv · p)
    | .opRevParseCommit t rv p =>
      base ++ (shrinkPathTarget t).map (.opRevParseCommit · rv p) ++
      (shrinkRevSpec rv).map (fun r' => .opRevParseCommit t r' p)
    | .opIsAncestor t a b rA? rB? p =>
      base ++
      (shrinkPathTarget t).map (.opIsAncestor · a b rA? rB? p) ++
      (if rA?.isSome then [.opIsAncestor t a b none rB? p] else []) ++
      (if rB?.isSome then [.opIsAncestor t a b rA? none p] else []) ++
      (shrinkCommitIdxNat a).map (.opIsAncestor t · b rA? rB? p) ++
      (shrinkCommitIdxNat b).map (.opIsAncestor t a · rA? rB? p)
    | .opMergeBase t a b rA? rB? p =>
      base ++
      (shrinkPathTarget t).map (.opMergeBase · a b rA? rB? p) ++
      (if rA?.isSome then [.opMergeBase t a b none rB? p] else []) ++
      (if rB?.isSome then [.opMergeBase t a b rA? none p] else []) ++
      (shrinkCommitIdxNat a).map (.opMergeBase t · b rA? rB? p) ++
      (shrinkCommitIdxNat b).map (.opMergeBase t a · rA? rB? p)
    | .opInit t bare initBr? p =>
      let brShrinks :=
        match initBr? with
        | none => []
        | some ib => .opInit t bare none p :: ((shrinkRefName ib).map fun b' => .opInit t bare (some b') p)
      base ++
      (shrinkPathTarget t).map (.opInit · bare initBr? p) ++
      (if bare then [.opInit t false initBr? p] else []) ++
      brShrinks
    | .opClone s t opts p =>
      let srcShrinks := (shrinkPathTarget s).map (.opClone · t opts p)
      let dstShrinks := (shrinkPathTarget t).map (.opClone s · opts p)
      base ++ srcShrinks ++ dstShrinks ++
      (if opts.bare then [.opClone s t { opts with bare := false } p] else []) ++
      (if opts.singleBranch then [.opClone s t { opts with singleBranch := false } p] else []) ++
      (if opts.depth?.isSome then [.opClone s t { opts with depth? := none } p] else []) ++
      (if opts.branch?.isSome then [.opClone s t { opts with branch? := none } p] else [])
    | .opAdd t ps a p =>
      let dropOneCands :=
        if ps.size > 2 then
          (List.range ps.size).map fun i => .opAdd t (dropArrayIdx ps i) a p
        else []
      let elemCands :=
        (List.range ps.size).flatMap fun i =>
          match ps[i]? with
          | none => []
          | some rp => (shrinkRelPathStr rp).map fun rp' => .opAdd t (ps.set! i rp') a p
      base ++
      (shrinkPathTarget t).map (.opAdd · ps a p) ++
      (if a && !ps.isEmpty then [.opAdd t #[] true p, .opAdd t ps false p] else []) ++
      (if ps.size > 1 then (ps.toList.map fun single => .opAdd t #[single] a p) ++ dropOneCands else []) ++
      elemCands
    | .opCommit t opts p =>
      base ++
      (shrinkPathTarget t).map (.opCommit · opts p) ++
      (if opts.allowEmpty then [.opCommit t { opts with allowEmpty := false } p] else []) ++
      (if opts.authorName.isSome then [.opCommit t { opts with authorName := none } p] else []) ++
      (if opts.authorEmail.isSome then [.opCommit t { opts with authorEmail := none } p] else []) ++
      (if opts.message.length > 2 then [.opCommit t { opts with message := "x" } p] else [])
    | .opCreateBranch t br sp? f p =>
      base ++
      (shrinkPathTarget t).map (.opCreateBranch · br sp? f p) ++
      (shrinkRefName br).map (.opCreateBranch t · sp? f p) ++
      (if f then [.opCreateBranch t br sp? false p] else []) ++
      (if sp?.isSome then [.opCreateBranch t br none f p] else [])
    | .opDeleteBranch t br f p =>
      base ++
      (shrinkPathTarget t).map (.opDeleteBranch · br f p) ++
      (shrinkRefName br).map (.opDeleteBranch t · f p) ++
      (if f then [.opDeleteBranch t br false p] else [])
    | .opCheckout t coTgt f p =>
      base ++
      (shrinkPathTarget t).map (.opCheckout · coTgt f p) ++
      (shrinkCheckoutTarget coTgt).map (.opCheckout t · f p) ++
      (if f then [.opCheckout t coTgt false p] else [])
    | .opSwitch t br c sp? f p =>
      base ++
      (shrinkPathTarget t).map (.opSwitch · br c sp? f p) ++
      (shrinkRefName br).map (.opSwitch t · c sp? f p) ++
      (if f then [.opSwitch t br c sp? false p] else []) ++
      (if c then [.opSwitch t br false none f p] else []) ++
      (if sp?.isSome then [.opSwitch t br c none f p] else [])
    | .opReset t m rv p =>
      let mShrinks :=
        match m with
        | .hard => [.opReset t .mixed rv p, .opReset t .soft rv p]
        | .mixed => [.opReset t .soft rv p]
        | .soft => []
      base ++ (shrinkPathTarget t).map (.opReset · m rv p) ++ mShrinks ++ (shrinkRevSpec rv).map (fun r' => .opReset t m r' p)
    | .opFetch t rem rs? pr p =>
      base ++
      (shrinkPathTarget t).map (.opFetch · rem rs? pr p) ++
      (if pr then [.opFetch t rem rs? false p] else []) ++
      (if rs?.isSome then [.opFetch t rem none pr p] else [])
    | .opDiffNameStatus t ra rb? ps p =>
      let rbShrinks :=
        match rb? with
        | none => []
        | some rb => .opDiffNameStatus t ra none ps p :: ((shrinkRevSpec rb).map fun rb' => .opDiffNameStatus t ra (some rb') ps p)
      let dropOneCands :=
        if ps.size > 2 then
          (List.range ps.size).map fun i => .opDiffNameStatus t ra rb? (dropArrayIdx ps i) p
        else []
      let elemCands :=
        (List.range ps.size).flatMap fun i =>
          match ps[i]? with
          | none => []
          | some rp => (shrinkRelPathStr rp).map fun rp' => .opDiffNameStatus t ra rb? (ps.set! i rp') p
      base ++
      (shrinkPathTarget t).map (.opDiffNameStatus · ra rb? ps p) ++
      (shrinkRevSpec ra).map (.opDiffNameStatus t · rb? ps p) ++
      rbShrinks ++
      (if ps.size > 1 then .opDiffNameStatus t ra rb? #[] p :: (ps.toList.map fun single => .opDiffNameStatus t ra rb? #[single] p) ++ dropOneCands
       else if ps.size == 1 then [.opDiffNameStatus t ra rb? #[] p] else []) ++
      elemCands
    | .opWorktreeAdd t wt wr? nb? dt f p =>
      let nbShrinks :=
        match nb? with
        | none => []
        | some nb => .opWorktreeAdd t wt wr? none dt f p :: ((shrinkRefName nb).map fun b' => .opWorktreeAdd t wt wr? (some b') dt f p)
      base ++
      (shrinkPathTarget t).map (.opWorktreeAdd · wt wr? nb? dt f p) ++
      (shrinkPathTarget wt).map (.opWorktreeAdd t · wr? nb? dt f p) ++
      (if f then [.opWorktreeAdd t wt wr? nb? dt false p] else []) ++
      (if dt then [.opWorktreeAdd t wt wr? nb? false f p] else []) ++
      (if wr?.isSome then [.opWorktreeAdd t wt none nb? dt f p] else []) ++
      nbShrinks
    | .opWorktreeRemove t wt f p =>
      base ++
      (shrinkPathTarget t).map (.opWorktreeRemove · wt f p) ++
      (shrinkPathTarget wt).map (.opWorktreeRemove t · f p) ++
      (if f then [.opWorktreeRemove t wt false p] else [])
    | .opWithWorktree t wt wr? nb? dt f ins re p =>
      let liftedCands := (retargetStepList wt t ins) ++ ins
      let innerCands := (shrinkInnerList (shrinkStepFuel fuel) ins).map (.opWithWorktree t wt wr? nb? dt f · re p)
      let nbShrinks :=
        match nb? with
        | none => []
        | some nb => .opWithWorktree t wt wr? none dt f ins re p :: ((shrinkRefName nb).map fun b' => .opWithWorktree t wt wr? (some b') dt f ins re p)
      base ++
      liftedCands ++
      (shrinkPathTarget t).map (.opWithWorktree · wt wr? nb? dt f ins re p) ++
      (shrinkPathTarget wt).map (.opWithWorktree t · wr? nb? dt f ins re p) ++
      innerCands ++
      (if f then [.opWithWorktree t wt wr? nb? dt false ins re p] else []) ++
      (if dt then [.opWithWorktree t wt wr? nb? false f ins re p] else []) ++
      (if re then [.opWithWorktree t wt wr? nb? dt f ins false p] else []) ++
      (if wr?.isSome then [.opWithWorktree t wt none nb? dt f ins re p] else []) ++
      nbShrinks
    | .opTimeoutProbe t k =>
      let k' := k % 4
      (shrinkPathTarget t).map (.opTimeoutProbe · k) ++
      (if k != k' then [.opTimeoutProbe t k'] else [])
    | _ => base
  cands.filter (· != step)

/-- Shrink a single `GitFuzzStep` into strictly simpler candidate steps for delta debugging. -/
def shrinkStep (step : GitFuzzStep) : List GitFuzzStep :=
  shrinkStepFuel 2 step

/-- Lightweight generator state tracking plausible live files, branches, and repositories. -/
structure GenContext where
  /-- Candidate repository-relative file paths introduced in the episode. -/
  knownFiles : Array String := #["a.txt", "b.txt", "a", "dir/c.txt", "with space.txt", "exec.sh", "debug.log"]
  /-- Candidate branch names introduced in the episode. -/
  knownBranches : Array String := #["main", "feat", "topic", "conflict"]
  /-- Approximate number of commits created so far. -/
  commitHint : Nat := 0
  /-- Whether `repoA` has likely been initialized. -/
  hasRepoA : Bool := false
  /-- Whether `repoB` has likely been initialized. -/
  hasRepoB : Bool := false
  /-- Whether `bareRepo` has likely been initialized. -/
  hasBare : Bool := false
  /-- Whether `bareWt` has likely been added as a linked worktree of `bareRepo`. -/
  hasBareWt : Bool := false
  /-- Whether `cloneRepo` has likely been created. -/
  hasClone : Bool := false
  /-- Whether `wt1` has likely been added as a worktree. -/
  hasWt1 : Bool := false
  /-- Whether `wt2` has likely been added as a worktree. -/
  hasWt2 : Bool := false
  /-- Whether a merge conflict was recently created in `repoA`. -/
  hasConflict : Bool := false
  /-- Repository-relative path used for the latest generated merge conflict. -/
  conflictPath : String := "conflict.txt"
  /-- Second branch name (`mc_b` or `mc_d`) created by the latest `gitRawCreateMergeConflict`. -/
  conflictBranchB : String := "mc_b"
  /-- Branch name currently attached to `wt1`, if `wt1` is active. -/
  wt1Branch? : Option String := none
  /-- Branch name currently attached to `wt2`, if `wt2` is active. -/
  wt2Branch? : Option String := none
  /-- Monotonic counter generating collision-free worktree branch names. -/
  wtBrSeq : Nat := 0
  /-- Monotonic counter generating collision-free merge-conflict branch pairs. -/
  mcSeq : Nat := 0
  /-- Remaining conflict-probe stages (`3`: checkout, `2`: switch, `1`: commit, `0`: reset). -/
  conflictStage : Nat := 0
  /-- Remaining dirty-diverged stages (`2`: checkout, `1`: switch). -/
  dirtyDivStage : Nat := 0
  /-- Newly attached worktree branch queued for a `switch` `branchInUse` probe. -/
  pendingSwInUse? : Option String := none
  /-- Newly attached worktree branch queued for a `checkout` `branchInUse` probe. -/
  pendingCoInUse? : Option String := none
  /-- Newly created clean branch in `repoA` queued for a non-force `deleteBranch` `ok` probe. -/
  pendingDelBr? : Option String := none
  /-- Newly created unlocked worktree slot queued for a dirty write + non-force remove probe. -/
  pendingDirtyWtWrite? : Option SlotId := none
  /-- Whether `wt1` is currently locked via `git worktree lock`. -/
  wt1Locked : Bool := false
  /-- Whether `wt2` is currently locked via `git worktree lock`. -/
  wt2Locked : Bool := false
  /-- Whether `repoA` currently has an untracked non-UTF-8 file awaiting a `status` probe. -/
  hasBadUtf8InRepoA : Bool := false
  /-- Whether `repoA` just ran `status` on `badUtf8FileBytes` and should unlink it next. -/
  justProbedBadUtf8 : Bool := false
  /-- Files written to `repoA` during this episode (high-hit pool for remove/chmod). -/
  liveFiles : Array String := #[]
  /-- Empty directories created in `repoA` during this episode. -/
  liveDirs : Array String := #[]
  /-- Whether `repoA` has diverged branches (`mc_a` vs `mc_b`) with differing `conflict.txt`. -/
  hasDiverged : Bool := false
  /-- Whether `repoA` just completed a `reset --hard` on a diverged conflict pair. -/
  justResetDiverged : Bool := false
  /-- Whether `conflictPath` has been modified unstaged on disk after diverging. -/
  hasDirtyConflictFile : Bool := false
  /-- Whether `wt1` has received an unstaged/untracked write since creation. -/
  hasDirtyWt1 : Bool := false
  /-- Linked worktree slot that just received a dirty write, ready for non-force `worktreeRemove`. -/
  dirtyWtSlot? : Option SlotId := none
  deriving Repr, Inhabited

private def activeWtBranch? (ctx : GenContext) : Option String :=
  match ctx.wt1Branch? with
  | some b => some b
  | none => ctx.wt2Branch?

private def activeWtSlot? (ctx : GenContext) : Option SlotId :=
  if ctx.hasWt1 then some .wt1
  else if ctx.hasWt2 then some .wt2
  else none

private def clearWtSlotState (ctx : GenContext) (tgt : PathTarget) : GenContext :=
  match tgt with
  | .slot .wt1 =>
    { ctx with
      hasWt1 := false
      wt1Branch? := none
      wt1Locked := false
      hasDirtyWt1 := false
      pendingSwInUse? := if ctx.pendingSwInUse? == ctx.wt1Branch? then none else ctx.pendingSwInUse?
      pendingCoInUse? := if ctx.pendingCoInUse? == ctx.wt1Branch? then none else ctx.pendingCoInUse?
      pendingDirtyWtWrite? := if ctx.pendingDirtyWtWrite? == some .wt1 then none else ctx.pendingDirtyWtWrite?
      dirtyWtSlot? := if ctx.dirtyWtSlot? == some .wt1 then none else ctx.dirtyWtSlot? }
  | .slot .wt2 =>
    { ctx with
      hasWt2 := false
      wt2Branch? := none
      wt2Locked := false
      pendingSwInUse? := if ctx.pendingSwInUse? == ctx.wt2Branch? then none else ctx.pendingSwInUse?
      pendingCoInUse? := if ctx.pendingCoInUse? == ctx.wt2Branch? then none else ctx.pendingCoInUse?
      pendingDirtyWtWrite? := if ctx.pendingDirtyWtWrite? == some .wt2 then none else ctx.pendingDirtyWtWrite?
      dirtyWtSlot? := if ctx.dirtyWtSlot? == some .wt2 then none else ctx.dirtyWtSlot? }
  | _ => ctx

private def validRepoSlots : Array SlotId := #[
  .repoA, .repoB, .subDir, .wt1, .wt2, .bareWt, .cloneRepo, .symLinkDir
]

private def hostileStrings : Array String := #[
  "",
  "\x00",
  "bad\x00path",
  "../outside",
  "/nonexistent_leanswe/passwd",
  ".git/HEAD",
  ".git/config",
  "-f",
  "--upload-pack=evil",
  "--detach",
  "-b",
  ":(exclude)a.txt",
  ":!a.txt",
  "*.txt",
  "a//b",
  "./a",
  "   ",
  "\n",
  "bad\x7fchar",
  "repo_cr\r",
  "dir_nl\n",
  "out/missing/../../repoA/nested",
  "https://127.0.0.1:1/x.git",
  "host:repo.git",
  String.ofList (List.replicate 260 'x'),
  String.ofList (List.replicate 4200 'a')
]

private def hostileRefNames : Array String := #[
  "HEAD",
  "@",
  "",
  "-bad",
  "/leading",
  "trailing/",
  "a..b",
  "a//b",
  "a@{0}",
  "foo.lock",
  "foo/.bar",
  "foo/bar.",
  "bad name",
  "bad\nname",
  String.ofList (List.replicate 245 'r'),
  String.ofList (List.replicate 1050 'r')
]

private def validBranchNames : Array String := #[
  "main", "feat", "topic", "bugfix", "dev/sub", "rel-1.0", "foo", "conflict", "unmerged", "v1",
  "refs/heads/foo"
]

private def tagNamesPool : Array String := #[
  "v1", "main", "feat", "conflict", "rel-1.0"
]

private def validRelFiles : Array String := #[
  "a.txt",
  "b.txt",
  "a",
  "a/b.txt",
  "dir/c.txt",
  "sub/x.txt",
  "with space.txt",
  "exec.sh",
  "moved.txt",
  "empty.txt",
  ".gitignore",
  ".gitattributes",
  "debug.log",
  "keep.log",
  "build/out.o",
  "rootonly.txt",
  "sub/rootonly.txt",
  "conflict.txt",
  "already exists.txt",
  "local changes.txt",
  "not a git repository.txt",
  "nothing to commit.txt",
  "used by worktree.txt",
  "sym/'not a git repository'",
  "sym/a\nfatal: not a git repository",
  "wt' is not fully merged/sub",
  "bad\"not a git repository\"file",
  "bs\"not a git repository\\\"end",
  "quote\"name.txt",
  "quote'single.txt",
  "tab\tname.txt",
  "back\\slash.txt",
  "foo/keep.txt",
  "foo/drop.txt",
  "sub/d1.txt",
  "sub/d9.txt",
  "1.txt",
  "sp ",
  "crlf.txt",
  "a1.txt",
  "a[12].txt",
  "b*.txt",
  "c?.txt",
  "d\\e.txt",
  ":colon.txt",
  ":(top)x.txt",
  "-dash.txt"
]

private def showAndAddExtraPaths : Array String := #[
  "dir", "sub", "dir/", "sub/", ".", "./", "./a.txt", "link.txt", "symdir", "symdir/c.txt", "missing.txt",
  "conflict.txt", "already exists.txt", "local changes.txt", "debug.log", "build",
  "sub/d1.txt", "foo/keep.txt", "foo/drop.txt", "sp ", "1.txt", "crlf.txt",
  "a1.txt", "a[12].txt", "b*.txt", "c?.txt", "d\\e.txt", ":colon.txt", ":(top)x.txt", "-dash.txt"
]

private def badUtf8FileBytes : ByteArray :=
  ByteArray.mk #[0x62, 0x61, 0x64, 0xff, 0x2e, 0x74, 0x78, 0x74]

private def badUtf8DirBytes : ByteArray :=
  ByteArray.mk #[0x64, 0x69, 0x72, 0xff, 0x31]

private def badUtf8LinkBytes : ByteArray :=
  ByteArray.mk #[0x73, 0x79, 0x6d, 0xff, 0x6c]

private def hostileRevSpecs : Array String := #[
  "",
  "-f",
  "HEAD@{0}",
  "@{0}",
  "main@{0}",
  "@{-1}",
  "ORIG_HEAD",
  ":/msg",
  ":/init",
  "HEAD^{tree}",
  "HEAD:a.txt",
  "a..b",
  "dead",
  "0000000",
  String.ofList (List.replicate 40 '0'),
  String.ofList (List.replicate 64 'f'),
  "missing-branch",
  "HEAD~99",
  "HEAD^2",
  "bad rev",
  "conflict"
]

private def validRevSpecs (ctx : GenContext) : Array String :=
  let base := #[
    "HEAD", "@", "HEAD^0", "HEAD~0", "HEAD~1", "HEAD^1",
    "main", "main^0", "main~0", "feat", "topic", "v1", "v1^0",
    "origin", "origin/main", "conflict"
  ]
  let extra := ctx.knownBranches.flatMap fun b => #[s!"{b}~1", s!"{b}^0"]
  base ++ extra

private def genPathTarget (rng : Rng) (ctx : GenContext) : PathTarget × Rng :=
  let (hostile, r1) := rng.chance 20 100
  if hostile then
    let (kind, r2) := r1.nextNat 3
    if kind == 0 then
      let (s, r3) := r2.chooseWeighted
        #[(2, .missingDir), (2, .plainFile), (2, .bareRepo), (1, .badUtf8Dir),
          (1, .symLinkDir), (2, .danglingSym), (2, .symLoopA)] .missingDir
      (.slot s, r3)
    else if kind == 1 then
      let (pickInvalidPath, r3a) := r2.chance 35 100
      if pickInvalidPath then
        let (rawS, r3) := r3a.choose #["", "\x00", "bad\x00path"] ""
        (.raw rawS, r3)
      else
        let (rawS, r3) := r3a.choose hostileStrings ""
        (.raw rawS, r3)
    else
      let (pickFileMkdir, r3a) := r2.chance 15 100
      if pickFileMkdir then
        (.subRel .plainFile "not a git repository", r3a)
      else
        let (s, r3) := r3a.choose validRepoSlots .repoA
        let (rel, r4) := r3.choose #["../escape", "nonexistent", ".git", "", "missing_sub/..", "sub/..", "child"] "nonexistent"
        let (useDang, r5) := r4.chance 15 100
        if useDang then (.subRel .danglingSym "child", r5)
        else (.subRel s rel, r5)
  else
    let weights : Array (Nat × SlotId) := #[
      (if ctx.hasRepoA then 16 else 4, SlotId.repoA),
      (if ctx.hasRepoB then 5 else 1, SlotId.repoB),
      (if ctx.hasRepoA then 2 else 1, SlotId.subDir),
      (if ctx.hasWt1 then 5 else 0, SlotId.wt1),
      (if ctx.hasWt2 then 4 else 0, SlotId.wt2),
      (if ctx.hasBareWt then 5 else 0, SlotId.bareWt),
      (if ctx.hasBare then 4 else 1, SlotId.bareRepo),
      (if ctx.hasClone then 6 else 0, SlotId.cloneRepo),
      (if ctx.hasRepoA then 2 else 0, SlotId.symLinkDir)
    ] |>.filter (·.1 > 0)
    let (s, r2) := r1.chooseWeighted weights .repoA
    (.slot s, r2)

private def genCloneSource (rng : Rng) : PathTarget × Rng :=
  let (kind, r1) := rng.nextNat 12
  if kind < 4 then
    let (s, r2) := r1.chooseWeighted #[
      (4, .repoA), (2, .bareRepo), (2, .wt1), (1, .wt2), (2, .bareWt),
      (1, .repoB), (1, .plainFile), (1, .danglingSym), (1, .symLoopA)
    ] .repoA
    (.slot s, r2)
  else if kind < 7 then
    let (s, r2) := r1.choose #[.repoA, .bareRepo, .wt1, .bareWt, .plainFile] .repoA
    (.fileUrl s, r2)
  else if kind < 9 then
    let (s, r2) := r1.choose #[.repoA, .bareRepo, .wt1, .bareWt] .repoA
    (.fileUrlLocalhost s, r2)
  else
    let hostileCloneSrcs := hostileStrings.filter (· != "/etc/passwd")
    let (rawS, r2) := r1.choose hostileCloneSrcs "https://127.0.0.1:1/x.git"
    (.raw rawS, r2)

private def genBranchRef (rng : Rng) (ctx : GenContext) : RefName × Rng :=
  let (kind, r1) := rng.nextNat 20
  if kind < 3 then
    let (s, r2) := r1.choose hostileRefNames "HEAD"
    ({ raw := s }, r2)
  else if kind == 3 then
    let (s, r2) := r1.choose #["origin/main", "v1", "conflict", "unmerged"] "origin/main"
    ({ raw := s }, r2)
  else if kind < 13 then
    let (s, r2) := r1.choose #["main", "feat", "topic", "mc_a", "mc_b", "conflict"] "main"
    ({ raw := s }, r2)
  else
    let (s, r2) := r1.choose (validBranchNames ++ ctx.knownBranches) "main"
    ({ raw := s }, r2)

private def genRevSpec (rng : Rng) (ctx : GenContext) : FuzzRevSpec × Rng :=
  let (kind, r1) := rng.nextNat 20
  if kind < 4 then
    let (s, r2) := r1.choose hostileRevSpecs "HEAD@{0}"
    (.raw s, r2)
  else if kind < 6 then
    let (idx, r2) := r1.nextNat 16
    let (len, r3) := r2.nextRange 7 12
    (.shortCommitIdx idx len "dead000", r3)
  else if kind < 10 then
    let (idx, r2) := r1.nextNat 16
    let (fb, r3) := r2.choose #["HEAD", "main", "HEAD~1"] "HEAD"
    (.commitIdx idx fb, r3)
  else
    let (s, r2) := r1.choose (validRevSpecs ctx) "HEAD"
    (.raw s, r2)

private def genRelPath (rng : Rng) (ctx : GenContext) : String × Rng :=
  let (kind, r1) := rng.nextNat 20
  if kind < 4 then
    r1.choose hostileStrings "../outside"
  else if kind < 9 then
    r1.choose showAndAddExtraPaths "dir"
  else
    r1.choose (validRelFiles ++ ctx.knownFiles) "a.txt"

private def genRelPathsArray (rng : Rng) (ctx : GenContext) : Array String × Rng :=
  let (count, r1) := rng.nextRange 0 3
  Id.run do
    let mut cur := r1
    let mut out : Array String := #[]
    for _ in List.range count do
      let (p, nxt) := genRelPath cur ctx
      cur := nxt
      out := out.push p
    return (out, cur)

private def genCommitOptions (rng : Rng) : CommitOptions × Rng :=
  let (hostile, r1) := rng.chance 25 100
  if hostile then
    let (msg, r2) := r1.choose #["", "   ", "\n", "# comment", "bad\x00msg", "ok"] ""
    let (aName?, r3) := r2.choose #[none, some "", some "<>", some "  .  ", some "A\nB", some "Valid"] none
    let (aEmail?, r4) := r3.choose #[none, some "", some "bad<email>", some "ok@example.com"] none
    let (allowEmpty, r5) := r4.nextBool
    ({ message := msg, allowEmpty := allowEmpty, authorName := aName?, authorEmail := aEmail? }, r5)
  else
    let (msg, r2) := r1.choose #["feat: update", "fix: edge\n\nbody", "  pad  \n  \n\n\nline2 \t \r\n\n", "   \n", "# hash line", "msg"] "feat: update"
    let (allowEmpty, r3) := r2.chance 45 100
    let (withAuthor, r4) := r3.nextBool
    let aName? := if withAuthor then some "Fuzz Author" else none
    let aEmail? := if withAuthor then some "fuzz@example.com" else none
    ({ message := msg, allowEmpty := allowEmpty, authorName := aName?, authorEmail := aEmail? }, r4)

private def gitignoreContents : Array ByteArray := #[
  "*.log\n!keep.log\nbuild/\n/rootonly.txt\n".toUTF8,
  "*.log\n# comment\n!debug.log\nsub/*.txt\n".toUTF8,
  "a/b.txt\n[a-c].tmp\n".toUTF8,
  "foo/**\n!foo/keep.txt\n".toUTF8,
  "[[:digit:]].txt\nd[[:digit:]].txt\n".toUTF8,
  "sp\\ \n".toUTF8
]

private def gitattributesContents : Array ByteArray := #[
  "*.txt text\n".toUTF8,
  "*.txt eol=crlf\n".toUTF8,
  "*.txt eol=lf\n".toUTF8,
  "* text=auto\n".toUTF8,
  "*.txt -text\n".toUTF8,
  "*.sh -text\n".toUTF8,
  "*.bin binary\n".toUTF8
]

private def genVfsFileBytes (rng : Rng) (relBytes : ByteArray) : ByteArray × Rng :=
  if relBytes == ".gitignore".toUTF8 then
    rng.choose gitignoreContents ("*.log\n!keep.log\nbuild/\n/rootonly.txt\n".toUTF8)
  else if relBytes == ".gitattributes".toUTF8 then
    rng.choose gitattributesContents ("*.txt text\n".toUTF8)
  else
    let (kind, r1) := rng.nextNat 6
    if kind == 0 then (ByteArray.empty, r1)
    else if kind == 1 then ("hello\n".toUTF8, r1)
    else if kind == 2 then ("updated\n".toUTF8, r1)
    else if kind == 3 then ("line1\r\nline2\r\n".toUTF8, r1)
    else if kind == 4 then (ByteArray.mk #[0x00, 0x01, 0xfe, 0xff, 0x41], r1)
    else r1.nextBytesRange 4 32

private def genVfsRelBytes (rng : Rng) : ByteArray × Rng :=
  let (kind, r1) := rng.nextNat 100
  if kind < 16 then
    (badUtf8FileBytes, r1)
  else if kind < 52 then
    let (name, r2) := r1.choose #[
      "a.txt", "b.txt", "conflict.txt", "dir/c.txt", "a", "a/b.txt",
      "foo/keep.txt", "foo/drop.txt", "1.txt", "sp ", "crlf.txt", "sub/d1.txt"
    ] "a.txt"
    (name.toUTF8, r2)
  else if kind < 68 then
    let (name, r2) := r1.choose #["dir", ".gitignore", "debug.log", "keep.log", "build/out.o", "sub/x.txt"] "dir"
    (name.toUTF8, r2)
  else
    let (name, r2) := r1.choose validRelFiles "a.txt"
    (name.toUTF8, r2)

private def genInnerStep (rng : Rng) (ctx : GenContext) (repoTarget wtTarget : PathTarget) : GitFuzzStep × Rng :=
  let (poison, r0) := rng.chance 25 100
  let (kind, r1) := r0.nextNat 11
  if kind == 0 then
    let (relB, r2) := genVfsRelBytes r1
    let (body, r3) := genVfsFileBytes r2 relB
    let (ex, r4) := r3.nextBool
    let s := match wtTarget with | .slot sl => sl | _ => .wt1
    (.vfsWriteFile s relB body ex, r4)
  else if kind == 1 then
    (.opAdd wtTarget #[] true poison, r1)
  else if kind == 2 then
    let (opts, r2) := genCommitOptions r1
    (.opCommit wtTarget opts poison, r2)
  else if kind == 3 then
    (.opStatus wtTarget poison, r1)
  else if kind == 4 then
    (.opHeadState wtTarget poison, r1)
  else if kind == 5 then
    let (p, r2) := genRelPath r1 ctx
    (.opShowFile wtTarget (.raw "HEAD") p poison, r2)
  else if kind == 6 then
    let (br, r2) := genBranchRef r1 ctx
    let (create, r3) := r2.nextBool
    let (force, r4) := r3.nextBool
    (.opSwitch wtTarget br create none force poison, r4)
  else if kind == 7 then
    let (br, r2) := genBranchRef r1 ctx
    let (force, r3) := r2.nextBool
    (.opCheckout wtTarget (.branch br) force poison, r3)
  else if kind == 8 then
    let (rev, r2) := genRevSpec r1 ctx
    let (mIdx, r3) := r2.nextNat 3
    let mode := if mIdx == 0 then .soft else if mIdx == 1 then .mixed else .hard
    (.opReset wtTarget mode rev poison, r3)
  else if kind == 9 then
    (.opDiffNameStatus wtTarget (.raw "HEAD") none #[] poison, r1)
  else
    let (force, r2) := r1.nextBool
    (.opWorktreeRemove repoTarget wtTarget force poison, r2)

private def genStepKind (rng : Rng) : Nat × Rng :=
  rng.chooseWeighted #[
    (9, 0),
    (3, 1),
    (2, 2),
    (4, 3),
    (3, 4),
    (2, 5),
    (2, 6),
    (5, 7),
    (1, 8),
    (3, 9),
    (2, 37),
    (3, 38),
    (3, 39),
    (6, 10),
    (4, 11),
    (3, 12),
    (3, 13),
    (4, 14),
    (4, 15),
    (5, 16),
    (3, 17),
    (4, 18),
    (9, 19),
    (4, 20),
    (3, 21),
    (4, 22),
    (5, 23),
    (5, 24),
    (8, 25),
    (10, 26),
    (7, 27),
    (8, 28),
    (9, 29),
    (6, 30),
    (4, 31),
    (8, 32),
    (6, 33),
    (6, 34),
    (4, 35),
    (2, 36)
  ] 10

/-- Generate one weighted randomized `GitFuzzStep` and update `GenContext`. -/
def genGitFuzzStep (rng : Rng) (ctx : GenContext) : GitFuzzStep × GenContext × Rng :=
  let (followConflict, r0) := if ctx.hasConflict then rng.chance 82 100 else (false, rng)
  if followConflict then
    let (poison, r1) := r0.chance 25 100
    if ctx.conflictStage == 3 then
      (.opCheckout (.slot .repoA) (.branch { raw := ctx.conflictBranchB }) false poison,
        { ctx with conflictStage := 2 }, r1)
    else if ctx.conflictStage == 2 then
      let (create, r2) := r1.chance 20 100
      let brName := if create then s!"conf_sw_{ctx.mcSeq}" else ctx.conflictBranchB
      let sp? := if create then some (FuzzRevSpec.raw ctx.conflictBranchB) else none
      (.opSwitch (.slot .repoA) { raw := brName } create sp? false poison,
        { ctx with conflictStage := 1 }, r2)
    else if ctx.conflictStage == 1 then
      (.opCommit (.slot .repoA) { message := "conflict commit" } poison,
        { ctx with conflictStage := 0 }, r1)
    else
      let (useReset, r2) := r1.chance 80 100
      if useReset then
        (.opReset (.slot .repoA) .hard (.raw "HEAD") poison,
          { ctx with
            hasConflict := false
            conflictStage := 0
            hasDiverged := true
            justResetDiverged := true
            hasDirtyConflictFile := false
            dirtyDivStage := 0 }, r2)
      else
        (.opAdd (.slot .repoA) #[ctx.conflictPath] false poison,
          { ctx with hasConflict := false, conflictStage := 0, hasDiverged := true }, r2)
  else
  let (followDirtyWrite, r0a) := if ctx.justResetDiverged then r0.chance 80 100 else (false, r0)
  if followDirtyWrite then
    (.vfsWriteFile .repoA ctx.conflictPath.toUTF8 "dirty_div\n".toUTF8 false,
      { ctx with justResetDiverged := false, hasDirtyConflictFile := true, dirtyDivStage := 2 }, r0a)
  else
  let (followDirtyDiv, r0b) :=
    if ctx.hasDiverged && (ctx.dirtyDivStage > 0 || ctx.hasDirtyConflictFile) then r0a.chance 80 100
    else (false, r0a)
  if followDirtyDiv then
    let (poison, r1) := r0b.chance 25 100
    if ctx.dirtyDivStage == 2 then
      (.opCheckout (.slot .repoA) (.branch { raw := ctx.conflictBranchB }) false poison,
        { ctx with dirtyDivStage := 1 }, r1)
    else if ctx.dirtyDivStage == 1 then
      (.opSwitch (.slot .repoA) { raw := ctx.conflictBranchB } false none false poison,
        { ctx with dirtyDivStage := 0, hasDirtyConflictFile := false }, r1)
    else
      let (useSwitch, r2) := r1.chance 55 100
      let ctxCleared := { ctx with hasDirtyConflictFile := false, dirtyDivStage := 0 }
      if useSwitch then
        (.opSwitch (.slot .repoA) { raw := ctx.conflictBranchB } false none false poison, ctxCleared, r2)
      else
        (.opCheckout (.slot .repoA) (.branch { raw := ctx.conflictBranchB }) false poison, ctxCleared, r2)
  else
  let canRmDirtyWt :=
    match ctx.dirtyWtSlot? with
    | some .wt1 => ctx.hasWt1 && !ctx.wt1Locked
    | some .wt2 => ctx.hasWt2 && !ctx.wt2Locked
    | _ => false
  let (followDirtyWtRm, r0c) :=
    if canRmDirtyWt then r0b.chance 80 100 else (false, r0b)
  if followDirtyWtRm then
    let (poison, r1) := r0c.chance 25 100
    let ws := ctx.dirtyWtSlot?.getD .wt1
    (.opWorktreeRemove (.slot .repoA) (.slot ws) false poison, { ctx with dirtyWtSlot? := none }, r1)
  else
  let (followSwInUse, r0sw) :=
    if ctx.pendingSwInUse?.isSome && ctx.hasRepoA then r0c.chance 70 100 else (false, r0c)
  if followSwInUse then
    let (poison, r1) := r0sw.chance 25 100
    let wb := ctx.pendingSwInUse?.getD "wt_sh_0"
    (.opSwitch (.slot .repoA) { raw := wb } false none false poison,
      { ctx with pendingSwInUse? := none, pendingCoInUse? := some wb }, r1)
  else
  let (followCoInUse, r0co) :=
    if ctx.pendingCoInUse?.isSome && ctx.hasRepoA then r0sw.chance 70 100 else (false, r0sw)
  if followCoInUse then
    let (poison, r1) := r0co.chance 25 100
    let wb := ctx.pendingCoInUse?.getD "wt_sh_0"
    (.opCheckout (.slot .repoA) (.branch { raw := wb }) false poison,
      { ctx with pendingCoInUse? := none }, r1)
  else
  let (followDelBr, r0dl) :=
    if ctx.pendingDelBr?.isSome && ctx.hasRepoA then r0co.chance 70 100 else (false, r0co)
  if followDelBr then
    let (poison, r1) := r0dl.chance 25 100
    let db := ctx.pendingDelBr?.getD "del_br_0"
    (.opDeleteBranch (.slot .repoA) { raw := db } false poison, { ctx with pendingDelBr? := none }, r1)
  else
  let canWriteDirtyWt :=
    match ctx.pendingDirtyWtWrite? with
    | some .wt1 => ctx.hasWt1 && !ctx.wt1Locked
    | some .wt2 => ctx.hasWt2 && !ctx.wt2Locked
    | _ => false
  let (followWriteDirtyWt, r0dw) :=
    if canWriteDirtyWt then r0dl.chance 55 100 else (false, r0dl)
  if followWriteDirtyWt then
    let ws := ctx.pendingDirtyWtWrite?.getD .wt1
    let ctx' :=
      if ws == .wt1 then
        { ctx with pendingDirtyWtWrite? := none, hasDirtyWt1 := true, dirtyWtSlot? := some .wt1 }
      else
        { ctx with pendingDirtyWtWrite? := none, dirtyWtSlot? := some .wt2 }
    (.vfsWriteFile ws "dirty_wt.txt".toUTF8 "dirty_wt\n".toUTF8 false, ctx', r0dw)
  else
  let (followBadUtf8Status, r0d) :=
    if ctx.hasBadUtf8InRepoA && ctx.hasRepoA then r0dw.chance 75 100 else (false, r0dw)
  if followBadUtf8Status then
    let (poison, r1) := r0d.chance 25 100
    (.opStatus (.slot .repoA) poison, { ctx with hasBadUtf8InRepoA := false, justProbedBadUtf8 := true }, r1)
  else
  let (followCleanBadUtf8, r0e) :=
    if ctx.justProbedBadUtf8 then r0d.chance 80 100 else (false, r0d)
  if followCleanBadUtf8 then
    (.vfsRemoveFile .repoA badUtf8FileBytes, { ctx with justProbedBadUtf8 := false }, r0e)
  else
  let ctx :=
    if ctx.justResetDiverged || ctx.justProbedBadUtf8 || ctx.pendingSwInUse?.isSome ||
        ctx.pendingCoInUse?.isSome || ctx.pendingDelBr?.isSome || ctx.pendingDirtyWtWrite?.isSome then
      { ctx with
        justResetDiverged := false
        justProbedBadUtf8 := false
        pendingSwInUse? := none
        pendingCoInUse? := none
        pendingDelBr? := none
        pendingDirtyWtWrite? := none }
    else ctx
  let (kind, r1) := genStepKind r0e
  let (poison, r2) := r1.chance 25 100
  let (target, r3) := genPathTarget r2 ctx
  match kind with
  | 0 =>
    let wt1W := if ctx.hasWt1 && !ctx.hasDirtyWt1 && !ctx.wt1Locked then 7 else if ctx.hasWt1 then 4 else 1
    let wt2W := if ctx.hasWt2 && !ctx.wt2Locked then 5 else if ctx.hasWt2 then 3 else 1
    let (slot, r4) := r3.chooseWeighted #[
      (6, .repoA), (2, .repoB), (1, .subDir), (wt1W, .wt1), (wt2W, .wt2), (1, .bareWt), (1, .cloneRepo)
    ] .repoA
    let (pickConf, r4b) := if ctx.hasDiverged && slot == .repoA then r4.chance 60 100 else (false, r4)
    let (cleanWtDirty, r4c) :=
      if !pickConf && ((slot == .wt1 && ctx.hasWt1) || (slot == .wt2 && ctx.hasWt2)) then r4b.chance 70 100
      else (false, r4b)
    let (relB, r5) :=
      if pickConf then (ctx.conflictPath.toUTF8, r4c)
      else if cleanWtDirty then ("dirty_wt.txt".toUTF8, r4c)
      else genVfsRelBytes r4c
    let (body, r6) :=
      if pickConf then ("dirty_local\n".toUTF8, r5)
      else if cleanWtDirty then ("dirty_wt\n".toUTF8, r5)
      else genVfsFileBytes r5 relB
    let (ex, r7) := r6.nextBool
    let ctx1 :=
      match String.fromUTF8? relB with
      | some str =>
        let kf := if ctx.knownFiles.contains str then ctx.knownFiles else ctx.knownFiles.push str
        let lf := if slot == .repoA && !ctx.liveFiles.contains str then ctx.liveFiles.push str else ctx.liveFiles
        { ctx with knownFiles := kf, liveFiles := lf }
      | none =>
        if slot == .repoA && ctx.hasRepoA then { ctx with hasBadUtf8InRepoA := true } else ctx
    let ctx' :=
      if pickConf then { ctx1 with hasDirtyConflictFile := true }
      else if slot == .wt1 && ctx.hasWt1 && !ctx.wt1Locked then
        { ctx1 with hasDirtyWt1 := true, dirtyWtSlot? := some .wt1 }
      else if slot == .wt2 && ctx.hasWt2 && !ctx.wt2Locked then
        { ctx1 with dirtyWtSlot? := some .wt2 }
      else ctx1
    (.vfsWriteFile slot relB body ex, ctx', r7)
  | 1 =>
    let (slot, r4) := r3.chooseWeighted #[(5, .repoA), (2, .repoB), (2, .wt1), (1, .bareWt)] .repoA
    let (nonUtf8, r5) := r4.chance 15 100
    if nonUtf8 then
      (.vfsMkdir slot badUtf8DirBytes, ctx, r5)
    else
      let (pickEmpty, r5b) := r5.chance 55 100
      let (dirName, r6) :=
        if pickEmpty then r5b.choose #["emptyDir", "emptyDir2"] "emptyDir"
        else r5b.choose #["dir/sub", "nested/leaf", "sub", "build", "a"] "dir/sub"
      let ctx' :=
        if slot == .repoA && !ctx.liveDirs.contains dirName then
          { ctx with liveDirs := ctx.liveDirs.push dirName }
        else ctx
      (.vfsMkdir slot dirName.toUTF8, ctx', r6)
  | 2 =>
    let (slot, r4) := r3.choose #[.repoA, .repoB, .wt1] .repoA
    let (nonUtf8, r5) := r4.chance 15 100
    if nonUtf8 then
      (.vfsSymlink slot badUtf8LinkBytes badUtf8FileBytes, ctx, r5)
    else
      let (pair, r6) := r5.choose #[
        ("link.txt", "a.txt"),
        ("symdir", "dir"),
        ("symdir", "sub"),
        ("dir/sym", "missing"),
        ("dangling", "missing_target"),
        ("outlink", "../outside")
      ] ("link.txt", "a.txt")
      (.vfsSymlink slot pair.1.toUTF8 pair.2.toUTF8, ctx, r6)
  | 3 =>
    let (slot, r4) := r3.chooseWeighted #[(6, .repoA), (2, .repoB), (2, .wt1), (1, .wt2), (1, .bareWt)] .repoA
    let (dropBad, r5) := r4.chance 10 100
    if dropBad then
      (.vfsRemoveFile slot badUtf8FileBytes, ctx, r5)
    else
      let (hotPick, r5b) := r5.chance 65 100
      if hotPick && slot == .repoA && !ctx.liveFiles.isEmpty then
        let (rel, r6) := r5b.choose ctx.liveFiles "a.txt"
        let ctx' := { ctx with liveFiles := ctx.liveFiles.filter (· != rel) }
        (.vfsRemoveFile slot rel.toUTF8, ctx', r6)
      else if hotPick then
        let (rel, r6) := r5b.choose #[
          "a.txt", "b.txt", "conflict.txt", "dir/c.txt", "a", "a/b.txt",
          "link.txt", ".gitignore", ".gitattributes"
        ] "a.txt"
        (.vfsRemoveFile slot rel.toUTF8, ctx, r6)
      else
        let (rel, r6) := r5b.choose (validRelFiles ++ #["dir", "link.txt", "symdir"] ++ ctx.knownFiles) "a.txt"
        (.vfsRemoveFile slot rel.toUTF8, ctx, r6)
  | 4 =>
    let (slot, r4) := r3.chooseWeighted #[(6, .repoA), (2, .repoB), (2, .wt1)] .repoA
    let (nonUtf8, r5) := r4.chance 10 100
    if nonUtf8 then
      (.vfsRemoveDir slot badUtf8DirBytes, ctx, r5)
    else
      let (hotDir, r5b) := r5.chance 70 100
      if hotDir && slot == .repoA && !ctx.liveDirs.isEmpty then
        let (dirName, r6) := r5b.choose ctx.liveDirs "emptyDir"
        let ctx' := { ctx with liveDirs := ctx.liveDirs.filter (· != dirName) }
        (.vfsRemoveDir slot dirName.toUTF8, ctx', r6)
      else if hotDir then
        let (dirName, r6) := r5b.choose #["emptyDir", "emptyDir2", "dir/sub", "nested/leaf"] "emptyDir"
        (.vfsRemoveDir slot dirName.toUTF8, ctx, r6)
      else
        let (dirName, r6) := r5b.choose #["emptyDir", "dir/sub", "dir", "sub", "a.txt", "a"] "emptyDir"
        (.vfsRemoveDir slot dirName.toUTF8, ctx, r6)
  | 5 =>
    let (slot, r4) := r3.choose #[.repoB, .subDir, .wt2] .repoB
    let (searchable, r5) := r4.nextBool
    (.vfsChmodDir slot searchable, ctx, r5)
  | 6 =>
    let (useBare, r4a) := r3.chance 30 100
    let (repoSl, wtSl, r4) :=
      if useBare && ctx.hasBareWt then (.bareRepo, .bareWt, r4a)
      else
        let (ws, rW) := r4a.choose #[.wt1, .wt2] .wt1
        (.repoA, ws, rW)
    let (lock, r5) := r4.nextBool
    let (hasRsn, r6) := r5.nextBool
    let (rsn, r7) := r6.choose #[
      "maintenance", "ci lock", "", "   ", "  foo  ", "not a git repository", "already exists", "not found"
    ] "maintenance"
    let ctx' :=
      if repoSl == .repoA && wtSl == .wt1 && ctx.hasWt1 then { ctx with wt1Locked := lock }
      else if repoSl == .repoA && wtSl == .wt2 && ctx.hasWt2 then { ctx with wt2Locked := lock }
      else ctx
    (.gitRawLockWorktree repoSl wtSl lock (if hasRsn then some rsn else none), ctx', r7)
  | 7 =>
    let (dropMH, r4) := r3.nextBool
    let bA := s!"mc_a_{ctx.mcSeq}"
    let bB := s!"mc_b_{ctx.mcSeq}"
    let (relPath, r6) := r4.choose #[
      "conflict.txt",
      "not a git repository.txt",
      "nothing to commit.txt",
      "used by worktree.txt",
      "local changes.txt",
      "a.txt"
    ] "conflict.txt"
    (.gitRawCreateMergeConflict .repoA { raw := bA } { raw := bB } relPath dropMH,
      { ctx with
        hasConflict := true
        conflictStage := 3
        mcSeq := ctx.mcSeq + 1
        conflictPath := relPath
        conflictBranchB := bB }, r6)
  | 8 =>
    (.gitRawCreateCrissCrossMerge .repoA, ctx, r3)
  | 9 =>
    let (repoSl, r4) := r3.chooseWeighted #[(5, .repoA), (2, .bareRepo), (1, .cloneRepo)] .repoA
    let (tagName, r5) := r4.choose tagNamesPool "v1"
    let (rv, r6) := genRevSpec r5 ctx
    (.gitRawCreateTag repoSl { raw := tagName } rv, ctx, r6)
  | 37 =>
    let (slot, r4) := r3.chooseWeighted #[(3, .wt1), (3, .wt2), (2, .bareWt)] .wt1
    let ctx' :=
      if slot == .bareWt then { ctx with hasBareWt := false }
      else clearWtSlotState ctx (.slot slot)
    (.vfsRemoveTree slot, ctx', r4)
  | 38 =>
    let (slot, r4) := r3.chooseWeighted #[(6, .repoA), (2, .repoB), (1, .wt1)] .repoA
    let (hotDir, r4b) := r4.chance 75 100
    let (sub, r5) :=
      if hotDir && slot == .repoA && !ctx.liveDirs.isEmpty then
        r4b.choose ctx.liveDirs "emptyDir"
      else
        r4b.choose #["emptyDir", "emptyDir2", "sub", "build", "dir/sub"] "emptyDir"
    let (searchable, r6) := r5.nextBool
    (.vfsChmodSubDir slot sub.toUTF8 searchable, ctx, r6)
  | 39 =>
    let (slot, r4) := r3.chooseWeighted #[(6, .repoA), (2, .repoB), (1, .wt1)] .repoA
    let (hotPick, r4b) := r4.chance 70 100
    let (relB, r5) :=
      if hotPick && slot == .repoA && !ctx.liveFiles.isEmpty then
        let (nm, rN) := r4b.choose ctx.liveFiles "a.txt"
        (nm.toUTF8, rN)
      else if hotPick then
        let (nm, rN) := r4b.choose #["a.txt", "b.txt", "conflict.txt", "dir/c.txt", "a", "1.txt"] "a.txt"
        (nm.toUTF8, rN)
      else
        genVfsRelBytes r4b
    let (executable, r6) := r5.nextBool
    (.vfsSetFileExecutable slot relB executable, ctx, r6)
  | 10 =>
    let (forceBad, r4) := r3.chance 15 100
    if forceBad then
      let (rawS, r5) := r4.choose #["", "\x00", "bad\x00path"] ""
      (.opIsRepo (.raw rawS) poison, ctx, r5)
    else
      (.opIsRepo target poison, ctx, r4)
  | 11 =>
    let (pickNonRepo, r4) := r3.chance 25 100
    if pickNonRepo then
      let (t, r5) := r4.choose #[PathTarget.subRel .repoA "..", PathTarget.raw ".", PathTarget.slot .bareRepo] (.raw ".")
      (.opRepoRoot t poison, ctx, r5)
    else
      (.opRepoRoot target poison, ctx, r4)
  | 12 => (.opCommonDir target poison, ctx, r3)
  | 13 => (.opHeadCommit target poison, ctx, r3)
  | 14 => (.opHeadBranch target poison, ctx, r3)
  | 15 => (.opHeadState target poison, ctx, r3)
  | 16 =>
    let (rev, r4) := genRevSpec r3 ctx
    (.opRevParseCommit target rev poison, ctx, r4)
  | 17 =>
    let (aIdx, r4) := r3.nextNat 16
    let (bIdx, r5) := r4.nextNat 16
    let (useRaw, r6) := r5.chance 20 100
    let (rawA?, rawB?, r7) :=
      if useRaw then
        let (hA, rA) := r6.choose hostileRevSpecs "dead"
        (some hA, none, rA)
      else (none, none, r6)
    (.opIsAncestor target aIdx bIdx rawA? rawB? poison, ctx, r7)
  | 18 =>
    let (aIdx, r4) := r3.nextNat 16
    let (bIdx, r5) := r4.nextNat 16
    let (useRaw, r6) := r5.chance 20 100
    let (rawA?, rawB?, r7) :=
      if useRaw then
        let (hB, rB) := r6.choose hostileRevSpecs "dead"
        (none, some hB, rB)
      else (none, none, r6)
    (.opMergeBase target aIdx bIdx rawA? rawB? poison, ctx, r7)
  | 19 => (.opStatus target poison, ctx, r3)
  | 20 =>
    let (cleanDiff, r4a) := r3.chance 50 100
    if cleanDiff then
      let (useHead1, r4b) := r4a.chance 45 100
      let revA := if useHead1 then FuzzRevSpec.raw "HEAD~1" else FuzzRevSpec.raw "HEAD"
      let (withB, r4c) := r4b.chance 40 100
      let revB? := if withB then some (FuzzRevSpec.raw "HEAD") else none
      (.opDiffNameStatus (.slot .repoA) revA revB? #[] poison, ctx, r4c)
    else
      let (revA, r4) := genRevSpec r4a ctx
      let (hasB, r5) := r4.nextBool
      let (revB?, r6) :=
        if hasB then
          let (rb, rB) := genRevSpec r5 ctx
          (some rb, rB)
        else (none, r5)
      let (emptyPs, r6b) := r6.chance 50 100
      let (ps, r7) := if emptyPs then (#[], r6b) else genRelPathsArray r6b ctx
      (.opDiffNameStatus target revA revB? ps poison, ctx, r7)
  | 21 => (.opListWorktrees target poison, ctx, r3)
  | 22 =>
    let (cleanShow, r4a) := r3.chance 45 100
    let (rev, r4) := if cleanShow then (.raw "HEAD", r4a) else genRevSpec r4a ctx
    let (pickSpecial, r5a) := r4.chance 30 100
    let (rel, r5) :=
      if pickSpecial then
        r5a.choose #["dir", "sub", "link.txt", "symdir", "symdir/c.txt", "a.txt", "conflict.txt", "tab\tname.txt"] "a.txt"
      else genRelPath r5a ctx
    (.opShowFile (if cleanShow then .slot .repoA else target) rev rel poison, ctx, r5)
  | 23 =>
    let (initSlot, r4) := r3.chooseWeighted #[
      (4, PathTarget.slot .repoA),
      (3, PathTarget.slot .repoB),
      (3, PathTarget.slot .bareRepo),
      (1, PathTarget.slot .plainFile),
      (1, PathTarget.slot .danglingSym),
      (1, PathTarget.slot .symLoopA),
      (1, PathTarget.slot .symLinkDir),
      (1, PathTarget.subRel .missingDir "missing_sub/.."),
      (1, PathTarget.slot .badUtf8Dir),
      (1, PathTarget.raw "repo_cr\r"),
      (1, PathTarget.raw "dir_nl\n"),
      (1, PathTarget.raw "")
    ] (.slot .repoA)
    let (bare, r5) :=
      if initSlot == .slot .bareRepo then (true, r4)
      else if initSlot == .slot .plainFile ||
          initSlot == .slot .symLoopA || initSlot == .raw "" then
        r4.chance 20 100
      else (false, r4)
    let (hasBr, r6) := r5.nextBool
    let (br, r7) := genBranchRef r6 ctx
    let initBr? := if hasBr then some br else none
    let ctx' :=
      if initSlot == .slot .bareRepo && bare then { ctx with hasBare := true }
      else if initSlot == .slot .repoB && !bare && initBr?.all (fun b => isValidRefNameStr b.raw) then
        { ctx with hasRepoB := true }
      else if initSlot == .slot .repoA && !bare && initBr?.all (fun b => isValidRefNameStr b.raw) then
        { ctx with hasRepoA := true }
      else ctx
    (.opInit initSlot bare initBr? poison, ctx', r7)
  | 24 =>
    let (cleanClone, r4a) := r3.chance 55 100
    if cleanClone then
      let (probeExists, r4e) := r4a.chance 25 100
      if probeExists then
        (.opClone (.slot .repoA) (.slot .plainFile) {} poison, ctx, r4e)
      else
        let (bareClone, r4b) := r4e.chance 20 100
        let dst := if bareClone then PathTarget.slot .bareRepo else PathTarget.slot .cloneRepo
        let ctx' :=
          if bareClone then { ctx with hasBare := true }
          else { ctx with hasClone := true }
        (.opClone (.slot .repoA) dst { bare := bareClone } poison, ctx', r4b)
    else
      let (src, r4) := genCloneSource r4a
      let (dst, r5) := r4.chooseWeighted #[
        (5, PathTarget.slot .cloneRepo),
        (2, PathTarget.slot .bareRepo),
        (2, PathTarget.slot .repoB),
        (3, PathTarget.slot .plainFile),
        (1, PathTarget.slot .danglingSym),
        (1, PathTarget.slot .badUtf8Dir),
        (1, PathTarget.raw "-f")
      ] (.slot .cloneRepo)
      let (bare, r6) :=
        if dst == .slot .bareRepo then (true, r5)
        else if dst == .slot .cloneRepo || dst == .slot .repoB || dst == .slot .danglingSym then (false, r5)
        else r5.chance 30 100
      let (hasDepth, r7) := r6.chance 45 100
      let (depthVal, r8) := r7.nextRange 0 3
      let (hasBr, r9) := r8.chance 35 100
      let (pickAlpha, r9b) := r9.chance 25 100
      let (br, r10) :=
        if pickAlpha then ({ raw := "alpha" }, r9b)
        else genBranchRef r9b ctx
      let (singleBr, r11) := r10.nextBool
      let opts : CloneOptions := {
        bare := bare
        depth? := if hasDepth then some depthVal else none
        branch? := if hasBr then some br.raw else none
        singleBranch := singleBr
      }
      let ctx' :=
        if dst == .slot .cloneRepo && !bare then { ctx with hasClone := true }
        else if dst == .slot .bareRepo && bare then { ctx with hasBare := true }
        else ctx
      (.opClone src dst opts poison, ctx', r11)
  | 25 =>
    let (allFlag, r4) := r3.chance 60 100
    let (ps, r5) :=
      if allFlag then
        let (emptyPs, r6) := r4.chance 80 100
        if emptyPs then (#[], r6) else genRelPathsArray r6 ctx
      else
        genRelPathsArray r4 ctx
    (.opAdd target ps allFlag poison, ctx, r5)
  | 26 =>
    let (opts, r4) := genCommitOptions r3
    (.opCommit target opts poison, { ctx with commitHint := ctx.commitHint + 1 }, r4)
  | 27 =>
    let (preferRepoA, r4a) := r3.chance 65 100
    let brTarget := if preferRepoA then .slot .repoA else target
    let (makeDelBr, r4d) :=
      if brTarget == .slot .repoA && ctx.hasRepoA && ctx.commitHint > 0 then r4a.chance 35 100
      else (false, r4a)
    if makeDelBr then
      let db := s!"del_br_{ctx.wtBrSeq}"
      (.opCreateBranch (.slot .repoA) { raw := db } none false poison,
        { ctx with wtBrSeq := ctx.wtBrSeq + 1, pendingDelBr? := some db }, r4d)
    else
      let (pickMain, r4b) := r4d.chance 35 100
      let (br, r4) :=
        if pickMain then ({ raw := "main" }, r4b)
        else genBranchRef r4b ctx
      let (hasSp, r5) := if pickMain then (false, r4) else r4.chance 20 100
      let (sp?, r6) :=
        if hasSp then
          let (sp, r7) := genRevSpec r5 ctx
          (some sp, r7)
        else (none, r5)
      let (force, r8) := if pickMain then (false, r6) else r6.chance 30 100
      let ctx' :=
        if isValidRefNameStr br.raw && !ctx.knownBranches.contains br.raw then
          { ctx with knownBranches := ctx.knownBranches.push br.raw }
        else ctx
      (.opCreateBranch brTarget br sp? force poison, ctx', r8)
  | 28 =>
    let (preferRepoA, r4a) := r3.chance 75 100
    let delTarget := if preferRepoA then .slot .repoA else target
    let (pickDivUnmerged, r4u) :=
      if ctx.hasDiverged && delTarget == .slot .repoA then r4a.chance 70 100 else (false, r4a)
    if pickDivUnmerged then
      let (force, r5) := r4u.chance 20 100
      (.opDeleteBranch delTarget { raw := ctx.conflictBranchB } force poison, ctx, r5)
    else
      let (pickCore, r4b) := r4u.chance 60 100
      let (br, r4) :=
        if pickCore then
          let (s, rC) := r4b.choose #["feat", "topic", "conflict", "mc_b", "mc_a", "mc_d", "mc_c", "main"] "feat"
          ({ raw := s }, rC)
        else
          genBranchRef r4b ctx
      let (force, r5) := r4.chance 45 100
      (.opDeleteBranch delTarget br force poison, ctx, r5)
  | 29 =>
    let (preferRepoA, r4a) := r3.chance 75 100
    let coRepo := if preferRepoA then .slot .repoA else target
    let wtBr? := activeWtBranch? ctx
    let wtSl? := activeWtSlot? ctx
    let (pickInUseRepo, r4u) :=
      if coRepo == .slot .repoA && wtBr?.isSome then r4a.chance 45 100 else (false, r4a)
    if pickInUseRepo then
      (.opCheckout coRepo (.branch { raw := wtBr?.getD "wt_sh1" }) false poison, ctx, r4u)
    else
      let (pickInUseWt, r4w) :=
        if ctx.hasRepoA && ctx.commitHint > 0 && wtSl?.isSome then r4u.chance 30 100 else (false, r4u)
      if pickInUseWt then
        (.opCheckout (.slot (wtSl?.getD .wt1)) (.branch { raw := "main" }) false poison, ctx, r4w)
      else
        let (pickDiv, r4b) := if ctx.hasDiverged && coRepo == .slot .repoA then r4w.chance 60 100 else (false, r4w)
        if pickDiv then
          let (brStr, r5) := r4b.choose #["mc_b", "mc_a", "mc_d", "mc_c", "main", "feat"] "mc_b"
          (.opCheckout coRepo (.branch { raw := brStr }) false poison, ctx, r5)
        else
          let (kindCo, r4) := r4b.nextNat 5
          let (coTarget, r5) :=
            if kindCo < 2 then
              let (br, r6) := genBranchRef r4 ctx
              (FuzzCheckoutTarget.branch br, r6)
            else if kindCo == 2 then
              (FuzzCheckoutTarget.ref (.raw "HEAD~1"), r4)
            else if kindCo == 3 then
              let (idx, r6) := r4.nextNat 16
              let (useUnknown, r7) := r6.chance 20 100
              let raw? := if useUnknown then some (String.ofList (List.replicate 40 '0')) else none
              (FuzzCheckoutTarget.commitIdx idx raw?, r7)
            else
              let (rev, r6) := genRevSpec r4 ctx
              (FuzzCheckoutTarget.ref rev, r6)
          let (force, r6) := r5.chance 20 100
          (.opCheckout coRepo coTarget force poison, ctx, r6)
  | 30 =>
    let (preferRepoA, r3a) := r3.chance 75 100
    let swTarget := if preferRepoA then .slot .repoA else target
    let wtBr? := activeWtBranch? ctx
    let wtSl? := activeWtSlot? ctx
    let (pickInUseRepo, r3u) :=
      if swTarget == .slot .repoA && wtBr?.isSome then r3a.chance 45 100 else (false, r3a)
    if pickInUseRepo then
      (.opSwitch swTarget { raw := wtBr?.getD "wt_sh1" } false none false poison, ctx, r3u)
    else
      let (pickInUseWt, r3w) :=
        if ctx.hasRepoA && ctx.commitHint > 0 && wtSl?.isSome then r3u.chance 35 100 else (false, r3u)
      if pickInUseWt then
        (.opSwitch (.slot (wtSl?.getD .wt1)) { raw := "main" } false none false poison, ctx, r3w)
      else
        let (pickDiv, r3d) :=
          if ctx.hasDiverged && swTarget == .slot .repoA then r3w.chance 55 100 else (false, r3w)
        if pickDiv then
          let (brStr, r4) := r3d.choose #["mc_b", "mc_a", "mc_d", "mc_c", "main", "feat"] "mc_b"
          (.opSwitch swTarget { raw := brStr } false none false poison, ctx, r4)
        else
          let (br, r4) := genBranchRef r3d ctx
          let (create, r5) := r4.nextBool
          let (hasSp, r6) := if create then r5.nextBool else r5.chance 15 100
          let (sp?, r7) :=
            if hasSp then
              let (sp, r8) := genRevSpec r6 ctx
              (some sp, r8)
            else (none, r6)
          let (force, r8) := r7.chance 35 100
          let ctx' :=
            if create && isValidRefNameStr br.raw && !ctx.knownBranches.contains br.raw then
              { ctx with knownBranches := ctx.knownBranches.push br.raw }
            else ctx
          (.opSwitch swTarget br create sp? force poison, ctx', r8)
  | 31 =>
    let (modeIdx, r4) := r3.nextNat 3
    let mode :=
      if modeIdx == 0 then ResetMode.soft
      else if modeIdx == 1 then ResetMode.mixed
      else ResetMode.hard
    let (rev, r5) := genRevSpec r4 ctx
    (.opReset target mode rev poison, ctx, r5)
  | 32 =>
    let (tgtKind, r4a) := r3.nextNat 10
    let fetchTarget :=
      if ctx.hasClone && tgtKind < 6 then .slot .cloneRepo
      else if ctx.hasRepoA && tgtKind == 6 then .slot .subDir
      else target
    let (rem, r4) := r4a.chooseWeighted
      #[(12, "origin"), (2, "."), (2, "../repoB"), (2, "../../repoB"),
        (2, "file://../repoA"), (1, "missing-remote"), (1, "-u"),
        (1, "https://127.0.0.1:1/x.git")] "origin"
    let (hasRs, r5) := r4.chance 40 100
    let (rs?, r6) :=
      if hasRs then
        let (rs, r7) := r5.choose #[
          "main",
          "+refs/heads/*:refs/remotes/origin/*",
          "+refs/pull/*/head:refs/remotes/origin/pr/*",
          "refs/heads/feat*:refs/remotes/origin/feat*",
          "refs/heads/main:refs/remotes/origin/main",
          "refs/heads/main:refs/heads/main",
          "+refs/heads/main:refs/heads/main",
          "refs/heads/side:refs/heads/got",
          "refs/tags/v1:refs/tags/v1",
          "+refs/tags/v1:refs/tags/v1",
          "refs/heads/missing",
          ":bad:refspec"
        ] "main"
        (some rs, r7)
      else (none, r5)
    let (prune, r7) := r6.nextBool
    (.opFetch fetchTarget rem rs? prune poison, ctx, r7)
  | 33 =>
    let (useBare, r4z) := if ctx.hasBare then r3.chance 30 100 else (false, r3)
    if useBare then
      let (cleanBareWt, r4b) := r4z.chance 50 100
      let ctx' := { ctx with hasBareWt := true }
      if cleanBareWt then
        (.opWorktreeAdd (.slot .bareRepo) (.slot .bareWt) (some (.raw "HEAD")) (some { raw := "bare_wtbr" }) false false poison, ctx', r4b)
      else
        let (rv, r5) := genRevSpec r4b ctx
        let (detach, r6) := r5.nextBool
        let (force, r7) := r6.nextBool
        (.opWorktreeAdd (.slot .bareRepo) (.slot .bareWt) (some rv) none detach force poison, ctx', r7)
    else
      let (useRepoA, r4a) := r4z.chance 70 100
      let wtRepo := if useRepoA then .slot .repoA else target
      let repoReady := wtRepo == .slot .repoA && ctx.hasRepoA && ctx.commitHint > 0
      let (preferSlot, r4b) := r4a.chance 80 100
      let (wtTgt, slotFresh, r4) :=
        if preferSlot && !ctx.hasWt1 then (PathTarget.slot .wt1, true, r4b)
        else if preferSlot && !ctx.hasWt2 then (PathTarget.slot .wt2, true, r4b)
        else
          let (chosen, rC) := r4b.chooseWeighted
            #[(4, PathTarget.slot .wt1), (4, PathTarget.slot .wt2),
              (1, PathTarget.slot .plainFile), (1, PathTarget.slot .badUtf8Dir),
              (1, PathTarget.raw "")] (.slot .wt1)
          let fresh :=
            (chosen == .slot .wt1 && !ctx.hasWt1) || (chosen == .slot .wt2 && !ctx.hasWt2)
          (chosen, fresh, rC)
      let (cleanWt, r5a) := r4.chance 65 100
      if cleanWt && repoReady then
        let wtBr? := activeWtBranch? ctx
        let inUseDst :=
          if !ctx.hasWt2 then PathTarget.slot .wt2
          else if !ctx.hasWt1 then PathTarget.slot .wt1
          else if !ctx.hasClone then PathTarget.slot .cloneRepo
          else if !ctx.hasRepoB then PathTarget.slot .repoB
          else PathTarget.slot .bareWt
        let (probeInUse, r5i) :=
          if wtBr?.isSome then r5a.chance 45 100 else r5a.chance 35 100
        if probeInUse then
          let (useMainRef, r5m) := if wtBr?.isSome then r5i.chance 40 100 else (true, r5i)
          let inUseBr := if useMainRef then "main" else wtBr?.getD "main"
          (.opWorktreeAdd wtRepo inUseDst (some (.raw inUseBr)) none false false poison, ctx, r5m)
        else if slotFresh then
          let (wtMode, r5b) := r5i.nextNat 5
          let wsSlot := if wtTgt == .slot .wt1 then SlotId.wt1 else SlotId.wt2
          let defaultBr := wsSlot.relPath
          if wtMode == 0 && !ctx.knownBranches.contains defaultBr then
            let ctxDef :=
              if wtTgt == .slot .wt1 then
                { ctx with
                  hasWt1 := true
                  wt1Branch? := some defaultBr
                  wt1Locked := false
                  knownBranches := ctx.knownBranches.push defaultBr
                  pendingSwInUse? := some defaultBr
                  pendingDirtyWtWrite? := some wsSlot }
              else
                { ctx with
                  hasWt2 := true
                  wt2Branch? := some defaultBr
                  wt2Locked := false
                  knownBranches := ctx.knownBranches.push defaultBr
                  pendingSwInUse? := some defaultBr
                  pendingDirtyWtWrite? := some wsSlot }
            (.opWorktreeAdd wtRepo wtTgt none none false false poison, ctxDef, r5b)
          else if wtMode <= 2 then
            let brName := s!"wt_sh_{ctx.wtBrSeq}"
            let ctxWt :=
              if wtTgt == .slot .wt1 then
                { ctx with
                  hasWt1 := true
                  wt1Branch? := some brName
                  wt1Locked := false
                  wtBrSeq := ctx.wtBrSeq + 1
                  pendingSwInUse? := some brName
                  pendingDirtyWtWrite? := some wsSlot }
              else
                { ctx with
                  hasWt2 := true
                  wt2Branch? := some brName
                  wt2Locked := false
                  wtBrSeq := ctx.wtBrSeq + 1
                  pendingSwInUse? := some brName
                  pendingDirtyWtWrite? := some wsSlot }
            (.opWorktreeAdd wtRepo wtTgt (some (.raw "HEAD")) (some { raw := brName }) false false poison, ctxWt, r5b)
          else
            let ctxDet :=
              if wtTgt == .slot .wt1 then
                { ctx with hasWt1 := true, wt1Branch? := none, wt1Locked := false, pendingDirtyWtWrite? := some wsSlot }
              else
                { ctx with hasWt2 := true, wt2Branch? := none, wt2Locked := false, pendingDirtyWtWrite? := some wsSlot }
            (.opWorktreeAdd wtRepo wtTgt (some (.raw "HEAD")) none true false poison, ctxDet, r5b)
        else
          (.opWorktreeAdd wtRepo wtTgt (some (.raw "HEAD")) none true false poison, ctx, r5i)
      else
        let (hasRev, r5) := r5a.nextBool
        let (rev?, r6) :=
          if hasRev then
            let (rv, r7) := genRevSpec r5 ctx
            (some rv, r7)
          else (none, r5)
        let (hasNb, r7) := r6.nextBool
        let (nb?, r8) :=
          if hasNb then
            let (nb, r9) := genBranchRef r7 ctx
            (some nb, r9)
          else (none, r7)
        let (detach, r9) := r8.nextBool
        let (force, r10) := r9.nextBool
        (.opWorktreeAdd wtRepo wtTgt rev? nb? detach force poison, ctx, r10)
  | 34 =>
    let hasWt := ctx.hasWt1 || ctx.hasWt2
    let (useBareWt, r4z) := if ctx.hasBareWt then r3.chance 30 100 else (false, r3)
    if useBareWt then
      let (force, r4) := r4z.chance 50 100
      (.opWorktreeRemove (.slot .bareRepo) (.slot .bareWt) force poison, { ctx with hasBareWt := false }, r4)
    else
      let (useRepoA, r4a) := r4z.chance 85 100
      let wtRepo := if hasWt && useRepoA then .slot .repoA else target
      let (wtTgt, r4) :=
        if ctx.hasDirtyWt1 && !ctx.wt1Locked && useRepoA then
          (.slot .wt1, r4a)
        else if hasWt && useRepoA then
          if ctx.hasWt1 && ctx.hasWt2 then
            r4a.choose #[PathTarget.slot .wt1, PathTarget.slot .wt2] (.slot .wt1)
          else if ctx.hasWt1 then
            (.slot .wt1, r4a)
          else
            (.slot .wt2, r4a)
        else
          r4a.chooseWeighted
            #[(4, PathTarget.slot .wt1), (4, PathTarget.slot .wt2), (2, PathTarget.slot .repoA),
              (2, PathTarget.slot .missingDir), (1, PathTarget.subRel .wt1 "../wt1"), (1, PathTarget.raw "")] (.slot .wt1)
      let isDirtyTarget :=
        (wtTgt == .slot .wt1 && (ctx.hasDirtyWt1 || ctx.dirtyWtSlot? == some .wt1)) ||
        (wtTgt == .slot .wt2 && ctx.dirtyWtSlot? == some .wt2)
      let isLockedTarget :=
        (wtTgt == .slot .wt1 && ctx.wt1Locked) || (wtTgt == .slot .wt2 && ctx.wt2Locked)
      let (force, r5) :=
        if isDirtyTarget && !isLockedTarget then r4.chance 20 100
        else if hasWt then r4.chance 35 100
        else r4.nextBool
      let ctx' :=
        if wtRepo == .slot .repoA && !isLockedTarget && (force || !isDirtyTarget) then
          clearWtSlotState ctx wtTgt
        else if wtRepo == .slot .repoA && wtTgt == .slot .wt1 && !force && ctx.hasDirtyWt1 then
          { ctx with hasDirtyWt1 := false, dirtyWtSlot? := none }
        else ctx
      (.opWorktreeRemove wtRepo wtTgt force poison, ctx', r5)
  | 36 =>
    let (probeOp, r4) := r3.nextNat 4
    let (pTgt, r5) := r4.chooseWeighted #[
      (4, PathTarget.slot .repoA),
      (2, PathTarget.slot .bareRepo),
      (1, PathTarget.slot .wt1),
      (1, PathTarget.slot .cloneRepo),
      (1, PathTarget.slot .missingDir)
    ] (.slot .repoA)
    (.opTimeoutProbe pTgt probeOp, ctx, r5)
  | _ =>
    let (cleanWwt, r4z) := r3.chance 45 100
    if cleanWwt then
      let (wtTgt, r4) :=
        if ctx.hasWt1 && !ctx.hasWt2 then (.slot .wt2, r4z)
        else if ctx.hasWt2 && !ctx.hasWt1 then (.slot .wt1, r4z)
        else r4z.choose #[.slot .wt2, .slot .wt1] (.slot .wt2)
      let (nInner, r5) := r4.nextRange 1 2
      let (ins, r6) := Id.run do
        let mut cur := r5
        let mut acc : List GitFuzzStep := []
        for _ in List.range nInner do
          let (st, nxt) := genInnerStep cur ctx (.slot .repoA) wtTgt
          cur := nxt
          acc := acc ++ [st]
        return (acc, cur)
      let ctx' := if ctx.hasRepoA && ctx.commitHint > 0 then clearWtSlotState ctx wtTgt else ctx
      (.opWithWorktree (.slot .repoA) wtTgt (some (.raw "HEAD")) none true true ins false poison, ctx', r6)
    else
      let (useRepoA, r4a) := r4z.chance 65 100
      let repoTgt := if useRepoA then .slot .repoA else target
      let (wtTgt, r4) :=
        if ctx.hasWt1 && !ctx.hasWt2 then (.slot .wt2, r4a)
        else if ctx.hasWt2 && !ctx.hasWt1 then (.slot .wt1, r4a)
        else r4a.choose #[.slot .wt2, .slot .wt1] (.slot .wt2)
      let (hasRev, r4b) := r4.chance 80 100
      let (wtRev?, r4c) :=
        if hasRev then
          let (rv, rR) := genRevSpec r4b ctx
          (some rv, rR)
        else (none, r4b)
      let (hasNb, r4d) := r4c.chance 35 100
      let (nb?, r4e) :=
        if hasNb then
          let (nb, rN) := genBranchRef r4d ctx
          (some nb, rN)
        else (none, r4d)
      let (detach, r5) := if nb?.isSome then (false, r4e) else r4e.chance 75 100
      let (force, r6) := r5.nextBool
      let (nInner, r7) := r6.nextRange 1 3
      let (ins, r8) := Id.run do
        let mut cur := r7
        let mut acc : List GitFuzzStep := []
        for _ in List.range nInner do
          let (st, nxt) := genInnerStep cur ctx repoTgt wtTgt
          cur := nxt
          acc := acc ++ [st]
        return (acc, cur)
      let (retErr, r9) := r8.nextBool
      let ctx' := if repoTgt == .slot .repoA && force then clearWtSlotState ctx wtTgt else ctx
      (.opWithWorktree repoTgt wtTgt wtRev? nb? detach force ins retErr poison, ctx', r9)

end Fuzz.Git
