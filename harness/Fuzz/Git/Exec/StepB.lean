import Fuzz.Git.Exec.Core
import Fuzz.Git.Exec.Vfs
import Fuzz.Git.Exec.Fixtures
import Fuzz.Git.Exec.Witness

namespace Fuzz.Git

open Fuzz.Common
open LeanSwe.Git
open LeanSwe.Git.Model

/-- Execute branch, checkout, switch, reset, fetch, worktree, and timeout-probe fuzz steps. -/
def execStepPartB
    (runInner : EpisodeState → CoverageTracker → GitFuzzStep → IO (Except TraceError (EpisodeState × CoverageTracker)))
    (st : EpisodeState) (tr : CoverageTracker) (step : GitFuzzStep) :
    IO (Except TraceError (EpisodeState × CoverageTracker)) := do
  match step with
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
          match ← runInner curSt curTr inner with
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

  | _ => return .error (.infra "unhandled in execStepPartB")

end Fuzz.Git
