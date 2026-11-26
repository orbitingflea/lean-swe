import Core.NondetTest
import LeanSwe.Process.Types
import LeanSwe.Process.Types.Internal
import LeanSwe.Process.Model
import LeanSwe.Process.SpecTests
import LeanSwe.Process.SpecMutants.RefSysBridge

/-! Additional compile-time negative specification mutants for `LeanSwe.Process`. -/

namespace LeanSwe.Process

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Process.SpecMutants

private instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error e1, .error e2 =>
    match decEq e1 e2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun hEq => by injection hEq with h'; exact h h')
  | .ok a1, .ok a2 =>
    match decEq a1 a2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun hEq => by injection hEq with h'; exact h h')
  | .error _, .ok _ => isFalse (fun hEq => by cases hEq)
  | .ok _, .error _ => isFalse (fun hEq => by cases hEq)

example : ¬ Core.AllPass (test_process_sysBridge_resolveExecutablePath_relativeCwdAndPathRules
    (fun files prog _ envPairs fuel =>
      refResolveExecutablePath files prog none envPairs fuel)) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

example : ¬ Core.AllPass (test_process_sysBridge_validateWorkingDir_chdirSemantics
    refProbePathBytes
    (fun _ _ _ => pure (.ok ()))) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

example : ¬ Core.AllPass (test_process_sysBridge_validateWorkingDir_chdirSemantics
    (fun cwd? dir prog =>
      (match cwd? with | some d => d ++ "/" ++ dir ++ "/" ++ prog | none => dir ++ "/" ++ prog).toUTF8)
    (@refValidateWorkingDir (StateM PathProbeState) _ Nat)) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

example : ¬ Core.AllPass (test_process_sysBridge_streamPipes_shortReadWriteEagainEintrReassembly
    (fun _ _ _ _ _ _ _ _ _ _ =>
      pure (.ok (.eof "abc".toUTF8 ByteArray.empty)))) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

example : ¬ Core.AllPass (test_process_sysBridge_streamPipes_drainsStdinAfterOutErrEof
    (fun files _ timeRand stdin startMs timeoutMs? _ stepFuel st _ => do
      let (inFdNext?, _, _, _, _) ←
        refStepStdinOpt files timeRand st.inFd? stdin startMs timeoutMs? st.stdinPos stepFuel
      refCloseOpt files inFdNext?
      refCloseOpt files st.outFd?
      refCloseOpt files st.errFd?
      return .ok (.eof ByteArray.empty ByteArray.empty))) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

example : ¬ Core.AllPass (test_process_sysBridge_maxOutputBytes_truncatesKillsAndReaps
    (@refStateProcTableOps CapSimState Nat)
    (fun deps tbl eintrFuel ioFuel =>
      { refMkRawOpsM deps tbl eintrFuel ioFuel with
        killProcessGroup := fun _ => pure (.ok ()) })) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

example : ¬ Core.AllPass (test_process_sysBridge_maxOutputBytes_truncatesKillsAndReaps
    (fun getTbl setTbl =>
      { refStateProcTableOps getTbl setTbl with activeCount := pure 1 })
    (@refMkRawOpsM (StateM CapSimState) _ Nat)) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

example : ¬ Core.AllPass (test_process_sysBridge_partialPipe2Failure_cleansUpAllocatedFds
    (@refStateProcTableOps PipeFailSimState Nat)
    (fun deps _ _ req => do
      match ← deps.proc.pipe2 { cloexec := true } with
      | .error e => return .error (refMapErrno (some req.program) "pipe2" e)
      | .ok (inR, inW) =>
        match ← deps.proc.pipe2 { cloexec := true } with
        | .error e =>
          refCloseOpt deps.files (some inR)
          refCloseOpt deps.files (some inW)
          return .error (refMapErrno (some req.program) "pipe2" e)
        | .ok _ =>
          match ← deps.proc.pipe2 { cloexec := true } with
          | .error e =>
            refCloseOpt deps.files (some inR)
            refCloseOpt deps.files (some inW)
            return .error (refMapErrno (some req.program) "pipe2" e)
          | .ok _ =>
            return .ok { handleId := 0, pid := 1, pgid := 1 })) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

/-- Mutant `mkApiM` corrupting `.signaled` signal number and swapping `stdout`/`stderr` is rejected by `test_process_mkApiM_preservesExactAwaitOutcomes`. -/
theorem mutant_mkApiM_corruptedSignaledAndSwappedStreams_rejected :
    ¬ Core.AllPass (test_process_mkApiM_preservesExactAwaitOutcomes
      (fun raw =>
        let base := refMkApiM raw
        { base with
          run := fun req => do
            match ← base.run req with
            | .ok res => return .ok { res with stdout := res.stderr, stderr := res.stdout }
            | .error e => return .error { e with signal := e.signal.map (· + 1) } })) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

/-- Mutant `resolveExecutablePath` accepting `+x` FIFO inodes instead of continuing `PATH` search is rejected by `test_process_sysBridge_resolveExecutablePath_relativeCwdAndPathRules`. -/
theorem mutant_resolveExecutablePath_acceptsFifo_rejected :
    ¬ Core.AllPass (test_process_sysBridge_resolveExecutablePath_relativeCwdAndPathRules
      (fun files prog cwd? _ _ => do
        if prog.toList.contains '/' then
          return .ok prog
        let p := refProbePathBytes cwd? "fifobin" prog
        match ← files.fstatat none p {} with
        | .ok _ => return .ok ("fifobin/" ++ prog)
        | .error e => return .error (refMapErrno (some prog) "execvp" e))) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

/-- Mutant `mkRawOpsM` sending `SIGKILL` to `0` on `pgid = 1` or skipping pre-`PATH` `cwd` validation is rejected by `test_process_sysBridge_spawnCwdIsolationKillPgid1AndChdirError`. -/
theorem mutant_mkRawOpsM_pgid1KillZero_rejected :
    ¬ Core.AllPass (test_process_sysBridge_spawnCwdIsolationKillPgid1AndChdirError
      (@refStateProcTableOps SpawnAuditState Nat)
      (fun deps tbl eintrFuel ioFuel =>
        { refMkRawOpsM deps tbl eintrFuel ioFuel with
          killProcessGroup := fun _ => do
            let _ ← deps.proc.kill 0 .sigterm
            let _ ← deps.proc.kill 0 .sigkill
            return .ok () })) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

/-- Mutant `mkApiM` bypassing `validateSpawnRequest` in `spawn` is rejected by `test_process_spawn_invalidRequest_doesNotCallRaw`. -/
theorem mutant_mkApiM_spawnBypassesValidate_rejected :
    ¬ Core.AllPass (test_process_spawn_invalidRequest_doesNotCallRaw
      (fun raw => { refMkApiM raw with spawn := fun req => raw.spawn { toSpawnRequest := req } })) := by
  intro h
  have h0 := h 0 { program := "" }
  simp [refMkApiM, Model.validateRequestModel, Model.validateSpawnRequestModel, StateT.run,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, assert] at h0

/-- Mutant `mkApiM` forwarding unnormalized `SpawnRequest` to `raw.spawn` is rejected by `test_process_spawn_usesNormalizedRequest`. -/
theorem mutant_mkApiM_spawnSkipsNormalize_rejected :
    ¬ Core.AllPass (test_process_spawn_usesNormalizedRequest
      (fun raw =>
        { refMkApiM raw with
          spawn := fun req =>
            match Model.validateSpawnRequestModel req with
            | .error e => pure (.error e)
            | .ok _ => raw.spawn { toSpawnRequest := req } })) := by
  intro h
  let req : SpawnRequest := { program := "echo", env := #[("A", some "1"), ("A", some "2")] }
  have h0 := h req
  have hValS : Model.validateSpawnRequestModel req = .ok { program := "echo", env := #[("A", some "2")] } := by
    decide +kernel
  have hVal : Model.validateRequestModel { toSpawnRequest := req } =
      .ok { program := "echo", env := #[("A", some "2")] } := by
    decide +kernel
  dsimp only [Core.AllPass, test_process_spawn_usesNormalizedRequest, nondet, bind] at h0
  rw [show (refMkApiM _).validateRequest { toSpawnRequest := req } =
      .ok { program := "echo", env := #[("A", some "2")] } from hVal] at h0
  dsimp only [assert] at h0
  have hBad := h0.1.1
  have hSz := congrArg (fun o => match o with | some r => r.env.size | none => 0) hBad
  simp [req, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, hValS] at hSz

/-- Mutant `mkApiM` lifting `SpawnRequest` with non-default `timeoutMs` is rejected by `test_process_spawn_usesNormalizedRequest`. -/
theorem mutant_mkApiM_spawnSetsSpuriousTimeout_rejected :
    ¬ Core.AllPass (test_process_spawn_usesNormalizedRequest
      (fun raw =>
        { refMkApiM raw with
          spawn := fun req =>
            match Model.validateSpawnRequestModel req with
            | .error e => pure (.error e)
            | .ok norm => raw.spawn { toSpawnRequest := norm, timeoutMs := some 1 } })) := by
  intro h
  let req : SpawnRequest := { program := "echo" }
  have h0 := h req
  have hValS : Model.validateSpawnRequestModel req = .ok req := by decide +kernel
  have hVal : Model.validateRequestModel { toSpawnRequest := req } = .ok { toSpawnRequest := req } := by decide +kernel
  dsimp only [Core.AllPass, test_process_spawn_usesNormalizedRequest, nondet, bind] at h0
  rw [show (refMkApiM _).validateRequest { toSpawnRequest := req } =
      .ok { toSpawnRequest := req } from hVal] at h0
  dsimp only [assert] at h0
  have hBad := h0.1.1
  have hTo := congrArg (fun o => match o with | some r => r.timeoutMs | none => none) hBad
  simp [req, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, hValS] at hTo

/-- Mutant `mkApiM` forwarding `timeoutMs = some 0` to `raw.awaitOutput` is rejected by `test_process_awaitOutput_rejectsZeroTimeout`. -/
theorem mutant_mkApiM_awaitOutputAllowsZeroTimeout_rejected :
    ¬ Core.AllPass (test_process_awaitOutput_rejectsZeroTimeout
      (fun raw => { refMkApiM raw with awaitOutput := raw.awaitOutput })) := by
  intro h
  have h0 := h 0 { handleId := 1, pid := 1, pgid := 1 } ByteArray.empty none
  simp [StateT.run, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, assert] at h0

/-- Mutant `mkApiM` dropping empty-message normalization on `killProcessGroup` is rejected by `test_process_lifecycle_delegatesAndNormalizesErrors`. -/
theorem mutant_mkApiM_lifecycleDropsMsgNormalization_rejected :
    ¬ Core.AllPass (test_process_lifecycle_delegatesAndNormalizesErrors
      (fun raw => { refMkApiM raw with killProcessGroup := raw.killProcessGroup })) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

end LeanSwe.Process
