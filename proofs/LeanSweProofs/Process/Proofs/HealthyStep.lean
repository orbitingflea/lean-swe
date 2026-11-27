import Core.NondetTest
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Process.Types
import LeanSweProofs.LinuxSyscall.Process.Model
import LeanSwe.LinuxSyscall.Files.Types
import LeanSweProofs.LinuxSyscall.Files.Model
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSweProofs.LinuxSyscall.TimeRand.Model
import LeanSwe.PostFork.Types
import LeanSweProofs.PostFork.Model
import LeanSwe.Process.Types
import LeanSwe.LinuxSyscall.Process.Interface
import LeanSwe.Process.SysBridge
import LeanSweProofs.Process.Proofs.HealthyStepAssoc

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process
open LeanSwe.Process.SysBridge

/-- Scoped refinement predicate for the `ProcessOpsM` subset (`pipe2`, `waitpid`, `kill`) consumed by `Process.SysBridge`, stated directly against canonical `LinuxSyscall.Process.healthyStep`. -/
structure RefinesHealthyProcOpsAt {S fd : Type}
    (proj : S → LinuxSyscall.Process.HealthyEnv)
    (toHid : fd → LinuxSyscall.Process.HandleId)
    (ops : LinuxSyscall.Process.ProcessOpsM (StateM S) fd) : Prop where
  /-- `pipe2` transitions via canonical `LinuxSyscall.Process.healthyStep`. -/
  pipe2_healthy : ∀ s flags, (proj s).wf = true →
    let r := (ops.pipe2 flags).run s
    LinuxSyscall.Process.healthyStep (proj s) (.pipe2 flags)
      (LinuxSyscall.Process.outcomeOfPiped (r.1.map fun p => (toHid p.1, toHid p.2))) = some (proj r.2)
  /-- `waitpid` transitions via canonical `LinuxSyscall.Process.healthyStep`. -/
  waitpid_healthy : ∀ s pid flags, (proj s).wf = true →
    let r := (ops.waitpid pid flags).run s
    LinuxSyscall.Process.healthyStep (proj s) (.waitpid pid flags)
      (LinuxSyscall.Process.outcomeOfWaited r.1) = some (proj r.2)
  /-- `kill` transitions via canonical `LinuxSyscall.Process.healthyStep`. -/
  kill_healthy : ∀ s target sig, (proj s).wf = true →
    let r := (ops.kill target sig).run s
    LinuxSyscall.Process.healthyStep (proj s) (.kill target sig)
      (LinuxSyscall.Process.outcomeOfUnit r.1) = some (proj r.2)

/-- Scoped refinement predicate for the `FilesOpsM` subset (`close`, `read`, `write`, `fstatat`, `faccessat`, `fcntl`) consumed by `Process.SysBridge`, stated directly against canonical `LinuxSyscall.Files.healthyStep`. -/
structure RefinesHealthyFilesOpsAt {S fd : Type}
    (proj : S → LinuxSyscall.Files.HealthyEnv)
    (toHid : fd → LinuxSyscall.Files.HandleId)
    (ops : LinuxSyscall.Files.FilesOpsM (StateM S) fd) : Prop where
  /-- `close` transitions via canonical `LinuxSyscall.Files.healthyStep` (excluding `EBUSY` and erasing `toHid h` from `fds`). -/
  close_healthy : ∀ s h, (proj s).wf = true →
    let r := (ops.close h).run s
    LinuxSyscall.Files.healthyStep (proj s) (.close (toHid h))
      (LinuxSyscall.Files.outcomeOfUnit r.1) = some (proj r.2)
  /-- `read` transitions via canonical `LinuxSyscall.Files.healthyStep` (permitting short pipe reads `0 ≤ chunk.size ≤ cap`, `EAGAIN`, and bounded `EINTR`). -/
  read_healthy : ∀ s h cap, (proj s).wf = true →
    let r := (ops.read h cap).run s
    LinuxSyscall.Files.healthyStep (proj s) (.read (toHid h) cap)
      (LinuxSyscall.Files.outcomeOfBytes r.1) = some (proj r.2) ∧
    (∀ bs, r.1 = .ok bs → bs.size ≤ cap.toNat)
  /-- `write` transitions via canonical `LinuxSyscall.Files.healthyStep` (permitting short pipe writes `0 ≤ n ≤ data.size`, `EAGAIN`, `EPIPE`, and bounded `EINTR`). -/
  write_healthy : ∀ s h data, (proj s).wf = true →
    let r := (ops.write h data).run s
    LinuxSyscall.Files.healthyStep (proj s) (.write (toHid h) data)
      (LinuxSyscall.Files.outcomeOfU32 r.1) = some (proj r.2) ∧
    (∀ n, r.1 = .ok n → n.toNat ≤ data.size)
  /-- `fstatat` transitions via canonical `LinuxSyscall.Files.healthyStep`. -/
  fstatat_healthy : ∀ s dir path flags, (proj s).wf = true →
    let r := (ops.fstatat dir path flags).run s
    LinuxSyscall.Files.healthyStep (proj s) (.fstatat (dir.map toHid) path flags)
      (LinuxSyscall.Files.outcomeOfStatted r.1) = some (proj r.2)
  /-- `faccessat` transitions via canonical `LinuxSyscall.Files.healthyStep`. -/
  faccessat_healthy : ∀ s dir path mask flags, (proj s).wf = true →
    let r := (ops.faccessat dir path mask flags).run s
    LinuxSyscall.Files.healthyStep (proj s) (.faccessat (dir.map toHid) path mask flags)
      (LinuxSyscall.Files.outcomeOfUnit r.1) = some (proj r.2)
  /-- `fcntl` transitions via canonical `LinuxSyscall.Files.healthyStep`. -/
  fcntl_healthy : ∀ s h cmd, (proj s).wf = true →
    let r := (ops.fcntl h cmd).run s
    LinuxSyscall.Files.healthyStep (proj s) (.fcntl (toHid h) cmd)
      (LinuxSyscall.Files.outcomeOfU32 r.1) = some (proj r.2)

/-- Universal refinement predicate for `PostFork.PostForkOpsM (StateM S) fd` under a healthy kernel. -/
structure RefinesHealthyPostFork {S fd : Type}
    (ops : PostFork.PostForkOpsM (StateM S) fd) : Prop where
  /-- On valid `ChildSpecM` with `.newGroup`, `spawn` either yields a positive Linux PID/PGID or fails without critical OS faults. -/
  spawn_healthy : ∀ s spec,
    let r := (ops.spawn spec).run s
    (∀ child, r.1 = .ok child →
      1 ≤ child.pid ∧ child.pid ≤ LinuxSyscall.Process.MAX_LINUX_PID ∧
      (spec.processGroup = .newGroup → child.pgid = some child.pid)) ∧
    (∀ err, r.1 = .error err →
      (∀ e, err.errno = some e → Errno.isCriticalOsErrno e = false) ∧
      (∀ cf, err.childFailure = some cf → Errno.isCriticalOsErrno cf.errno = false))

/-- Combined healthy-kernel refinement, descriptor-freshness, `close`-erasure, and table-lens contract for `SysBridge.SysDepsM (StateM S) fd`. -/
structure RefinesHealthySysDeps {S fd : Type} [DecidableEq fd]
    (getTbl : S → ProcTableState fd)
    (setTbl : S → ProcTableState fd → S)
    (openFds : S → List fd)
    (deps : SysDepsM (StateM S) fd) : Prop where
  /-- Lens law `getTbl (setTbl s t) = t`. -/
  get_set : ∀ s t, getTbl (setTbl s t) = t
  /-- Lens law `openFds (setTbl s t) = openFds s`. -/
  openFds_set : ∀ s t, openFds (setTbl s t) = openFds s
  /-- `proc.pipe2` preserves `getTbl`, leaves `openFds` unchanged on `.error`, and on `.ok (rf, wf)` allocates fresh `rf ≠ wf` (`rf ∉ openFds s`, `wf ∉ openFds s`) with `openFds r.2 = wf :: rf :: openFds s`. -/
  pipe2_frame : ∀ s flags,
    let r := (deps.proc.pipe2 flags).run s
    getTbl r.2 = getTbl s ∧
    (∀ e, r.1 = .error e → openFds r.2 = openFds s ∧ Errno.isCriticalOsErrno e = false) ∧
    (∀ rf wf, r.1 = .ok (rf, wf) →
      rf ≠ wf ∧ rf ∉ openFds s ∧ wf ∉ openFds s ∧ openFds r.2 = wf :: rf :: openFds s)
  /-- `proc.waitpid` preserves `getTbl` and `openFds` and never fails with `Errno.isCriticalOsErrno`. -/
  waitpid_frame : ∀ s pid flags,
    let r := (deps.proc.waitpid pid flags).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ e, r.1 = .error e → Errno.isCriticalOsErrno e = false)
  /-- `proc.kill` preserves `getTbl` and `openFds` and never fails with `Errno.isCriticalOsErrno`. -/
  kill_frame : ∀ s target sig,
    let r := (deps.proc.kill target sig).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ e, r.1 = .error e → Errno.isCriticalOsErrno e = false)
  /-- `files.close` preserves `getTbl`, erases `h` from `openFds` (`openFds r.2 = (openFds s).erase h`), and never fails with `Errno.isCriticalOsErrno`. -/
  close_frame : ∀ s h,
    let r := (deps.files.close h).run s
    getTbl r.2 = getTbl s ∧
    openFds r.2 = (openFds s).erase h ∧
    (∀ e, r.1 = .error e → Errno.isCriticalOsErrno e = false)
  /-- `files.read` preserves `getTbl` and `openFds`, obeys `bs.size ≤ cap.toNat`, and never fails with `Errno.isCriticalOsErrno`. -/
  read_frame : ∀ s h cap,
    let r := (deps.files.read h cap).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ bs, r.1 = .ok bs → bs.size ≤ cap.toNat) ∧
    (∀ e, r.1 = .error e → Errno.isCriticalOsErrno e = false)
  /-- `files.write` preserves `getTbl` and `openFds`, obeys `n.toNat ≤ data.size`, and never fails with `Errno.isCriticalOsErrno`. -/
  write_frame : ∀ s h data,
    let r := (deps.files.write h data).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ n, r.1 = .ok n → n.toNat ≤ data.size) ∧
    (∀ e, r.1 = .error e → Errno.isCriticalOsErrno e = false)
  /-- `files.fstatat` preserves `getTbl` and `openFds` and never fails with `Errno.isCriticalOsErrno`. -/
  fstatat_frame : ∀ s dir path flags,
    let r := (deps.files.fstatat dir path flags).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ e, r.1 = .error e → Errno.isCriticalOsErrno e = false)
  /-- `files.faccessat` preserves `getTbl` and `openFds` and never fails with `Errno.isCriticalOsErrno`. -/
  faccessat_frame : ∀ s dir path mask flags,
    let r := (deps.files.faccessat dir path mask flags).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ e, r.1 = .error e → Errno.isCriticalOsErrno e = false)
  /-- `files.fcntl` preserves `getTbl` and `openFds` and never fails with `Errno.isCriticalOsErrno`. -/
  fcntl_frame : ∀ s h cmd,
    let r := (deps.files.fcntl h cmd).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ e, r.1 = .error e → Errno.isCriticalOsErrno e = false)
  /-- `poll.ppoll` preserves `getTbl` and `openFds` and never fails with `Errno.isCriticalOsErrno`. -/
  ppoll_frame : ∀ s entries timeout,
    let r := (deps.poll.ppoll entries timeout).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ e, r.1 = .error e → Errno.isCriticalOsErrno e = false)
  /-- `timeRand.clock_gettime` preserves `getTbl` and `openFds` and never fails with `Errno.isCriticalOsErrno`. -/
  clock_gettime_frame : ∀ s clk,
    let r := (deps.timeRand.clock_gettime clk).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ e, r.1 = .error e → Errno.isCriticalOsErrno e = false)
  /-- `timeRand.clock_nanosleep` preserves `getTbl` and `openFds`. -/
  clock_nanosleep_frame : ∀ s clk abs req,
    let r := (deps.timeRand.clock_nanosleep clk abs req).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s
  /-- `postFork.spawn` satisfies `RefinesHealthyPostFork`. -/
  postFork_healthy : RefinesHealthyPostFork deps.postFork
  /-- `postFork.spawn` preserves `getTbl` and `openFds`. -/
  postFork_frame : ∀ s spec,
    let r := (deps.postFork.spawn spec).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s
  /-- `listAmbientEnv` preserves `getTbl` and `openFds`, and any error has a non-outcome error kind. -/
  listAmbientEnv_frame : ∀ s,
    let r := deps.listAmbientEnv.run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ e, r.1 = .error e →
      e.kind ≠ .timedOut ∧ e.kind ≠ .outputLimitExceeded ∧ e.kind ≠ .terminatedBySignal)

/-- Composition theorem deriving `RefinesHealthySysDeps` (including `close_frame`'s `openFds r.2 = (openFds s).erase h` directly from canonical `LinuxSyscall.Files.healthyStep` without `.close`/`EBUSY`) over shared `HandleId` (`Nat`). -/
theorem refinesHealthySysDeps_of_components {S : Type}
    (getTbl : S → ProcTableState LinuxSyscall.Files.HandleId)
    (setTbl : S → ProcTableState LinuxSyscall.Files.HandleId → S)
    (projProc : S → LinuxSyscall.Process.HealthyEnv)
    (projFiles : S → LinuxSyscall.Files.HealthyEnv)
    (projTime : S → LinuxSyscall.TimeRand.HealthyEnv)
    (deps : SysDepsM (StateM S) LinuxSyscall.Files.HandleId)
    (hWf : ∀ s : S,
      (projProc s).wf = true ∧
      (projFiles s).wf = true ∧
      (projTime s).wf = true)
    (hProc : RefinesHealthyProcOpsAt projProc id deps.proc)
    (hFiles : RefinesHealthyFilesOpsAt projFiles id deps.files)
    (hTime : LinuxSyscall.TimeRand.RefinesHealthyTimeRandAt projTime deps.timeRand)
    (hPostFork : RefinesHealthyPostFork deps.postFork)
    (hGetSet : ∀ s t, getTbl (setTbl s t) = t)
    (hOpenSet : ∀ s t,
      (projFiles (setTbl s t)).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hPipeLens : ∀ s flags,
      let openFds := fun st : S => (projFiles st).state.fds.map Prod.fst
      let r := (deps.proc.pipe2 flags).run s
      getTbl r.2 = getTbl s ∧
      (∀ e, r.1 = .error e → openFds r.2 = openFds s) ∧
      (∀ rf wf, r.1 = .ok (rf, wf) →
        rf ≠ wf ∧ rf ∉ openFds s ∧ wf ∉ openFds s ∧ openFds r.2 = wf :: rf :: openFds s))
    (hWaitLens : ∀ s pid flags,
      let r := (deps.proc.waitpid pid flags).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hKillLens : ∀ s target sig,
      let r := (deps.proc.kill target sig).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hCloseTblLens : ∀ s h, getTbl ((deps.files.close h).run s).2 = getTbl s)
    (hReadLens : ∀ s h cap,
      let r := (deps.files.read h cap).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hWriteLens : ∀ s h data,
      let r := (deps.files.write h data).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hStatLens : ∀ s dir path flags,
      let r := (deps.files.fstatat dir path flags).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hAccLens : ∀ s dir path mask flags,
      let r := (deps.files.faccessat dir path mask flags).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hFcntlLens : ∀ s h cmd,
      let r := (deps.files.fcntl h cmd).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hPollLens : ∀ s entries timeout,
      let r := (deps.poll.ppoll entries timeout).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst ∧
      (∀ e, r.1 = .error e → Errno.isCriticalOsErrno e = false))
    (hCgLens : ∀ s clk,
      let r := (deps.timeRand.clock_gettime clk).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hNsLens : ∀ s clk abs req,
      let r := (deps.timeRand.clock_nanosleep clk abs req).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hPfLens : ∀ s spec,
      let r := (deps.postFork.spawn spec).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hEnvLens : ∀ s,
      let r := deps.listAmbientEnv.run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst ∧
      (∀ e, r.1 = .error e →
        e.kind ≠ .timedOut ∧ e.kind ≠ .outputLimitExceeded ∧ e.kind ≠ .terminatedBySignal)) :
    RefinesHealthySysDeps getTbl setTbl (fun s => (projFiles s).state.fds.map Prod.fst) deps where
  get_set := hGetSet
  openFds_set := hOpenSet
  pipe2_frame s flags := by
    obtain ⟨hT, hE, hO⟩ := hPipeLens s flags
    have hSt := hProc.pipe2_healthy s flags (hWf s).1
    refine ⟨hT, ?_, hO⟩
    intro e he
    refine ⟨hE e he, ?_⟩
    have hCrit := proc_healthyStep_noCrit hSt
    simpa [he, Except.map, LinuxSyscall.Process.outcomeOfPiped, LinuxSyscall.Process.isCriticalFault] using hCrit
  waitpid_frame s pid flags := by
    obtain ⟨hT, hO⟩ := hWaitLens s pid flags
    have hSt := hProc.waitpid_healthy s pid flags (hWf s).1
    refine ⟨hT, hO, ?_⟩
    intro e he
    have hCrit := proc_healthyStep_noCrit hSt
    simpa [he, LinuxSyscall.Process.outcomeOfWaited, LinuxSyscall.Process.isCriticalFault] using hCrit
  kill_frame s target sig := by
    obtain ⟨hT, hO⟩ := hKillLens s target sig
    have hSt := hProc.kill_healthy s target sig (hWf s).1
    refine ⟨hT, hO, ?_⟩
    intro e he
    have hCrit := proc_healthyStep_noCrit hSt
    simpa [he, LinuxSyscall.Process.outcomeOfUnit, LinuxSyscall.Process.isCriticalFault] using hCrit
  close_frame s h := by
    have hSt := hFiles.close_healthy s h (hWf s).2.1
    refine ⟨hCloseTblLens s h, healthyFilesStep_close_fds hSt, ?_⟩
    intro e he
    have hCrit := (files_healthyStep_props hSt).2.2.1
    simpa [he, LinuxSyscall.Files.outcomeOfUnit, LinuxSyscall.Files.isCriticalFault] using hCrit
  read_frame s h cap := by
    obtain ⟨hT, hO⟩ := hReadLens s h cap
    obtain ⟨hSt, hSz⟩ := hFiles.read_healthy s h cap (hWf s).2.1
    refine ⟨hT, hO, hSz, ?_⟩
    intro e he
    have hCrit := (files_healthyStep_props hSt).2.2.1
    simpa [he, LinuxSyscall.Files.outcomeOfBytes, LinuxSyscall.Files.isCriticalFault] using hCrit
  write_frame s h data := by
    obtain ⟨hT, hO⟩ := hWriteLens s h data
    obtain ⟨hSt, hSz⟩ := hFiles.write_healthy s h data (hWf s).2.1
    refine ⟨hT, hO, hSz, ?_⟩
    intro e he
    have hCrit := (files_healthyStep_props hSt).2.2.1
    simpa [he, LinuxSyscall.Files.outcomeOfU32, LinuxSyscall.Files.isCriticalFault] using hCrit
  fstatat_frame s dir path flags := by
    obtain ⟨hT, hO⟩ := hStatLens s dir path flags
    have hSt := hFiles.fstatat_healthy s dir path flags (hWf s).2.1
    refine ⟨hT, hO, ?_⟩
    intro e he
    have hCrit := (files_healthyStep_props hSt).2.2.1
    simpa [he, LinuxSyscall.Files.outcomeOfStatted, LinuxSyscall.Files.isCriticalFault] using hCrit
  faccessat_frame s dir path mask flags := by
    obtain ⟨hT, hO⟩ := hAccLens s dir path mask flags
    have hSt := hFiles.faccessat_healthy s dir path mask flags (hWf s).2.1
    refine ⟨hT, hO, ?_⟩
    intro e he
    have hCrit := (files_healthyStep_props hSt).2.2.1
    simpa [he, LinuxSyscall.Files.outcomeOfUnit, LinuxSyscall.Files.isCriticalFault] using hCrit
  fcntl_frame s h cmd := by
    obtain ⟨hT, hO⟩ := hFcntlLens s h cmd
    have hSt := hFiles.fcntl_healthy s h cmd (hWf s).2.1
    refine ⟨hT, hO, ?_⟩
    intro e he
    have hCrit := (files_healthyStep_props hSt).2.2.1
    simpa [he, LinuxSyscall.Files.outcomeOfU32, LinuxSyscall.Files.isCriticalFault] using hCrit
  ppoll_frame := hPollLens
  clock_gettime_frame s clk := by
    obtain ⟨hT, hO⟩ := hCgLens s clk
    refine ⟨hT, hO, fun e he => False.elim ?_⟩
    have hWfT := (hWf s).2.2
    have hSt := hTime s (.clock_gettime clk) hWfT
    dsimp only [LinuxSyscall.TimeRand.execTimeRandReq, Bind.bind, StateT.bind,
      Pure.pure, StateT.pure, StateT.run, Id.run] at hSt
    rcases hRun : (deps.timeRand.clock_gettime clk).run s with ⟨res, s'⟩
    have hRes : res = .error e := by simpa [hRun] using he
    subst hRes
    rw [show deps.timeRand.clock_gettime clk s = (.error e, s') from hRun] at hSt
    have hSec : (projTime s).state.ambientSeccomp = false := by
      unfold LinuxSyscall.TimeRand.HealthyEnv.wf at hWfT
      cases hb : (projTime s).state.ambientSeccomp <;> simp_all
    simp [LinuxSyscall.TimeRand.healthyStep, hWfT, LinuxSyscall.TimeRand.outcomeOfTimespec,
      LinuxSyscall.TimeRand.allowedStep, LinuxSyscall.TimeRand.allowedStepCore, hSec] at hSt
  clock_nanosleep_frame := hNsLens
  postFork_healthy := hPostFork
  postFork_frame := hPfLens
  listAmbientEnv_frame := hEnvLens

/-- Relational contract on `RawProcessOpsM (StateM S)` enforcing both `activeProcessCount` conservation and OS descriptor (`openFds`) conservation across all `spawn`, `awaitOutput`, `killProcessGroup`, and `reap` paths. -/
structure RawProcessLaws {S fd : Type}
    (openFds : S → List fd)
    (raw : RawProcessOpsM (StateM S)) : Prop where
  /-- `mapRawError` agrees with `SysBridge.mapRawError`. -/
  mapRawError_eq : raw.mapRawError = SysBridge.mapRawError
  /-- `spawn` on error preserves both `activeProcessCount` and `openFds`, returns non-empty message, and never reports post-spawn outcome kinds. -/
  spawn_err : ∀ s req err, (raw.spawn req).run s = (.error err, ((raw.spawn req).run s).2) →
    (raw.activeProcessCount.run ((raw.spawn req).run s).2).1 = (raw.activeProcessCount.run s).1 ∧
    openFds ((raw.spawn req).run s).2 = openFds s ∧
    err.message ≠ "" ∧
    err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal
  /-- `activeProcessCount` is a pure read (`s' = s`). -/
  activeCount_pure : ∀ s, (raw.activeProcessCount.run s).2 = s
  /-- Full `spawn → awaitOutput → [killProcessGroup] → reap` lifecycle preserves both `activeProcessCount` and `openFds`, and enforces timeout/cap/signal invariants. -/
  spawn_lifecycle : ∀ s₀ req h s₁,
    (raw.spawn req).run s₀ = (.ok h, s₁) →
    h.pid > 0 ∧ h.pgid > 0 ∧
    let aw := (raw.awaitOutput h req.stdin req.timeoutMs req.maxOutputBytes).run s₁
    (∀ err, aw.1 = .error err →
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal ∧
      let kl := (raw.killProcessGroup h).run aw.2
      let rp := (raw.reap h).run kl.2
      (raw.activeProcessCount.run rp.2).1 = (raw.activeProcessCount.run s₀).1 ∧
      openFds rp.2 = openFds s₀) ∧
    (∀ res, aw.1 = .ok (.exited res) →
      (∀ limit, req.maxOutputBytes = some limit → res.stdout.size + res.stderr.size ≤ limit) ∧
      let rp := (raw.reap h).run aw.2
      (raw.activeProcessCount.run rp.2).1 = (raw.activeProcessCount.run s₀).1 ∧
      openFds rp.2 = openFds s₀ ∧
      (∀ rerr, rp.1 = .error rerr →
        rerr.kind ≠ .timedOut ∧ rerr.kind ≠ .outputLimitExceeded ∧ rerr.kind ≠ .terminatedBySignal)) ∧
    (∀ sig out errB, aw.1 = .ok (.signaled sig out errB) →
      let kl := (raw.killProcessGroup h).run aw.2
      let rp := (raw.reap h).run kl.2
      (raw.activeProcessCount.run rp.2).1 = (raw.activeProcessCount.run s₀).1 ∧
      openFds rp.2 = openFds s₀) ∧
    (∀ out errB, aw.1 = .ok (.timedOut out errB) →
      req.timeoutMs.isSome = true ∧
      let kl := (raw.killProcessGroup h).run aw.2
      let rp := (raw.reap h).run kl.2
      (raw.activeProcessCount.run rp.2).1 = (raw.activeProcessCount.run s₀).1 ∧
      openFds rp.2 = openFds s₀) ∧
    (∀ out errB, aw.1 = .ok (.outputLimitExceeded out errB) →
      req.maxOutputBytes.isSome = true ∧
      (∀ limit, req.maxOutputBytes = some limit → out.size + errB.size ≤ limit) ∧
      let kl := (raw.killProcessGroup h).run aw.2
      let rp := (raw.reap h).run kl.2
      (raw.activeProcessCount.run rp.2).1 = (raw.activeProcessCount.run s₀).1 ∧
      openFds rp.2 = openFds s₀)

end LeanSwe.Process.Proofs
