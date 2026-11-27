import Core.Obeys
import Core.ConcOps
import LeanSweProofs.Process.Model.FullStep
import LeanSweProofs.Process.Model.HealthySim
import LeanSweProofs.Process.Proofs.RefinesModelHostWitness

/-!
Schedule-parameterized `Core.ObeysConcFrame`, `Core.ObeysStateCell`, and `Model.allowedFullRawStep`
non-vacuity witness (`process_obeys_model_nonvacuous`) for `LeanSwe.Process.Proofs.obeys_model`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process

private noncomputable def runSafeTask {BaseW α : Type}
    (inv : BaseW → Prop) (frame : BaseW → BaseW → Prop)
    (t : StateM (BaseW × Nat) α) (s : BaseW × Nat) : Except String α × (BaseW × Nat) :=
  letI := Classical.propDecidable
  let (a, s') := t.run s
  if inv s'.1 ∧ frame s.1 s'.1 then (.ok a, s') else (.error "task frame aborted", s)

/-- Schedule-driven `Core.ConcOpsM` witness over `StateM (BaseW × Nat)` preserving `inv` and `frame`. -/
noncomputable def schedFrameConcOps (BaseW : Type) (inv : BaseW → Prop)
    (frame : BaseW → BaseW → Prop) (sched : Nat → Bool) :
    Core.ConcOpsM (StateM (BaseW × Nat)) where
  Ref := fun α => α
  TaskHandle := fun α => StateM (BaseW × Nat) α
  mkRef := fun x s => (x, s)
  readRef := fun r s => (r, s)
  writeRef := fun _ _ s => ((), s)
  modifyGetRef := fun r f s => ((f r).1, s)
  spawnTask := fun act (b, step) =>
    letI := Classical.propDecidable
    if sched step then
      let (a, s') := act.run (b, step + 1)
      if inv s'.1 ∧ frame b s'.1 then (pure a, s') else (act, (b, step + 1))
    else
      (act, (b, step + 1))
  hasFinished := fun _ (b, step) => (sched step, (b, step + 1))
  pollTask := fun t (b, step) =>
    if sched step then
      let (res, s') := runSafeTask inv frame t (b, step + 1)
      (some res, s')
    else
      (none, (b, step + 1))
  waitTask := fun t s => runSafeTask inv frame t s
  tryCatchMsg := fun act s =>
    let (a, s') := act.run s
    (.ok a, s')

/-- `schedFrameConcOps` satisfies `Core.ObeysConcFrame` for any reflexive `frame` and schedule `sched`. -/
theorem schedFrameConcOps_obeysConcFrame {BaseW : Type} (inv : BaseW → Prop)
    (frame : BaseW → BaseW → Prop) (hrefl : ∀ b, frame b b) (sched : Nat → Bool) :
    Core.ObeysConcFrame (fun s : BaseW × Nat => inv s.1)
      (fun s₁ s₂ : BaseW × Nat => frame s₁.1 s₂.1)
      (schedFrameConcOps BaseW inv frame sched) := by
  refine ⟨fun {α} (t : StateM (BaseW × Nat) α) (P : α → Prop) =>
      ∀ s, inv s.1 → let (a, s') := t.run s; inv s'.1 ∧ frame s.1 s'.1 ∧ P a,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ s h; exact ⟨h, hrefl s.1⟩
  · intro _ _ s h; exact ⟨h, hrefl s.1⟩
  · intro _ _ _ s h; exact ⟨h, hrefl s.1⟩
  · intro _ _ r f s h; exact ⟨h, hrefl s.1, r, rfl⟩
  · intro α act P hAct ⟨b, step⟩ hb
    letI := Classical.propDecidable
    change let (t, w') := (if sched step then
        let (a, s') := act.run (b, step + 1)
        if inv s'.1 ∧ frame b s'.1 then (pure a, s') else (act, (b, step + 1))
      else (act, (b, step + 1)))
      inv w'.1 ∧ frame b w'.1 ∧ ∀ s, inv s.1 → let (a, s') := t.run s; inv s'.1 ∧ frame s.1 s'.1 ∧ P a
    cases sched step with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨hb, hrefl b, hAct⟩
    | true =>
      simp only [↓reduceIte]
      have h1 := hAct (b, step + 1) hb
      cases hR : act.run (b, step + 1) with
      | mk a s' =>
        rw [hR] at h1
        dsimp only
        simp only [h1.1, h1.2.1, and_self, ↓reduceIte]
        exact ⟨trivial, trivial, fun s hs => ⟨hs, hrefl s.1, h1.2.2⟩⟩
  · intro _ _ s h; exact ⟨h, hrefl s.1⟩
  · intro α t ⟨b, step⟩ hb
    change let (res, w') := (if sched step then
        let (res, s') := runSafeTask inv frame t (b, step + 1)
        (some res, s')
      else (none, (b, step + 1)))
      inv w'.1 ∧ frame b w'.1 ∧ match res with | some (.error msg) => msg ≠ "" | _ => True
    cases sched step with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨hb, hrefl b, trivial⟩
    | true =>
      simp only [↓reduceIte]
      unfold runSafeTask
      cases hR : (t : StateM (BaseW × Nat) α).run (b, step + 1) with
      | mk a s' =>
        dsimp only
        by_cases hc : inv s'.1 ∧ frame b s'.1
        · simp only [hc]; exact ⟨hc.1, hc.2, trivial⟩
        · simp only [hc, ↓reduceIte]; exact ⟨hb, hrefl b, by decide⟩
  · intro α t s hs
    change let (res, w') := runSafeTask inv frame t s
      inv w'.1 ∧ frame s.1 w'.1 ∧ match res with | .error msg => msg ≠ "" | .ok _ => True
    unfold runSafeTask
    cases hR : (t : StateM (BaseW × Nat) α).run s with
    | mk a s' =>
      dsimp only
      by_cases hc : inv s'.1 ∧ frame s.1 s'.1
      · simp only [hc]; exact ⟨hc.1, hc.2, trivial⟩
      · simp only [hc, ↓reduceIte]; exact ⟨hs, hrefl s.1, by decide⟩
  · intro α t P hT ⟨b, step⟩ hb
    change let (res, w') := (if sched step then
        let (res, s') := runSafeTask inv frame t (b, step + 1)
        (some res, s')
      else (none, (b, step + 1)))
      inv w'.1 ∧ frame b w'.1 ∧ match res with | none => True | some (.ok a) => P a | some (.error msg) => msg ≠ ""
    cases sched step with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨hb, hrefl b, trivial⟩
    | true =>
      simp only [↓reduceIte]
      unfold runSafeTask
      have h1 := hT (b, step + 1) hb
      cases hR : (t : StateM (BaseW × Nat) α).run (b, step + 1) with
      | mk a s' =>
        rw [hR] at h1
        dsimp only
        have hc : inv s'.1 ∧ frame b s'.1 := ⟨h1.1, h1.2.1⟩
        simp only [hc]
        exact ⟨h1.1, h1.2.1, h1.2.2⟩
  · intro α t P hT s hs
    change let (res, w') := runSafeTask inv frame t s
      inv w'.1 ∧ frame s.1 w'.1 ∧ match res with | .ok a => P a | .error msg => msg ≠ ""
    unfold runSafeTask
    have h1 := hT s hs
    cases hR : (t : StateM (BaseW × Nat) α).run s with
    | mk a s' =>
      rw [hR] at h1
      dsimp only
      have hc : inv s'.1 ∧ frame s.1 s'.1 := ⟨h1.1, h1.2.1⟩
      simp only [hc]
      exact ⟨h1.1, h1.2.1, h1.2.2⟩
  · intro α act QOk QErr _ hAct s hs
    change let (res, w') := (let (a, s') := act.run s; (Except.ok a, s'))
      inv w'.1 ∧ match res with | .ok a => QOk s a w' | .error msg => msg ≠ "" ∧ QErr s w'
    have h1 := hAct s hs
    cases hR : act.run s with
    | mk a s' =>
      rw [hR] at h1
      exact ⟨h1.1, h1.2.1⟩

/-- Base simulation world pairing `(HealthySimState × EnvironState)` with `ProcTableState RawFd`. -/
abbrev SimCellWorld : Type :=
  (Model.Internal.HealthySimState × EnvVars.Raw.Model.EnvironState) × Internal.ProcTableState RawFd

private noncomputable def witnessRawFd : RawFd :=
  Classical.choice inferInstance

private def dummyRawHid : RawFd → Nat :=
  fun _ => 0

private def liftSimOs {α : Type} (act : StateM Model.Internal.HealthySimState α) :
    StateM (SimCellWorld × Nat) α :=
  fun (((hs, env), tbl), step) =>
    let (a, hs') := act.run hs
    (a, (((hs', env), tbl), step))

private noncomputable def liftSimFdPair (act : StateM Model.Internal.HealthySimState (Except Errno (Files.HandleId × Files.HandleId))) :
    StateM (SimCellWorld × Nat) (Except Errno (RawFd × RawFd)) :=
  fun (((hs, env), tbl), step) =>
    let (r, hs') := act.run hs
    (r.map (fun _ => (witnessRawFd, witnessRawFd)), (((hs', env), tbl), step))

private noncomputable def liftSimFd (act : StateM Model.Internal.HealthySimState (Except Errno Files.HandleId)) :
    StateM (SimCellWorld × Nat) (Except Errno RawFd) :=
  fun (((hs, env), tbl), step) =>
    let (r, hs') := act.run hs
    (r.map (fun _ => witnessRawFd), (((hs', env), tbl), step))

/-- Project `SimCellWorld × Nat` into `Model.FullHostWorld`. -/
def projSimFullRaw (s : SimCellWorld × Nat) : Model.FullHostWorld :=
  { proc := Model.Internal.projSimProc s.1.1.1
    files := Model.Internal.projSimFiles s.1.1.1
    time := Model.Internal.projSimTime s.1.1.1
    env := s.1.1.2 }

/-- Project `SimCellWorld × Nat` into `Internal.ProcTableState RawFd`. -/
def projSimFullCell (s : SimCellWorld × Nat) : Internal.ProcTableState RawFd :=
  s.1.2

/-- Concrete `Core.StateCellM` witness over `SimCellWorld × Nat`. -/
def simFullStateCell : Core.StateCellM (StateM (SimCellWorld × Nat)) (Internal.ProcTableState RawFd) where
  get := fun (((hs, env), tbl), step) => (tbl, (((hs, env), tbl), step))
  modifyGet := fun f (((hs, env), tbl), step) =>
    let (a, tbl') := f tbl
    (a, (((hs, env), tbl'), step))

/-- Concrete `Internal.ProcessSysCapsM` witness over `SimCellWorld × Nat`. -/
noncomputable def simFullSysCaps : Internal.ProcessSysCapsM (StateM (SimCellWorld × Nat)) where
  proc :=
    { pipe2 := fun fl => liftSimFdPair (healthySimHostCaps.proc.pipe2 fl)
      waitpid := fun pid fl => liftSimOs (healthySimHostCaps.proc.waitpid pid fl)
      kill := fun tgt sig => liftSimOs (healthySimHostCaps.proc.kill tgt sig)
      pidfd_open := fun pid fl => liftSimFd (healthySimHostCaps.proc.pidfd_open pid fl)
      pidfd_send_signal := fun fd sig fl => liftSimOs (healthySimHostCaps.proc.pidfd_send_signal (dummyRawHid fd) sig fl)
      getpid := liftSimOs healthySimHostCaps.proc.getpid
      getuid := liftSimOs healthySimHostCaps.proc.getuid }
  files :=
    { openat := fun d p fl m => liftSimFd (healthySimHostCaps.files.openat (d.map dummyRawHid) p fl m)
      openat2 := fun d p how => liftSimFd (healthySimHostCaps.files.openat2 (d.map dummyRawHid) p how)
      close := fun fd => liftSimOs (healthySimHostCaps.files.close (dummyRawHid fd))
      read := fun fd cap => liftSimOs (healthySimHostCaps.files.read (dummyRawHid fd) cap)
      write := fun fd bs => liftSimOs (healthySimHostCaps.files.write (dummyRawHid fd) bs)
      fstat := fun fd => liftSimOs (healthySimHostCaps.files.fstat (dummyRawHid fd))
      fstatat := fun d p fl => liftSimOs (healthySimHostCaps.files.fstatat (d.map dummyRawHid) p fl)
      faccessat := fun d p m fl => liftSimOs (healthySimHostCaps.files.faccessat (d.map dummyRawHid) p m fl)
      mkdirat := fun d p m => liftSimOs (healthySimHostCaps.files.mkdirat (d.map dummyRawHid) p m)
      unlinkat := fun d p rd => liftSimOs (healthySimHostCaps.files.unlinkat (d.map dummyRawHid) p rd)
      renameat2 := fun od op nd np fl => liftSimOs (healthySimHostCaps.files.renameat2 (od.map dummyRawHid) op (nd.map dummyRawHid) np fl)
      symlinkat := fun t d lp => liftSimOs (healthySimHostCaps.files.symlinkat t (d.map dummyRawHid) lp)
      readlinkat := fun d p c => liftSimOs (healthySimHostCaps.files.readlinkat (d.map dummyRawHid) p c)
      getdents64 := fun fd c => liftSimOs (healthySimHostCaps.files.getdents64 (dummyRawHid fd) c)
      fchmodat := fun d p m => liftSimOs (healthySimHostCaps.files.fchmodat (d.map dummyRawHid) p m)
      fchmod := fun fd m => liftSimOs (healthySimHostCaps.files.fchmod (dummyRawHid fd) m)
      flock := fun fd op => liftSimOs (healthySimHostCaps.files.flock (dummyRawHid fd) op)
      fcntl := fun fd cmd => liftSimOs (healthySimHostCaps.files.fcntl (dummyRawHid fd) cmd)
      fsync := fun fd => liftSimOs (healthySimHostCaps.files.fsync (dummyRawHid fd))
      getcwd := fun c => liftSimOs (healthySimHostCaps.files.getcwd c)
      lseek := fun fd off wh => liftSimOs (healthySimHostCaps.files.lseek (dummyRawHid fd) off wh)
      reopenReadOnly := fun fd => liftSimFd (healthySimHostCaps.files.reopenReadOnly (dummyRawHid fd))
      dupStdio := fun sl => liftSimFd (healthySimHostCaps.files.dupStdio sl) }
  poll :=
    { ppoll := fun fds to? => liftSimOs (healthySimHostCaps.poll.ppoll (fds.map fun p => (dummyRawHid p.1, p.2)) to?)
      eventfd2 := fun iv fl => liftSimFd (healthySimHostCaps.poll.eventfd2 iv fl) }
  timeRand :=
    { clock_gettime := fun clk => liftSimOs (healthySimHostCaps.timeRand.clock_gettime clk)
      clock_nanosleep := fun clk abs ts => liftSimOs (healthySimHostCaps.timeRand.clock_nanosleep clk abs ts)
      getrandom := fun len fl => liftSimOs (healthySimHostCaps.timeRand.getrandom len fl) }
  postFork :=
    { spawn := fun _ (((hs, env), tbl), step) =>
        (.ok { pid := 100, pgid := some 100 },
         ((({ hs with child100? := some (.exited 0) }, env), tbl), step))
      spawnWithBarrier := fun _ => pure (.error { kind := .invalidInput, message := "unused" })
      releaseBarrier := fun _ => pure (.error { kind := .invalidInput, message := "unused" })
      abortBarrier := fun _ => pure (.error { kind := .invalidInput, message := "unused" }) }
  envRaw :=
    { mapRawError := EnvVars.Raw.Model.mapRawErrorModel
      getEnv := fun key (((hs, env), tbl), step) =>
        (EnvVars.Raw.Model.rawGetEnvModel env key, (((hs, env), tbl), step))
      listEnv := fun (((hs, env), tbl), step) =>
        (EnvVars.Raw.Model.rawListEnvModel env, (((hs, env), tbl), step))
      listEnvironBytes := fun (((hs, env), tbl), step) =>
        (env.entries, (((hs, env), tbl), step)) }

private theorem projSimFullRaw_wf (hs : Model.Internal.HealthySimState)
    {env : EnvVars.Raw.Model.EnvironState} (hEnv : env.isWellFormed = true)
    (tbl : Internal.ProcTableState RawFd) (step : Nat) :
    Model.fullRawWf (projSimFullRaw (((hs, env), tbl), step)) = true := by
  unfold Model.fullRawWf projSimFullRaw
  have h1 : (Model.Internal.projSimProc hs).wf = true := rfl
  have h2 : (Model.Internal.projSimFiles hs).wf = true := rfl
  have h3 : (Model.Internal.projSimTime hs).wf = true := rfl
  simp [h1, h2, h3, hEnv]

private theorem simHostWorldWf_clean (hs : Model.Internal.HealthySimState) :
    Model.hostWorldWf (projSimToHostWorld { hs with tbl := {} }) = true :=
  rfl

private theorem simFullSysCaps_obeys :
    Core.ObeysStep projSimFullRaw Model.fullRawWf
      (Model.execFullRawStep simFullSysCaps) Model.allowedFullRawStep := by
  intro ⟨⟨⟨hs, env⟩, tbl⟩, step⟩ req hWf
  have hEnv : env.isWellFormed = true := by
    unfold Model.fullRawWf projSimFullRaw at hWf
    simp only [Bool.and_eq_true] at hWf
    exact hWf.2
  let hs0 : Model.Internal.HealthySimState := { hs with tbl := {} }
  have hHw0 : Model.hostWorldWf (projSimToHostWorld hs0) = true := simHostWorldWf_clean hs
  cases req with
  | proc pr =>
    cases pr with
    | pipe2 flags =>
      have hStep := healthySimHostCaps_refines_allowedHostCapStep hs0 (.proc (.pipe2 flags)) hHw0
      dsimp only [Model.execHostCapStep, Model.HostProcReq.toProcessReq, LinuxSyscall.Process.execProcessReq,
        Model.allowedHostCapStep, Model.execFullRawStep, Model.execRawFdProcReq, simFullSysCaps,
        liftSimFdPair, healthySimHostCaps, Functor.map, StateT.map, Bind.bind, StateT.bind,
        Pure.pure, StateT.pure, StateT.run, Function.comp] at hStep ⊢
      have hEqRun : Model.Internal.healthySimDeps.proc.pipe2 flags hs =
          let (r, s') := Model.Internal.healthySimDeps.proc.pipe2 flags hs0
          (r, { s' with tbl := hs.tbl }) := by
        dsimp only [Model.Internal.healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
        split
        · rfl
        · split <;> rfl
      rw [hEqRun]
      cases hR : Model.Internal.healthySimDeps.proc.pipe2 flags hs0 with
      | mk r s' =>
        rw [hR] at hStep
        dsimp only at hStep ⊢
        refine ⟨hWf, projSimFullRaw_wf _ hEnv tbl step, LinuxSyscall.Process.outcomeOfPiped r, ?_, hStep.2.2.1, hStep.2.2.2.1, rfl⟩
        cases r with
        | ok p => exact trivial
        | error e => exact rfl
    | waitpid pid flags =>
      have hStep := healthySimHostCaps_refines_allowedHostCapStep hs0 (.proc (.waitpid pid flags)) hHw0
      dsimp only [Model.execHostCapStep, Model.HostProcReq.toProcessReq, LinuxSyscall.Process.execProcessReq,
        Model.allowedHostCapStep, Model.execFullRawStep, Model.execRawFdProcReq, simFullSysCaps,
        liftSimOs, healthySimHostCaps, Functor.map, StateT.map, Bind.bind, StateT.bind,
        Pure.pure, StateT.pure, StateT.run, Function.comp] at hStep ⊢
      have hEqRun : Model.Internal.healthySimDeps.proc.waitpid pid flags hs =
          let (r, s') := Model.Internal.healthySimDeps.proc.waitpid pid flags hs0
          (r, { s' with tbl := hs.tbl }) := rfl
      rw [hEqRun]
      cases hR : Model.Internal.healthySimDeps.proc.waitpid pid flags hs0 with
      | mk r s' =>
        rw [hR] at hStep; dsimp only at hStep ⊢
        refine ⟨hWf, projSimFullRaw_wf _ hEnv tbl step, LinuxSyscall.Process.outcomeOfWaited r, ?_, hStep.2.2.1, hStep.2.2.2.1, rfl⟩
        cases r <;> rfl
    | kill target sig =>
      have hStep := healthySimHostCaps_refines_allowedHostCapStep hs0 (.proc (.kill target sig)) hHw0
      dsimp only [Model.execHostCapStep, Model.HostProcReq.toProcessReq, LinuxSyscall.Process.execProcessReq,
        Model.allowedHostCapStep, Model.execFullRawStep, Model.execRawFdProcReq, simFullSysCaps,
        liftSimOs, healthySimHostCaps, Functor.map, StateT.map, Bind.bind, StateT.bind,
        Pure.pure, StateT.pure, StateT.run, Function.comp] at hStep ⊢
      have hEqRun : Model.Internal.healthySimDeps.proc.kill target sig hs =
          let (r, s') := Model.Internal.healthySimDeps.proc.kill target sig hs0
          (r, { s' with tbl := hs.tbl }) := rfl
      rw [hEqRun]
      cases hR : Model.Internal.healthySimDeps.proc.kill target sig hs0 with
      | mk r s' =>
        rw [hR] at hStep; dsimp only at hStep ⊢
        refine ⟨hWf, projSimFullRaw_wf _ hEnv tbl step, LinuxSyscall.Process.outcomeOfUnit r, ?_, hStep.2.2.1, hStep.2.2.2.1, rfl⟩
        cases r with | ok _ => trivial | error _ => rfl
  | files fr =>
    let mapH : Model.RawFdFilesReq → Model.HostFilesReq
      | .close fd => .close (dummyRawHid fd)
      | .read fd cap => .read (dummyRawHid fd) cap
      | .write fd bs => .write (dummyRawHid fd) bs
      | .fstatat d p fl => .fstatat (d.map dummyRawHid) p fl
      | .faccessat d p m fl => .faccessat (d.map dummyRawHid) p m fl
      | .fcntl fd cmd => .fcntl (dummyRawHid fd) cmd
    have hMapEq : (mapH fr).toFilesReq = Model.mapRawFdFilesReq dummyRawHid fr := by cases fr <;> rfl
    have hStep := healthySimHostCaps_refines_allowedHostCapStep hs0 (.files (mapH fr)) hHw0
    cases fr with
    | close fd =>
      dsimp only [mapH, Model.execHostCapStep, Model.HostFilesReq.toFilesReq, Files.execFilesReq,
        Model.allowedHostCapStep, Model.execFullRawStep, Model.execRawFdFilesReq, simFullSysCaps,
        liftSimOs, healthySimHostCaps, Functor.map, StateT.map, Bind.bind, StateT.bind,
        Pure.pure, StateT.pure, StateT.run, Function.comp] at hStep ⊢
      have hEq : Model.Internal.healthySimDeps.files.close (dummyRawHid fd) hs =
          let (r, s') := Model.Internal.healthySimDeps.files.close (dummyRawHid fd) hs0
          (r, { s' with tbl := hs.tbl }) := by
        dsimp only [Model.Internal.healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
        cases Files.assocGet hs.simFds (dummyRawHid fd) <;> rfl
      rw [hEq]
      cases hR : Model.Internal.healthySimDeps.files.close (dummyRawHid fd) hs0 with
      | mk r s' =>
        rw [hR] at hStep; dsimp only at hStep ⊢
        exact ⟨hWf, projSimFullRaw_wf _ hEnv tbl step, ⟨dummyRawHid, hStep.2.2.1⟩,
          hStep.2.2.2.1, hStep.2.2.2.2.1, rfl, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | read fd cap =>
      dsimp only [mapH, Model.execHostCapStep, Model.HostFilesReq.toFilesReq, Files.execFilesReq,
        Model.allowedHostCapStep, Model.execFullRawStep, Model.execRawFdFilesReq, simFullSysCaps,
        liftSimOs, healthySimHostCaps, Functor.map, StateT.map, Bind.bind, StateT.bind,
        Pure.pure, StateT.pure, StateT.run, Function.comp] at hStep ⊢
      have hEq : Model.Internal.healthySimDeps.files.read (dummyRawHid fd) cap hs =
          let (r, s') := Model.Internal.healthySimDeps.files.read (dummyRawHid fd) cap hs0
          (r, { s' with tbl := hs.tbl }) := by
        dsimp only [Model.Internal.healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
        cases Files.assocGet hs.simFds (dummyRawHid fd) with
        | none => rfl
        | some d => dsimp only; repeat (first | rfl | split)
      rw [hEq]
      cases hR : Model.Internal.healthySimDeps.files.read (dummyRawHid fd) cap hs0 with
      | mk r s' =>
        rw [hR] at hStep; dsimp only at hStep ⊢
        refine ⟨hWf, projSimFullRaw_wf _ hEnv tbl step, ⟨dummyRawHid, hStep.2.2.1⟩,
          hStep.2.2.2.1, hStep.2.2.2.2.1, rfl, ?_, (fun _ _ _ h => by cases h)⟩
        intro fd' cap' bs hReq hOut
        cases hReq
        exact hStep.2.2.2.2.2.2.2.1 (dummyRawHid _) _ bs rfl hOut
    | write fd bs =>
      dsimp only [mapH, Model.execHostCapStep, Model.HostFilesReq.toFilesReq, Files.execFilesReq,
        Model.allowedHostCapStep, Model.execFullRawStep, Model.execRawFdFilesReq, simFullSysCaps,
        liftSimOs, healthySimHostCaps, Functor.map, StateT.map, Bind.bind, StateT.bind,
        Pure.pure, StateT.pure, StateT.run, Function.comp] at hStep ⊢
      have hEq : Model.Internal.healthySimDeps.files.write (dummyRawHid fd) bs hs =
          let (r, s') := Model.Internal.healthySimDeps.files.write (dummyRawHid fd) bs hs0
          (r, { s' with tbl := hs.tbl }) := by
        dsimp only [Model.Internal.healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
        cases Files.assocGet hs.simFds (dummyRawHid fd) with
        | none => rfl
        | some d => dsimp only; split <;> rfl
      rw [hEq]
      cases hR : Model.Internal.healthySimDeps.files.write (dummyRawHid fd) bs hs0 with
      | mk r s' =>
        rw [hR] at hStep; dsimp only at hStep ⊢
        refine ⟨hWf, projSimFullRaw_wf _ hEnv tbl step, ⟨dummyRawHid, hStep.2.2.1⟩,
          hStep.2.2.2.1, hStep.2.2.2.2.1, rfl, (fun _ _ _ h => by cases h), ?_⟩
        intro fd' data' n hReq hOut
        cases hReq
        exact hStep.2.2.2.2.2.2.2.2 (dummyRawHid _) _ n rfl hOut
    | fstatat d p fl =>
      dsimp only [mapH, Model.execHostCapStep, Model.HostFilesReq.toFilesReq, Files.execFilesReq,
        Model.allowedHostCapStep, Model.execFullRawStep, Model.execRawFdFilesReq, simFullSysCaps,
        liftSimOs, healthySimHostCaps, Functor.map, StateT.map, Bind.bind, StateT.bind,
        Pure.pure, StateT.pure, StateT.run, Function.comp] at hStep ⊢
      have hEq : Model.Internal.healthySimDeps.files.fstatat (d.map dummyRawHid) p fl hs =
          let (r, s') := Model.Internal.healthySimDeps.files.fstatat (d.map dummyRawHid) p fl hs0
          (r, { s' with tbl := hs.tbl }) := rfl
      rw [hEq]
      cases hR : Model.Internal.healthySimDeps.files.fstatat (d.map dummyRawHid) p fl hs0 with
      | mk r s' =>
        rw [hR] at hStep; dsimp only at hStep ⊢
        exact ⟨hWf, projSimFullRaw_wf _ hEnv tbl step, ⟨dummyRawHid, hStep.2.2.1⟩,
          hStep.2.2.2.1, hStep.2.2.2.2.1, rfl, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | faccessat d p m fl =>
      dsimp only [mapH, Model.execHostCapStep, Model.HostFilesReq.toFilesReq, Files.execFilesReq,
        Model.allowedHostCapStep, Model.execFullRawStep, Model.execRawFdFilesReq, simFullSysCaps,
        liftSimOs, healthySimHostCaps, Functor.map, StateT.map, Bind.bind, StateT.bind,
        Pure.pure, StateT.pure, StateT.run, Function.comp] at hStep ⊢
      have hEq : Model.Internal.healthySimDeps.files.faccessat (d.map dummyRawHid) p m fl hs =
          let (r, s') := Model.Internal.healthySimDeps.files.faccessat (d.map dummyRawHid) p m fl hs0
          (r, { s' with tbl := hs.tbl }) := rfl
      rw [hEq]
      cases hR : Model.Internal.healthySimDeps.files.faccessat (d.map dummyRawHid) p m fl hs0 with
      | mk r s' =>
        rw [hR] at hStep; dsimp only at hStep ⊢
        exact ⟨hWf, projSimFullRaw_wf _ hEnv tbl step, ⟨dummyRawHid, hStep.2.2.1⟩,
          hStep.2.2.2.1, hStep.2.2.2.2.1, rfl, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | fcntl fd cmd =>
      dsimp only [mapH, Model.execHostCapStep, Model.HostFilesReq.toFilesReq, Files.execFilesReq,
        Model.allowedHostCapStep, Model.execFullRawStep, Model.execRawFdFilesReq, simFullSysCaps,
        liftSimOs, healthySimHostCaps, Functor.map, StateT.map, Bind.bind, StateT.bind,
        Pure.pure, StateT.pure, StateT.run, Function.comp] at hStep ⊢
      have hEq : Model.Internal.healthySimDeps.files.fcntl (dummyRawHid fd) cmd hs =
          let (r, s') := Model.Internal.healthySimDeps.files.fcntl (dummyRawHid fd) cmd hs0
          (r, { s' with tbl := hs.tbl }) := by
        dsimp only [Model.Internal.healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
        cases Files.assocGet hs.simFds (dummyRawHid fd) with
        | none => rfl
        | some d => dsimp only; cases cmd <;> repeat (first | rfl | split)
      rw [hEq]
      cases hR : Model.Internal.healthySimDeps.files.fcntl (dummyRawHid fd) cmd hs0 with
      | mk r s' =>
        rw [hR] at hStep; dsimp only at hStep ⊢
        exact ⟨hWf, projSimFullRaw_wf _ hEnv tbl step, ⟨dummyRawHid, hStep.2.2.1⟩,
          hStep.2.2.2.1, hStep.2.2.2.2.1, rfl, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  | poll entries timeout? =>
    have hStep := healthySimHostCaps_refines_allowedHostCapStep hs0
      (.poll (entries.map fun p => (dummyRawHid p.1, p.2)) timeout?) hHw0
    dsimp only [Model.execHostCapStep, Model.allowedHostCapStep, Model.execFullRawStep,
      simFullSysCaps, liftSimOs, healthySimHostCaps,
      Functor.map, StateT.map, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Function.comp] at hStep ⊢
    have hEq : Model.Internal.healthySimDeps.poll.ppoll (entries.map fun p => (dummyRawHid p.1, p.2)) timeout? hs =
        let (r, s') := Model.Internal.healthySimDeps.poll.ppoll (entries.map fun p => (dummyRawHid p.1, p.2)) timeout? hs0
        (r, { s' with tbl := hs.tbl }) := by
      dsimp only [Model.Internal.healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
      split
      · rfl
      · cases timeout? with
        | none => rfl
        | some ts =>
          dsimp only
          cases TimeRand.modelOps.clock_nanosleep TimeRand.ClockId.monotonic false
            { sec := ts.sec, nsec := ts.nsec } (Model.Internal.toSimTimeState hs0) with
          | mk _ _ => rfl
    rw [hEq]
    cases hR : Model.Internal.healthySimDeps.poll.ppoll (entries.map fun p => (dummyRawHid p.1, p.2)) timeout? hs0 with
    | mk r s' =>
      rw [hR] at hStep; dsimp only at hStep ⊢
      refine ⟨hWf, projSimFullRaw_wf _ hEnv tbl step, hStep.2.2.1, hStep.2.2.2.1, rfl, ?_⟩
      cases r with
      | ok revents =>
        dsimp only [Model.rawFdPollOutOf]
        exact (hStep.2.2.2.2.2.2).trans (Array.size_map ..)
      | error e =>
        dsimp only [Model.rawFdPollOutOf]
        exact hStep.2.2.2.2.2.2
  | timeRand tr =>
    have hStep := healthySimHostCaps_refines_allowedHostCapStep hs0 (.timeRand tr) hHw0
    cases tr with
    | clock_gettime clk =>
      dsimp only [Model.execHostCapStep, TimeRand.execTimeRandReq, Model.allowedHostCapStep,
        Model.execFullRawStep, simFullSysCaps, liftSimOs, healthySimHostCaps,
        Functor.map, StateT.map, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Function.comp] at hStep ⊢
      have hEq : Model.Internal.healthySimDeps.timeRand.clock_gettime clk hs =
          let (r, s') := Model.Internal.healthySimDeps.timeRand.clock_gettime clk hs0
          (r, { s' with tbl := hs.tbl }) := rfl
      rw [hEq]
      cases hR : Model.Internal.healthySimDeps.timeRand.clock_gettime clk hs0 with
      | mk r s' =>
        rw [hR] at hStep; dsimp only at hStep ⊢
        exact ⟨hWf, projSimFullRaw_wf _ hEnv tbl step, hStep.2.2.1, hStep.2.2.2.1, hStep.2.2.2.2.1, rfl⟩
    | clock_nanosleep clk abs ts =>
      dsimp only [Model.execHostCapStep, TimeRand.execTimeRandReq, Model.allowedHostCapStep,
        Model.execFullRawStep, simFullSysCaps, liftSimOs, healthySimHostCaps,
        Functor.map, StateT.map, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Function.comp] at hStep ⊢
      have hEq : Model.Internal.healthySimDeps.timeRand.clock_nanosleep clk abs ts hs =
          let (r, s') := Model.Internal.healthySimDeps.timeRand.clock_nanosleep clk abs ts hs0
          (r, { s' with tbl := hs.tbl }) := rfl
      rw [hEq]
      cases hR : Model.Internal.healthySimDeps.timeRand.clock_nanosleep clk abs ts hs0 with
      | mk r s' =>
        rw [hR] at hStep; dsimp only at hStep ⊢
        exact ⟨hWf, projSimFullRaw_wf _ hEnv tbl step, hStep.2.2.1, hStep.2.2.2.1, hStep.2.2.2.2.1, rfl⟩
    | getrandom len fl =>
      dsimp only [Model.execHostCapStep, TimeRand.execTimeRandReq, Model.allowedHostCapStep,
        Model.execFullRawStep, simFullSysCaps, liftSimOs, healthySimHostCaps,
        Functor.map, StateT.map, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Function.comp] at hStep ⊢
      have hEq : Model.Internal.healthySimDeps.timeRand.getrandom len fl hs =
          let (r, s') := Model.Internal.healthySimDeps.timeRand.getrandom len fl hs0
          (r, { s' with tbl := hs.tbl }) := rfl
      rw [hEq]
      cases hR : Model.Internal.healthySimDeps.timeRand.getrandom len fl hs0 with
      | mk r s' =>
        rw [hR] at hStep; dsimp only at hStep ⊢
        exact ⟨hWf, projSimFullRaw_wf _ hEnv tbl step, hStep.2.2.1, hStep.2.2.2.1, hStep.2.2.2.2.1, rfl⟩
  | postFork _ =>
    dsimp only [Model.execFullRawStep, simFullSysCaps, Model.allowedFullRawStep,
      Functor.map, StateT.map, StateT.run, Function.comp, Model.rawFdPostForkOutOf]
    exact ⟨hWf, projSimFullRaw_wf _ hEnv tbl step, rfl, rfl, by decide, by decide, fun _ => rfl⟩
  | envRaw er =>
    cases er <;> exact ⟨hWf, hWf, rfl, rfl, rfl, rfl, rfl⟩

private theorem simFullSysCaps_frame :
    ∀ (w : SimCellWorld × Nat) (req : Model.FullRawReq),
      Model.fullRawWf (projSimFullRaw w) = true →
      projSimFullCell ((Model.execFullRawStep simFullSysCaps req).run w).2 = projSimFullCell w := by
  intro ⟨⟨⟨hs, env⟩, tbl⟩, step⟩ req _
  cases req with
  | proc pr => cases pr <;> rfl
  | files fr => cases fr <;> rfl
  | poll _ _ => rfl
  | timeRand tr => cases tr <;> rfl
  | postFork _ => rfl
  | envRaw er => cases er <;> rfl

private theorem simFullStateCell_obeys :
    Core.ObeysStateCell projSimFullRaw projSimFullCell simFullStateCell :=
  ⟨fun ⟨⟨⟨_, _⟩, _⟩, _⟩ => ⟨rfl, rfl, rfl⟩,
   fun _ ⟨⟨⟨_, _⟩, _⟩, _⟩ => ⟨rfl, rfl, rfl⟩⟩

/-- Non-vacuity witness showing all capability, concurrency-frame, and state-cell hypotheses of
    `LeanSwe.Process.Proofs.obeys_model` are inhabited across every schedule `sched : Nat → Bool`. -/
theorem process_obeys_model_nonvacuous (sched : Nat → Bool) :
    ∃ (W : Type) (projRaw : W → Model.FullHostWorld)
      (raw : Internal.ProcessSysCapsM (StateM W))
      (conc : Core.ConcOpsM (StateM W))
      (projCell : W → Internal.ProcCellS conc.Ref conc.TaskHandle)
      (cell : Core.StateCellM (StateM W) (Internal.ProcCellS conc.Ref conc.TaskHandle)),
      Core.ObeysStep projRaw Model.fullRawWf (Model.execFullRawStep raw) Model.allowedFullRawStep ∧
      (∀ w req, Model.fullRawWf (projRaw w) = true →
        projCell ((Model.execFullRawStep raw req).run w).2 = projCell w) ∧
      Core.ObeysConcFrame (fun w => Model.fullRawWf (projRaw w) = true)
        (fun w₁ w₂ => projCell w₂ = projCell w₁) conc ∧
      Core.ObeysStateCell projRaw projCell cell :=
  ⟨SimCellWorld × Nat, projSimFullRaw, simFullSysCaps,
   schedFrameConcOps SimCellWorld
     (fun b => Model.fullRawWf { proc := Model.Internal.projSimProc b.1.1, files := Model.Internal.projSimFiles b.1.1, time := Model.Internal.projSimTime b.1.1, env := b.1.2 } = true)
     (fun b₁ b₂ => b₂.2 = b₁.2) sched,
   projSimFullCell, simFullStateCell,
   simFullSysCaps_obeys,
   simFullSysCaps_frame,
   schedFrameConcOps_obeysConcFrame
     (fun (b : SimCellWorld) => Model.fullRawWf { proc := Model.Internal.projSimProc b.1.1, files := Model.Internal.projSimFiles b.1.1, time := Model.Internal.projSimTime b.1.1, env := b.1.2 } = true)
     (fun (b₁ b₂ : SimCellWorld) => b₂.2 = b₁.2) (fun _ => rfl) sched,
   simFullStateCell_obeys⟩

end LeanSwe.Process.Proofs
