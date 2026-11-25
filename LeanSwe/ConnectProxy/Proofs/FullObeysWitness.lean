import Core.ConcOps
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Model.FullStep
import LeanSwe.ConnectProxy.Proofs.HealthyWitness
import LeanSwe.ConnectProxy.Proofs.FullObeysHelpers

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Internal.HealthySys

/-- Pure schedule-driven `Core.ConcOpsM` witness over `StateM (W × Nat)` parameterized by
    `sched : Nat → Bool`: interleaves spawned tasks when `sched step = true` or defers them when
    `false`, and yields pending `none` vs completed `some (.ok a)` in `pollTask` according to `sched`. -/
def schedConcOps (W : Type) (sched : Nat → Bool) : Core.ConcOpsM (StateM (W × Nat)) where
  Ref := fun α => α
  TaskHandle := fun α => StateM (W × Nat) α
  mkRef := fun x s => (x, s)
  readRef := fun r s => (r, s)
  writeRef := fun _ _ s => ((), s)
  modifyGetRef := fun r f s => ((f r).1, s)
  spawnTask := fun act (w, step) =>
    if sched step then
      let (a, (w', step')) := act.run (w, step + 1)
      (pure a, (w', step'))
    else
      (act, (w, step + 1))
  hasFinished := fun _ (w, step) => (sched step, (w, step + 1))
  pollTask := fun t (w, step) =>
    if sched step then
      let (a, (w', step')) := t.run (w, step + 1)
      (some (.ok a), (w', step'))
    else
      (none, (w, step + 1))
  waitTask := fun t s =>
    let (a, s') := t.run s
    (.ok a, s')
  tryCatchMsg := fun act s =>
    let (a, s') := act.run s
    (.ok a, s')

/-- `schedConcOps W sched` satisfies `Core.ObeysConc` for any schedule `sched` and `W`-invariant `inv`. -/
theorem schedConcOps_obeysConc {W : Type} (inv : W → Prop) (sched : Nat → Bool) :
    Core.ObeysConc (fun p : W × Nat => inv p.1) (schedConcOps W sched) := by
  refine ⟨fun {α} (t : StateM (W × Nat) α) (P : α → Prop) =>
      ∀ s, inv s.1 → let (a, s') := t.run s; inv s'.1 ∧ P a,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ h; exact h
  · intro _ _ _ h; exact h
  · intro _ _ _ _ h; exact h
  · intro _ _ r f _ h; exact ⟨h, r, rfl⟩
  · intro α act P hAct ⟨w, step⟩ h
    change (match (if sched step then let (a, s') := act.run (w, step + 1); (pure a, s') else (act, (w, step + 1))) with
      | (t, s') => inv s'.1 ∧ ∀ s, inv s.1 → let (a, s'') := (t : StateM (W × Nat) α).run s; inv s''.1 ∧ P a)
    cases hS : sched step with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨h, hAct⟩
    | true =>
      simp only [↓reduceIte]
      have h1 := hAct (w, step + 1) h
      cases hR : act.run (w, step + 1) with
      | mk a s' =>
        rw [hR] at h1
        exact ⟨h1.1, fun s hs => ⟨hs, h1.2⟩⟩
  · intro _ _ _ h; exact h
  · intro α t P hT ⟨w, step⟩ h
    change (match (if sched step then let (a, s') := (t : StateM (W × Nat) α).run (w, step + 1); (some (Except.ok a), s') else (none, (w, step + 1))) with
      | (res, s') => inv s'.1 ∧ match res with | none => True | some (Except.ok a) => P a | some (Except.error msg) => msg ≠ "")
    cases hS : sched step with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨h, trivial⟩
    | true =>
      simp only [↓reduceIte]
      have h1 := hT (w, step + 1) h
      cases hR : (t : StateM (W × Nat) α).run (w, step + 1) with
      | mk a s' =>
        rw [hR] at h1
        exact h1
  · intro α t P hT s h
    change (match (let (a, s') := (t : StateM (W × Nat) α).run s; (Except.ok a, s')) with
      | (res, s') => inv s'.1 ∧ match res with | .ok a => P a | .error msg => msg ≠ "")
    have h1 := hT s h
    cases hR : (t : StateM (W × Nat) α).run s with
    | mk a s' =>
      rw [hR] at h1
      exact h1
  · intro α act P hAct s h
    change (match (let (a, s') := act.run s; (Except.ok a, s')) with
      | (res, s') => inv s'.1 ∧ match res with | .ok a => P a | .error msg => msg ≠ "")
    have h1 := hAct s h
    cases hR : act.run s with
    | mk a s' =>
      rw [hR] at h1
      exact h1

private noncomputable def witnessFd : RawFd :=
  Classical.choice inferInstance

private def dummyHid : RawFd → Nat :=
  fun _ => 0

private def liftSched {α : Type} (act : StateM HealthySysWorld α) :
    StateM (HealthySysWorld × Nat) α :=
  fun (w, k) => let (r, w') := act.run w; (r, (w', k))

private def liftFdOut {α β : Type} (f : α → β)
    (act : StateM HealthySysWorld (Except Errno α)) :
    StateM (HealthySysWorld × Nat) (Except Errno β) :=
  fun (w, k) => let (r, w') := act.run w; (r.map f, (w', k))

private theorem liftSched_map {α β : Type} (act : StateM HealthySysWorld α) (f : α → β)
    (w : HealthySysWorld) (k : Nat) :
    (f <$> liftSched act).run (w, k) =
      let (b, w') := (f <$> act).run w; (b, (w', k)) := by
  dsimp only [liftSched, Functor.map, StateT.map, StateT.run, Id.run]
  cases act.run w
  rfl

private theorem liftFdOut_map {α β γ : Type} (f : α → β) (g : Except Errno β → γ)
    (act : StateM HealthySysWorld (Except Errno α))
    (w : HealthySysWorld) (k : Nat) :
    (g <$> liftFdOut f act).run (w, k) =
      let (r, w') := act.run w; (g (r.map f), (w', k)) := by
  dsimp only [liftFdOut, Functor.map, StateT.map, StateT.run, Id.run]
  cases act.run w
  rfl

private theorem liftSched_run_bind {α β : Type}
    (act : StateM (HealthySysWorld × Nat) α) (base : StateM HealthySysWorld α)
    (f : α → β) (w : HealthySysWorld) (k : Nat)
    (h : act.run (w, k) = let (a, w') := base.run w; (a, (w', k))) :
    (do let r ← act; pure (f r)).run (w, k) = let (a, w') := base.run w; (f a, (w', k)) := by
  change (let (a, s) := act.run (w, k); (f a, s)) = _
  rw [h]
  cases base.run w
  rfl

private theorem net_step_match {α β : Type}
    (act : StateM HealthySysWorld (Except Errno α))
    (f : α → β)
    (wrapRaw : Except Errno β → RawFdNetOut)
    (wrapMod : Except Errno α → Net.NetOutcome)
    (hOk : ∀ a, RawFdNetOut.MatchesModel (wrapRaw (.ok (f a))) (wrapMod (.ok a)))
    (hErr : ∀ e, RawFdNetOut.MatchesModel (wrapRaw (.error e)) (wrapMod (.error e)))
    (w : HealthySysWorld) (k : Nat) :
    let (no, s') := (wrapRaw <$> liftFdOut f act).run (w, k)
    let (mo, w') := (wrapMod <$> act).run w
    s' = (w', k) ∧ RawFdNetOut.MatchesModel no mo := by
  rw [liftFdOut_map]
  dsimp only [Functor.map, StateT.map, StateT.run, Id.run]
  cases act w with
  | mk r w' =>
    cases r with
    | ok a => exact ⟨rfl, hOk a⟩
    | error e => exact ⟨rfl, hErr e⟩

private theorem net_step_id {α : Type}
    (act : StateM HealthySysWorld (Except Errno α))
    (wrapRaw : Except Errno α → RawFdNetOut)
    (wrapMod : Except Errno α → Net.NetOutcome)
    (hOk : ∀ a, RawFdNetOut.MatchesModel (wrapRaw (.ok a)) (wrapMod (.ok a)))
    (hErr : ∀ e, RawFdNetOut.MatchesModel (wrapRaw (.error e)) (wrapMod (.error e)))
    (w : HealthySysWorld) (k : Nat) :
    let (no, s') := (wrapRaw <$> liftSched act).run (w, k)
    let (mo, w') := (wrapMod <$> act).run w
    s' = (w', k) ∧ RawFdNetOut.MatchesModel no mo := by
  rw [liftSched_map]
  dsimp only [Functor.map, StateT.map, StateT.run, Id.run]
  cases act w with
  | mk r w' =>
    cases r with
    | ok a => exact ⟨rfl, hOk a⟩
    | error e => exact ⟨rfl, hErr e⟩

/-- Lift `sampleHealthySys` onto `StateM (HealthySysWorld × Nat)` over `RawFd` for `obeys_model_nonvacuous`. -/
noncomputable def sampleHealthySysSched : FullSysOpsM (StateM (HealthySysWorld × Nat)) :=
  { files :=
      { openat := fun d p fl m => liftFdOut (fun _ => witnessFd) (sampleHealthySys.files.openat (d.map dummyHid) p fl m)
        openat2 := fun d p how => liftFdOut (fun _ => witnessFd) (sampleHealthySys.files.openat2 (d.map dummyHid) p how)
        close := fun h => liftSched (sampleHealthySys.files.close (dummyHid h))
        read := fun h n => liftSched (sampleHealthySys.files.read (dummyHid h) n)
        write := fun h bs => liftSched (sampleHealthySys.files.write (dummyHid h) bs)
        fstat := fun h => liftSched (sampleHealthySys.files.fstat (dummyHid h))
        fstatat := fun d p fl => liftSched (sampleHealthySys.files.fstatat (d.map dummyHid) p fl)
        faccessat := fun d p m fl => liftSched (sampleHealthySys.files.faccessat (d.map dummyHid) p m fl)
        mkdirat := fun d p m => liftSched (sampleHealthySys.files.mkdirat (d.map dummyHid) p m)
        unlinkat := fun d p rd => liftSched (sampleHealthySys.files.unlinkat (d.map dummyHid) p rd)
        renameat2 := fun od op nd np fl => liftSched (sampleHealthySys.files.renameat2 (od.map dummyHid) op (nd.map dummyHid) np fl)
        symlinkat := fun t d lp => liftSched (sampleHealthySys.files.symlinkat t (d.map dummyHid) lp)
        readlinkat := fun d p c => liftSched (sampleHealthySys.files.readlinkat (d.map dummyHid) p c)
        getdents64 := fun h c => liftSched (sampleHealthySys.files.getdents64 (dummyHid h) c)
        fchmodat := fun d p m => liftSched (sampleHealthySys.files.fchmodat (d.map dummyHid) p m)
        fchmod := fun h m => liftSched (sampleHealthySys.files.fchmod (dummyHid h) m)
        flock := fun h op => liftSched (sampleHealthySys.files.flock (dummyHid h) op)
        fcntl := fun h cmd => liftSched (sampleHealthySys.files.fcntl (dummyHid h) cmd)
        fsync := fun h => liftSched (sampleHealthySys.files.fsync (dummyHid h))
        getcwd := fun c => liftSched (sampleHealthySys.files.getcwd c)
        lseek := fun h off wh => liftSched (sampleHealthySys.files.lseek (dummyHid h) off wh)
        reopenReadOnly := fun h => liftFdOut (fun _ => witnessFd) (sampleHealthySys.files.reopenReadOnly (dummyHid h))
        dupStdio := fun sl => liftFdOut (fun _ => witnessFd) (sampleHealthySys.files.dupStdio sl) }
    net :=
      { socket := fun dom st fl p => liftFdOut (fun _ => witnessFd) (sampleHealthySys.net.socket dom st fl p)
        socketpair := fun dom st fl => liftFdOut (fun _ => (witnessFd, witnessFd)) (sampleHealthySys.net.socketpair dom st fl)
        bind := fun h sa => liftSched (sampleHealthySys.net.bind (dummyHid h) sa)
        listen := fun h bl => liftSched (sampleHealthySys.net.listen (dummyHid h) bl)
        accept4 := fun h fl => liftFdOut (fun (_, sa) => (witnessFd, sa)) (sampleHealthySys.net.accept4 (dummyHid h) fl)
        connect := fun h sa => liftSched (sampleHealthySys.net.connect (dummyHid h) sa)
        getsockopt := fun h opt => liftSched (sampleHealthySys.net.getsockopt (dummyHid h) opt)
        setsockopt := fun h opt val => liftSched (sampleHealthySys.net.setsockopt (dummyHid h) opt val)
        getsockname := fun h => liftSched (sampleHealthySys.net.getsockname (dummyHid h))
        recvfrom := fun h n fl => liftSched (sampleHealthySys.net.recvfrom (dummyHid h) n fl)
        sendto := fun h bs fl => liftSched (sampleHealthySys.net.sendto (dummyHid h) bs fl)
        shutdown := fun h how => liftSched (sampleHealthySys.net.shutdown (dummyHid h) how)
        sendmsg := fun h fds => liftSched (sampleHealthySys.net.sendmsg (dummyHid h) (fds.map dummyHid))
        recvmsg := fun h mf => liftFdOut (fun hs => hs.map (fun _ => witnessFd)) (sampleHealthySys.net.recvmsg (dummyHid h) mf)
        ioctl := fun h req ifn => liftSched (sampleHealthySys.net.ioctl (dummyHid h) req ifn) }
    poll :=
      { ppoll := fun fds to? => liftSched (sampleHealthySys.poll.ppoll (fds.map fun p => (dummyHid p.1, p.2)) to?)
        eventfd2 := fun iv fl => liftFdOut (fun _ => witnessFd) (sampleHealthySys.poll.eventfd2 iv fl) }
    dns :=
      { getaddrinfo := fun h hints => liftSched (sampleHealthySys.dns.getaddrinfo h hints) }
    timeRand :=
      { clock_gettime := fun clk => liftSched (sampleHealthySys.timeRand.clock_gettime clk)
        clock_nanosleep := fun clk ab ts => liftSched (sampleHealthySys.timeRand.clock_nanosleep clk ab ts)
        getrandom := fun n fl => liftSched (sampleHealthySys.timeRand.getrandom n fl) } }

private theorem execRawFdNetReq_sampleHealthy (nreq : RawFdNetReq) (w : HealthySysWorld) (k : Nat) :
    let (no, s') := (execRawFdNetReq sampleHealthySysSched.net nreq).run (w, k)
    let (mo, w') := (Net.execNetReq sampleHealthySys.net (mapRawFdNetReq dummyHid nreq)).run w
    s' = (w', k) ∧ RawFdNetOut.MatchesModel no mo := by
  cases nreq <;> dsimp only [execRawFdNetReq, Net.execNetReq, mapRawFdNetReq, sampleHealthySysSched]
  · apply net_step_match; exact fun _ => trivial; exact fun _ => rfl
  · apply net_step_match; exact fun _ => trivial; exact fun _ => rfl
  · apply net_step_id; exact fun _ => trivial; exact fun _ => rfl
  · apply net_step_id; exact fun _ => trivial; exact fun _ => rfl
  · apply net_step_match; exact (fun ⟨_, _⟩ => rfl); exact fun _ => rfl
  · apply net_step_id; exact fun _ => trivial; exact fun _ => rfl
  · apply net_step_id; exact fun _ => rfl; exact fun _ => rfl
  · apply net_step_id; exact fun _ => trivial; exact fun _ => rfl
  · apply net_step_id; exact fun _ => rfl; exact fun _ => rfl
  · apply net_step_id; exact fun _ => rfl; exact fun _ => rfl
  · apply net_step_id; exact fun _ => rfl; exact fun _ => rfl
  · apply net_step_id; exact fun _ => trivial; exact fun _ => rfl

/-- `sampleHealthySysSched` obeys `allowedFullRawStep` over `HealthySysWorld × Nat`. -/
theorem sampleHealthySysSched_obeys :
    Core.ObeysStep (fun p : HealthySysWorld × Nat => p.1) fullWorldWf
      (execFullRawStep sampleHealthySysSched) allowedFullRawStep := by
  have hRef := sampleHealthySys_refines
  intro ⟨w, k⟩ req hWf
  have hParts := (wf_iff_parts w).mp hWf
  cases req with
  | dns dreq =>
    have hD := hRef.2.2.2.1 w dreq hParts
    have hLift : (Dns.execDnsReq sampleHealthySysSched.dns dreq).run (w, k) =
        let (r, w') := (Dns.execDnsReq sampleHealthySys.dns dreq).run w; (r, (w', k)) := by
      cases dreq; rfl
    dsimp only [execFullRawStep, allowedFullRawStep]
    rw [liftSched_run_bind (Dns.execDnsReq sampleHealthySysSched.dns dreq) (Dns.execDnsReq sampleHealthySys.dns dreq) FullRawOut.dns w k hLift]
    cases hRun : (Dns.execDnsReq sampleHealthySys.dns dreq).run w with
    | mk r w' =>
      rw [hRun] at hD
      exact ⟨(wf_iff_parts w').mpr hD.2.1, hD.1⟩
  | timeRand treq =>
    have hT := hRef.2.2.2.2.1 w treq hParts
    have hLift : (TimeRand.execTimeRandReq sampleHealthySysSched.timeRand treq).run (w, k) =
        let (r, w') := (TimeRand.execTimeRandReq sampleHealthySys.timeRand treq).run w; (r, (w', k)) := by
      cases treq <;> exact liftSched_map _ _ w k
    dsimp only [execFullRawStep, allowedFullRawStep]
    rw [liftSched_run_bind (TimeRand.execTimeRandReq sampleHealthySysSched.timeRand treq) (TimeRand.execTimeRandReq sampleHealthySys.timeRand treq) FullRawOut.timeRand w k hLift]
    cases hRun : (TimeRand.execTimeRandReq sampleHealthySys.timeRand treq).run w with
    | mk r w' =>
      rw [hRun] at hT
      exact ⟨(wf_iff_parts w').mpr hT.2.1, hT.1⟩
  | filesClose d =>
    have hC := hRef.1 w (dummyHid d) hParts
    dsimp only [execFullRawStep, allowedFullRawStep, sampleHealthySysSched, liftSched,
      bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at hC ⊢
    cases hRun : sampleHealthySys.files.close (dummyHid d) w with
    | mk r w' =>
      rw [hRun] at hC
      exact ⟨(wf_iff_parts w').mpr hC.2.1, dummyHid d, hC.1⟩
  | net nreq =>
    have hN := hRef.2.1 w (mapRawFdNetReq dummyHid nreq) hParts
    have hM := execRawFdNetReq_sampleHealthy nreq w k
    dsimp only [execFullRawStep]
    change (let (r, s') := (execRawFdNetReq sampleHealthySysSched.net nreq).run (w, k);
      allowedFullRawStep w (.net nreq) (.net r) s'.1)
    cases hR1 : (execRawFdNetReq sampleHealthySysSched.net nreq).run (w, k) with
    | mk no s' =>
      cases hR2 : (Net.execNetReq sampleHealthySys.net (mapRawFdNetReq dummyHid nreq)).run w with
      | mk mo w' =>
        rw [hR1, hR2] at hM
        rw [hR2] at hN
        rcases hM with ⟨rfl, hMatch⟩
        exact ⟨(wf_iff_parts w').mpr hN.2.1, dummyHid, mo, hMatch, hN.1⟩
  | pollPpoll fds to? =>
    let entries := fds.map fun p => (dummyHid p.1, p.2)
    have hP := hRef.2.2.1 w (.ppoll entries to?) hParts
    have hLift : (do let r ← sampleHealthySysSched.poll.ppoll fds to?; pure (FullRawOut.poll (pollOutcomeOfPolled r))).run (w, k) =
        let (po, w') := (Poll.execPollReq sampleHealthySys.poll (.ppoll entries to?)).run w; (FullRawOut.poll po, (w', k)) := by
      dsimp only [sampleHealthySysSched, liftSched, Poll.execPollReq, Functor.map, StateT.map,
        bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run]
      cases hRun : sampleHealthySys.poll.ppoll entries to? w with
      | mk r w' => cases r <;> rfl
    dsimp only [execFullRawStep]
    rw [hLift]
    cases hRun : (Poll.execPollReq sampleHealthySys.poll (.ppoll entries to?)).run w with
    | mk po w' =>
      rw [hRun] at hP
      exact ⟨(wf_iff_parts w').mpr hP.2.1, dummyHid, hP.1⟩

end LeanSwe.ConnectProxy.Proofs
