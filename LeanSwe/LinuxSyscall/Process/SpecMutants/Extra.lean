import LeanSwe.LinuxSyscall.Process.SpecTests

namespace LeanSwe.LinuxSyscall.Process

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall

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

private def baseMkOps {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixProcessOpsM m fd) : ProcessOpsM m fd :=
  { pipe2 := fun flags => raw.pipe2 flags.toBits
    waitpid := fun pid flags => do
      match ← raw.waitpid pid flags.toBits with
      | .ok tuple => return .ok (WaitResult.ofRawWait4 tuple)
      | .error e => return .error e
    kill := fun pid sig =>
      if sig.isNptlReserved then pure (.error Errno.EINVAL)
      else
        let (tag, arg) := sig.toRaw
        raw.kill pid tag arg
    pidfd_open := fun pid flags => raw.pidfd_open pid flags.toBits
    pidfd_send_signal := fun pfd sig flags =>
      if sig.isNptlReserved then pure (.error Errno.EINVAL)
      else
        let (tag, arg) := sig.toRaw
        raw.pidfd_send_signal pfd tag arg flags.toBits
    getpid := raw.getpid
    getuid := raw.getuid }

private def refRawIoProcOps : PosixProcessOps :=
  { pipe2 := fun _ => pure (.error Errno.EMFILE)
    waitpid := fun _ _ => pure (.error Errno.ECHILD)
    kill := fun _ _ _ => pure (.error Errno.ESRCH)
    pidfd_open := fun _ _ => pure (.error Errno.ESRCH)
    pidfd_send_signal := fun _ _ _ _ => pure (.error Errno.EBADF)
    getpid := pure (.ok 1)
    getuid := pure (.ok 0) }

private def refIoProcOps : ProcessOps :=
  baseMkOps refRawIoProcOps

example : ¬ Core.AllPass (test_process_ops_pidfdSendSignal_processGroupAfterLeaderReapOrMove
    { modelOps with
      pidfd_send_signal := fun hid sig flags => do
        let s ← get
        match assocGet s.fds hid with
        | some (.pidfd targetPid _ _) =>
          match assocGet s.procs targetPid with
          | some e =>
            match flags.processGroup && e.pgid != targetPid with
            | true => return .error Errno.ESRCH
            | false => modelOps.pidfd_send_signal hid sig flags
          | none => modelOps.pidfd_send_signal hid sig flags
        | _ => modelOps.pidfd_send_signal hid sig flags }) := by
  intro h
  exact absurd h.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_model_allowedStep_invariantsAndRejections
    (fun s req out =>
      match req, out with
      | .getpid, .u32 p =>
        if 1 ≤ p && p ≤ maxLinuxPid then some { s with selfPid := p }
        else none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_model_allowedStep_invariantsAndRejections
    (fun s req out =>
      match req, out with
      | .waitpid _ flags, .waited (.exited rPid _) =>
        if !flags.nohang then some (reapThreadGroup s rPid) else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_model_allowedStep_invariantsAndRejections
    (fun s req out =>
      match req, out with
      | .waitpid _ flags, .waited (.exited _ _) =>
        if flags.nohang then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_model_allowedStep_invariantsAndRejections
    (fun s req out =>
      match req, out with
      | .pidfd_open 1001 _, .err code =>
        if code == Errno.ENOENT then some s else none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_model_allowedStep_stopRaceAndQueuedSigcont
    (fun s req out =>
      match req, out with
      | .waitpid 2100 flags, .waited .stillRunning =>
        if flags.nohang && flags.untraced then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.1 (by decide)

example : ¬ Core.AllPass (test_process_model_allowedStep_coreDumpAndRacingSignals
    (fun s req out =>
      match req, out with
      | .waitpid _ _, .waited (.signaled _ _ true) => none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.1 (by decide)

example : ¬ Core.AllPass (test_process_model_allowedStep_coreDumpAndRacingSignals
    (fun s req out =>
      match req, out with
      | .waitpid 2102 _, .waited (.signaled 2102 6 true) => some (reapThreadGroup s 2102)
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_model_allowedStep_coreDumpAndRacingSignals
    (fun s req out =>
      match req, out with
      | .waitpid 2103 _, .waited (.exited 2103 42) =>
        match assocGet s.procs 2103 with
        | some e =>
          match e.lifecycle with
          | .alive a => if !a.pending.termSigs.isEmpty then none else allowedStep s req out
          | _ => allowedStep s req out
        | none => none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_model_allowedStep_stopRaceAndQueuedSigcont
    (fun s req out =>
      match req, out with
      | .waitpid 2100 flags, .waited (.stopped 2100 20) =>
        if flags.nohang && flags.untraced then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_ambientSigchldAutoreapAndIgnoredSigs
    { modelOps with
      waitpid := fun pid flags => do
        let s ← get
        let (res, s') := evalModelWaitpid { s with sigchld := .default } pid flags
        set s'
        return res }) := by
  intro h
  exact absurd h.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_ambientSigchldAutoreapAndIgnoredSigs
    { modelOps with
      waitpid := fun pid flags => do
        let s ← get
        match evalModelWaitpid s pid flags with
        | (.ok w, s') => set s'; return .ok w
        | (.error e, _) => return .error e }) := by
  intro h
  exact absurd h.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_ambientSigchldAutoreapAndIgnoredSigs
    { modelOps with
      kill := fun pid sig => do
        let s ← get
        match evalKill { s with ambientIgnoredSigs := [] } pid sig with
        | .ok s' => set s'; return .ok ()
        | .error e => return .error e }) := by
  intro h
  exact absurd h.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_model_allowedStep_sigchldAutoreapPrecision
    (fun s req out =>
      match req, out with
      | .pidfd_open 1000 _, .err code =>
        if s.sigchld == .autoreap && code == Errno.ESRCH then some s else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.1 (by decide)

example : ¬ Core.AllPass (test_process_model_allowedStep_sigchldAutoreapPrecision
    (fun s req out =>
      match req, out with
      | .waitpid 2211 _flags, .waited (.exited 2211 0) =>
        some (reapThreadGroup s 2211)
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_model_allowedStep_sigchldAutoreapPrecision
    (fun s req out =>
      match req, out with
      | .kill 2211 .sigzero, .err code =>
        if code == Errno.ESRCH then some s else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_pidNamespaceUnkillableInitAndZeroPgid
    { modelOps with
      kill := fun pid sig => do
        let s ← get
        let procsNoInit := s.procs.map (fun (k, e) => (k, match e.role with | .foreign _ => { e with role := .foreign false } | _ => e))
        match evalKill { s with procs := procsNoInit } pid sig with
        | .ok s' => set s'; return .ok ()
        | .error e => return .error e }) := by
  intro h
  exact absurd h.1.2 (by decide)

example : ¬ Core.AllPass (test_process_ops_pidNamespaceUnkillableInitAndZeroPgid
    { modelOps with
      pidfd_send_signal := fun hid sig flags => do
        let s ← get
        let procsNoInit := s.procs.map (fun (k, e) => (k, match e.role with | .foreign _ => { e with role := .foreign false } | _ => e))
        match evalPidfdSendSignal { s with procs := procsNoInit } hid sig flags with
        | .ok s' => set s'; return .ok ()
        | .error e => return .error e }) := by
  intro h
  exact absurd h.2.2.1.2 (by decide)

example : ¬ Core.AllPass (test_process_ops_pidNamespaceUnkillableInitAndZeroPgid
    { modelOps with
      pidfd_send_signal := fun hid sig flags => do
        let s ← get
        let sBad := if s.selfPgid == 0 then { s with selfPgid := effectiveSelfPid s } else s
        match evalPidfdSendSignal sBad hid sig flags with
        | .ok s' => set s'; return .ok ()
        | .error e => return .error e }) := by
  intro h
  exact absurd h.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_model_allowedStep_openHostPidsAndAmbientSeccomp
    (fun s req out => allowedStep { s with closedPidNamespace := true } req out)) := by
  intro h
  exact absurd h.1 (by decide)

example : ¬ Core.AllPass (test_process_model_allowedStep_openHostPidsAndAmbientSeccomp
    (fun s req out =>
      match req, out with
      | .kill 2 .sigzero, .err code =>
        if code == Errno.EACCES then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_model_allowedStep_openHostPidsAndAmbientSeccomp
    (fun s req out => allowedStep { s with ambientSeccomp := false } req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_model_allowedStep_openHostPidsAndAmbientSeccomp
    (fun s req out =>
      match req, out with
      | .pipe2 _, .err code =>
        if s.ambientSeccomp && code == Errno.EFAULT then some s else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_model_modelOpsSoundForAllowedStep
    { modelOps with
      pipe2 := fun _ => pure (.ok (0, 0)) }
    allowedStep) := by
  intro h
  have h0 := h ProcessSysState.initial (.pipe2 {})
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_process_model_modelOpsSoundForAllowedStep
    { modelOps with
      waitpid := fun pid flags =>
        if pid == Int32.minValue && flags.isValid then pure (.error Errno.EINVAL)
        else modelOps.waitpid pid flags }
    allowedStep) := by
  intro h
  have h0 := h ProcessSysState.initial (.waitpid Int32.minValue {})
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_process_impl_mkProcessOpsSound
    (fun raw =>
      { baseMkOps raw with
        kill := fun pid sig =>
          if sig.isNptlReserved then pure (.error Errno.EPERM)
          else (baseMkOps raw).kill pid sig })) := by
  intro h
  have hKill := h.2.2.2.1 (m := StateM Nat) (fd := Nat)
    (PosixProcessOpsM.mk
      (fun _ => pure (.ok (0, 0)))
      (fun _ _ => pure (.error Errno.ECHILD))
      (fun _ _ _ => pure (.error Errno.ESRCH))
      (fun _ _ => pure (.error Errno.ESRCH))
      (fun _ _ _ _ => pure (.error Errno.EBADF))
      (pure (.ok 1000))
      (pure (.ok 1000)))
    0 (.raw 32)
  have hres := congrArg (fun f => (f 0).1) hKill
  cases hres

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .waitpid 2000 _, .waited (.exited 2000 42) => some s
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .kill 2001 .sigzero, .err code =>
        if code == Errno.ESRCH then some s else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .waitpid 2010 _, .waited (.stopped 2010 20) => none
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .kill 2041 .sigzero, .err code =>
        if code == Errno.ESRCH then some s else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .waitpid 2000 flags, .waited (.continued 2000) =>
        if flags.continued then some s else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .kill 3 .sigzero, .err code =>
        if code == Errno.ESRCH then some s else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .waitpid 2050 flags, .waited .stillRunning =>
        if flags.continued then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .waitpid 2010 flags, .waited (.continued 2010) =>
        if flags.continued then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .kill p .sigzero, .err _ =>
        if p == Int32.minValue then some { s with procs := [] } else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad.2.2 (by decide)

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .waitpid 2056 _, .waited (.signaled 2056 15 false) => some s
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .pidfd_open 2031 flags, .opened _ =>
        if flags.thread then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .waitpid 2070 _, .err e =>
        if e == Errno.ECHILD then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .waitpid 2074 _, .waited (.exited 2074 99) => none
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .waitpid 2080 flags, .waited (.stopped 2080 20) =>
        if flags.untraced then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .waitpid (-1) flags, .waited .stillRunning =>
        if flags.continued then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .waitpid 2095 _, .waited (.exited 2095 77) => none
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    modelOps
    (fun s req out =>
      match req, out with
      | .waitpid 2074 _, .waited (.signaled 2074 15 false) => some s
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_interface_defaultOpsWiring
    baseMkOps
    { refIoProcOps with kill := fun _ _ => pure (.error Errno.EPERM) }
    refIoProcOps.pipe2 (refIoProcOps.pipe2 {})
    refIoProcOps.waitpid (fun pid => refIoProcOps.waitpid pid {})
    refIoProcOps.kill
    refIoProcOps.pidfd_open (fun pid => refIoProcOps.pidfd_open pid {})
    refIoProcOps.pidfd_send_signal (fun fd sig => refIoProcOps.pidfd_send_signal fd sig {})
    refIoProcOps.getpid refIoProcOps.getuid) := by
  intro h
  rcases h with ⟨⟨raw, hmk⟩, _⟩
  have hk := congrArg (fun o => o.kill 0 (.raw 32)) hmk
  exact (inferInstance : Nonempty (Void IO.RealWorld)).elim fun w => by
    have hw := congrFun hk w
    cases hw

example : ¬ Core.AllPass (test_process_interface_defaultOpsWiring
    baseMkOps
    { refIoProcOps with
      pidfd_send_signal := fun _ _ flags =>
        if flags == {} then pure (.error Errno.EPERM) else pure (.error Errno.EINVAL) }
    refIoProcOps.pipe2 (refIoProcOps.pipe2 {})
    refIoProcOps.waitpid (fun pid => refIoProcOps.waitpid pid {})
    refIoProcOps.kill
    refIoProcOps.pidfd_open (fun pid => refIoProcOps.pidfd_open pid {})
    refIoProcOps.pidfd_send_signal (fun fd sig => refIoProcOps.pidfd_send_signal fd sig {})
    refIoProcOps.getpid refIoProcOps.getuid) := by
  intro h
  rcases h with ⟨⟨raw, hmk⟩, _⟩
  exact (inferInstance : Nonempty RawFd).elim fun fd =>
    (inferInstance : Nonempty (Void IO.RealWorld)).elim fun w => by
      have hk := congrArg (fun o => o.pidfd_send_signal fd (.raw 32) {}) hmk
      have hw := congrFun hk w
      cases hw

example : ¬ Core.AllPass (test_process_model_subthreadGroupExitCloneFlagsSigcontAndWatchQueue
    modelOps
    (fun s req out =>
      match req, out with
      | .kill 2051 .sigzero, .err e =>
        if e == Errno.ESRCH then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_subthreadGroupExitCloneFlagsSigcontAndWatchQueue
    { modelOps with
      waitpid := fun pid flags =>
        if pid == 2100 && !flags.nohang then pure (.error Errno.EINTR)
        else modelOps.waitpid pid flags }
    allowedStep) := by
  intro h
  rcases h with ⟨_, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_subthreadGroupExitCloneFlagsSigcontAndWatchQueue
    { modelOps with
      waitpid := fun pid flags =>
        if pid == 2401 && !flags.wclone && !flags.wall then pure (.ok (.exited 2401 20))
        else modelOps.waitpid pid flags }
    allowedStep) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨hbad, _⟩, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_subthreadGroupExitCloneFlagsSigcontAndWatchQueue
    { modelOps with
      kill := fun pid sig =>
        if pid == 2500 && sig == .sigcont then pure (.error Errno.EPERM)
        else modelOps.kill pid sig }
    allowedStep) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨hbad, _⟩, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_subthreadGroupExitCloneFlagsSigcontAndWatchQueue
    { modelOps with
      pipe2 := fun flags =>
        if flags.notificationPipe then pure (.error Errno.EPERM)
        else modelOps.pipe2 flags }
    allowedStep) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨hbad, _⟩, _⟩
  exact absurd hbad (by decide)

example : ¬ Core.AllPass (test_process_model_subthreadGroupExitCloneFlagsSigcontAndWatchQueue
    modelOps
    (fun s req out =>
      match req, out with
      | .waitpid 2600 _, .waited (.signaled 2600 15 true) => some s
      | _, _ => allowedStep s req out)) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbad, _⟩
  exact absurd hbad (by decide)

end LeanSwe.LinuxSyscall.Process
