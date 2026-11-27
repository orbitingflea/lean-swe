import LeanSwe.LinuxSyscall.Process.SpecTests

namespace LeanSwe.LinuxSyscall.Process

open Core (NondetTest AllPass)
open Core.NondetTest

private theorem some_eq_getD {α : Type} [Inhabited α] {o : Option α} {x : α} (h : o = some x) :
    x = o.getD default := by
  cases h; rfl

private theorem run_pipe2_ok (s : ProcessSysState) (flags : PipeFlags) (hval : flags.isValid = true)
    (hwatch : (flags.notificationPipe && !s.watchQueueSupported) = false) :
    StateT.run (modelOps.pipe2 flags) s =
      let rHid := nextFreeHid s.fds s.nextHid
      (.ok (rHid, rHid + 1), commitPipeFds s rHid (rHid + 1) flags) := by
  have hwatch' : ¬(flags.notificationPipe = true ∧ s.watchQueueSupported = false) := by
    simpa using hwatch
  simp [modelOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
    pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind, hval, hwatch']

private theorem run_pidfd_open_ok (s : ProcessSysState) (pid : UInt32) (flags : PidfdOpenFlags)
    (hok : checkPidfdOpenTarget s pid flags = .ok ()) :
    StateT.run (modelOps.pidfd_open pid flags) s =
      let hid := nextFreeHid s.fds s.nextHid
      (.ok hid, commitPidfd s hid pid flags.nonblock flags.thread) := by
  simp [modelOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
    pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind, hok]

private theorem run_kill_ok (s s' : ProcessSysState) (pid : Int32) (sig : Signal)
    (hpre : validateReqBeforeKernel s (.kill pid sig) = none)
    (hok : evalKill s pid sig = .ok s') :
    StateT.run (modelOps.kill pid sig) s = (.ok (), s') := by
  dsimp only [modelOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
    pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]
  rw [hpre]
  dsimp only
  rw [hok]
  rfl

private theorem run_kill_err (s : ProcessSysState) (pid : Int32) (sig : Signal) (e : Errno)
    (hpre : validateReqBeforeKernel s (.kill pid sig) = none)
    (herr : evalKill s pid sig = .error e)
    (hesrch : (if e == Errno.ESRCH then esrchKillNext s pid else s) = s) :
    StateT.run (modelOps.kill pid sig) s = (.error e, s) := by
  dsimp only [modelOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
    set, StateT.set, pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]
  rw [hpre]
  dsimp only
  rw [herr]
  dsimp only
  rw [hesrch]
  rfl

private theorem run_pidfd_send_signal_ok (s s' : ProcessSysState) (hid : HandleId) (sig : Signal)
    (flags : PidfdSignalFlags)
    (hpre : validateReqBeforeKernel s (.pidfd_send_signal hid sig flags) = none)
    (hok : evalPidfdSendSignal s hid sig flags = .ok s') :
    StateT.run (modelOps.pidfd_send_signal hid sig flags) s = (.ok (), s') := by
  dsimp only [modelOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
    pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]
  rw [hpre]
  dsimp only
  rw [hok]
  rfl

private theorem run_pidfd_send_signal_err (s : ProcessSysState) (hid : HandleId) (sig : Signal)
    (flags : PidfdSignalFlags) (e : Errno)
    (hpre : validateReqBeforeKernel s (.pidfd_send_signal hid sig flags) = none)
    (herr : evalPidfdSendSignal s hid sig flags = .error e)
    (hesrch : (if e == Errno.ESRCH then esrchPidfdSendNext s hid flags else s) = s) :
    StateT.run (modelOps.pidfd_send_signal hid sig flags) s = (.error e, s) := by
  dsimp only [modelOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
    set, StateT.set, pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]
  rw [hpre]
  dsimp only
  rw [herr]
  dsimp only
  rw [hesrch]
  rfl

/-- `waitpid` validates option flags before `INT32_MIN`, handles `WNOHANG`/blocking, and reaps exited zombies. -/
theorem process_ops_waitpid_optionsWnohangAndExitedReap_allPass :
    AllPass (test_process_ops_waitpid_optionsWnohangAndExitedReap modelOps) := by
  dsimp only [AllPass, test_process_ops_waitpid_optionsWnohangAndExitedReap, Bind.bind, Pure.pure, assert]
  repeat (first | exact trivial | exact rfl | apply And.intro)

/-- `waitpid` reports `WUNTRACED` stops, `WCONTINUED` wakes, and reaps `SIGKILL`-killed children. -/
theorem process_ops_waitpid_stopContinueAndSignaledReap_allPass :
    AllPass (test_process_ops_waitpid_stopContinueAndSignaledReap modelOps) := by
  dsimp only [AllPass, test_process_ops_waitpid_stopContinueAndSignaledReap, Bind.bind, Pure.pure, assert]
  repeat (first | exact trivial | exact rfl | apply And.intro)

/-- Non-`SIGKILL` fatal signals sent to stopped children remain queued until `SIGCONT`. -/
theorem process_ops_waitpid_queuedFatalAcrossSigcont_allPass :
    AllPass (test_process_ops_waitpid_queuedFatalAcrossSigcont modelOps) := by
  dsimp only [AllPass, test_process_ops_waitpid_queuedFatalAcrossSigcont, Bind.bind, Pure.pure, assert]
  repeat (first | exact trivial | exact rfl | apply And.intro)

/-- `kill` enforces error precedence, `-pgid` `EPERM` vs `kill(-1)` unowned ignore, `ESRCH` when alone, and ignores `{17, 23, 28}`. -/
theorem process_ops_kill_precedencePermissionsAndIgnoredSignals_allPass :
    AllPass (test_process_ops_kill_precedencePermissionsAndIgnoredSignals modelOps) := by
  dsimp only [AllPass, test_process_ops_kill_precedencePermissionsAndIgnoredSignals, Bind.bind, Pure.pure, assert]
  repeat (first | exact trivial | exact rfl | apply And.intro)

/-- `kill` supports side-effect-free `SIGZERO`, zombie stability, post-reap `ESRCH`, and `-pgid` delivery. -/
theorem process_ops_kill_sigzeroZombieAndProcessGroup_allPass :
    AllPass (test_process_ops_kill_sigzeroZombieAndProcessGroup modelOps) := by
  dsimp only [AllPass, test_process_ops_kill_sigzeroZombieAndProcessGroup, Bind.bind, Pure.pure, assert]
  repeat (first | exact trivial | exact rfl | apply And.intro)

/-- Non-leader thread `kill` routes to `tgid` and reaping the leader reaps its threads. -/
theorem process_ops_kill_nonLeaderThreadRoutesToTgidAndReaps_allPass :
    AllPass (test_process_ops_kill_nonLeaderThreadRoutesToTgidAndReaps modelOps) := by
  dsimp only [AllPass, test_process_ops_kill_nonLeaderThreadRoutesToTgidAndReaps, Bind.bind, Pure.pure, assert]
  repeat (first | exact trivial | exact rfl | apply And.intro)

/-- `pidfd_open` validates flags, checks non-positive PIDs, rejects non-leader threads (`ENOENT`), and opens leaders/zombies. -/
theorem process_ops_pidfdOpen_validationThreadAndZombie_allPass :
    AllPass (test_process_ops_pidfdOpen_validationThreadAndZombie modelOps) := by
  dsimp only [AllPass, test_process_ops_pidfdOpen_validationThreadAndZombie, Bind.bind, Pure.pure, assert]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rw [run_pidfd_open_ok _ 1 {} rfl]; dsimp only
  rw [run_pidfd_open_ok _ 3002 { nonblock := true } rfl]; dsimp only
  rw [run_pidfd_open_ok _ 3001 {} rfl]; dsimp only
  exact ⟨by decide, trivial⟩

/-- `pidfd_send_signal` enforces unallocated/closed `EBADF` and non-pidfd `EINVAL`/`EBADF` precedence. -/
theorem process_ops_pidfdSendSignal_fdKindsAndFlags_allPass :
    AllPass (test_process_ops_pidfdSendSignal_fdKindsAndFlags modelOps) := by
  dsimp only [AllPass, test_process_ops_pidfdSendSignal_fdKindsAndFlags, Bind.bind, Pure.pure, assert]
  refine ⟨rfl, ?_⟩
  rw [run_pipe2_ok _ {} rfl rfl]; dsimp only
  exact ⟨rfl, rfl, rfl, trivial⟩

/-- `pidfd_send_signal` enforces permissions, empty-PGID `ESRCH`, and post-reap `ESRCH` vs `EINVAL`. -/
theorem process_ops_pidfdSendSignal_permissionsAndPostReap_allPass :
    AllPass (test_process_ops_pidfdSendSignal_permissionsAndPostReap modelOps) := by
  dsimp only [AllPass, test_process_ops_pidfdSendSignal_permissionsAndPostReap, Bind.bind, Pure.pure, assert]
  rw [run_pidfd_open_ok _ 1 {} rfl]; dsimp only
  rw [run_pidfd_open_ok _ 3002 { nonblock := true } rfl]; dsimp only
  rw [run_pidfd_open_ok _ 3001 {} rfl]; dsimp only
  repeat (first | exact trivial | exact rfl | apply And.intro | exact (by decide))

/-- `pidfd_send_signal` with `PIDFD_SIGNAL_PROCESS_GROUP` follows `PIDTYPE_PGID` even after leader reap or move. -/
theorem process_ops_pidfdSendSignal_processGroupAfterLeaderReapOrMove_allPass :
    AllPass (test_process_ops_pidfdSendSignal_processGroupAfterLeaderReapOrMove modelOps) := by
  dsimp only [AllPass, test_process_ops_pidfdSendSignal_processGroupAfterLeaderReapOrMove, Bind.bind, Pure.pure, assert]
  rw [run_pidfd_open_ok _ 3010 {} rfl]; dsimp only
  rw [run_pidfd_open_ok _ 3020 {} rfl]; dsimp only
  repeat (first | exact trivial | exact rfl | apply And.intro | exact (by decide))

/-- `allowedStep` enforces invariants, `selfPid`/`selfUid`, controlled vs autonomous exits, and double-reap rejection. -/
theorem process_model_allowedStep_invariantsAndRejections_allPass :
    AllPass (test_process_model_allowedStep_invariantsAndRejections allowedStep) := by
  dsimp only [AllPass, test_process_model_allowedStep_invariantsAndRejections, Bind.bind, Pure.pure, assert]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  cases h : allowedStep ((ProcessSysState.initial 1000 1000 500 |>.registerNonLeaderThread 1001 1000).spawnAutonomousChild 2060 2060) (.waitpid 2060 { nohang := false }) (.waited (.exited 2060 0)) with
  | none => exact absurd h (by decide)
  | some sReaped =>
    have hs := some_eq_getD h; clear h; subst hs
    dsimp only
    exact ⟨by decide, by decide, trivial⟩

private def optBool {α : Type} (o : Option α) (b : α → Bool) : Bool :=
  match o with | none => false | some x => b x

/-- `allowedStep` permits stop races, queued fatal signals across `SIGCONT`, and `altStopSigs` preservation. -/
theorem process_model_allowedStep_stopRaceAndQueuedSigcont_allPass :
    AllPass (test_process_model_allowedStep_stopRaceAndQueuedSigcont allowedStep) := by
  dsimp only [AllPass, test_process_model_allowedStep_stopRaceAndQueuedSigcont, Bind.bind, Pure.pure, assert]
  let sBase := (ProcessSysState.initial 1000 1000 1000).spawnRunningChild 2100 2100
  let bChain : Bool :=
    optBool (allowedStep sBase (.kill 2100 .sigstop) .unit) fun sStopAsync =>
      (allowedStep sStopAsync (.waitpid 2100 { nohang := true, untraced := true }) (.waited .stillRunning)).isSome &&
      optBool (allowedStep sStopAsync (.waitpid 2100 { nohang := true, untraced := true }) (.waited (.stopped 2100 19))) fun sStopConfirmed =>
        optBool (allowedStep sStopConfirmed (.kill 2100 .sigterm) .unit) fun sQueued =>
          (allowedStep sQueued (.waitpid 2100 { nohang := true }) (.waited (.signaled 2100 15 false))).isNone &&
          optBool (allowedStep sQueued (.kill 2100 .sigcont) .unit) fun sWoken =>
            (allowedStep sWoken (.waitpid 2100 { nohang := true }) (.waited (.signaled 2100 15 false))).isSome &&
            (allowedStep sWoken (.waitpid 2100 { nohang := false }) (.waited (.signaled 2100 15 false))).isSome &&
            optBool (allowedStep sWoken (.waitpid 2100 { nohang := true, continued := true }) (.waited (.continued 2100))) fun sAfterContRace =>
              (allowedStep sAfterContRace (.waitpid 2100 { nohang := false }) (.waited (.signaled 2100 15 false))).isSome
  let bTstp : Bool :=
    optBool (allowedStep sBase (.kill 2100 (.raw 20)) .unit) fun sTstp =>
      optBool (allowedStep sTstp (.kill 2100 .sigstop) .unit) (fun sTstpThenStop =>
        (allowedStep sTstpThenStop (.waitpid 2100 { nohang := true, untraced := true }) (.waited (.stopped 2100 20))).isSome &&
        (allowedStep sTstpThenStop (.waitpid 2100 { nohang := true, untraced := true }) (.waited (.stopped 2100 19))).isSome) &&
      optBool (allowedStep sTstp (.kill 2100 .sigterm) .unit) fun sTstpTerm =>
        (allowedStep sTstpTerm (.waitpid 2100 { nohang := true }) (.waited (.signaled 2100 15 false))).isSome &&
        (allowedStep sTstpTerm (.waitpid 2100 { nohang := true }) (.waited .stillRunning)).isSome
  have hChain : bChain = true := by decide
  have hTstp : bTstp = true := by decide
  dsimp only [bChain, sBase] at hChain
  dsimp only [bTstp, sBase] at hTstp
  cases h1 : allowedStep _ (.kill 2100 .sigstop) .unit with
  | none => rw [h1] at hChain; cases hChain
  | some sStopAsync =>
    rw [h1] at hChain; dsimp only [optBool] at hChain
    rw [Bool.and_eq_true] at hChain
    dsimp only
    refine ⟨hChain.1, ?_⟩
    have hc2 := hChain.2
    cases h2 : allowedStep sStopAsync (.waitpid 2100 { nohang := true, untraced := true }) (.waited (.stopped 2100 19)) with
    | none => rw [h2] at hc2; cases hc2
    | some sStopConfirmed =>
      rw [h2] at hc2; dsimp only [optBool] at hc2
      dsimp only
      cases h3 : allowedStep sStopConfirmed (.kill 2100 .sigterm) .unit with
      | none => rw [h3] at hc2; cases hc2
      | some sQueued =>
        rw [h3] at hc2; dsimp only [optBool] at hc2
        rw [Bool.and_eq_true] at hc2
        dsimp only
        refine ⟨hc2.1, ?_⟩
        have hc4 := hc2.2
        cases h4 : allowedStep sQueued (.kill 2100 .sigcont) .unit with
        | none => rw [h4] at hc4; cases hc4
        | some sWoken =>
          rw [h4] at hc4; dsimp only [optBool] at hc4
          rw [Bool.and_eq_true, Bool.and_eq_true] at hc4
          dsimp only
          refine ⟨hc4.1.1, hc4.1.2, ?_⟩
          have hc5 := hc4.2
          cases h5 : allowedStep sWoken (.waitpid 2100 { nohang := true, continued := true }) (.waited (.continued 2100)) with
          | none => rw [h5] at hc5; cases hc5
          | some sAfterContRace =>
            rw [h5] at hc5; dsimp only [optBool] at hc5
            dsimp only
            refine ⟨hc5, by decide, ?_⟩
            cases h6 : allowedStep _ (.kill 2100 (.raw 20)) .unit with
            | none => rw [h6] at hTstp; cases hTstp
            | some sTstp =>
              rw [h6] at hTstp; dsimp only [optBool] at hTstp
              rw [Bool.and_eq_true] at hTstp
              dsimp only
              have ht1 := hTstp.1
              have ht2 := hTstp.2
              cases h7 : allowedStep sTstp (.kill 2100 .sigstop) .unit with
              | none => rw [h7] at ht1; cases ht1
              | some sTstpThenStop =>
                rw [h7] at ht1; dsimp only [optBool] at ht1
                rw [Bool.and_eq_true] at ht1
                dsimp only
                refine ⟨ht1.1, ht1.2, ?_⟩
                cases h8 : allowedStep sTstp (.kill 2100 .sigterm) .unit with
                | none => rw [h8] at ht2; cases ht2
                | some sTstpTerm =>
                  rw [h8] at ht2; dsimp only [optBool] at ht2
                  rw [Bool.and_eq_true] at ht2
                  exact ⟨ht2.1, ht2.2, trivial⟩

/-- `allowedStep` captures core-dump ambiguity, racing fatal signals, and preserved `autoExit?` outcomes. -/
theorem process_model_allowedStep_coreDumpAndRacingSignals_allPass :
    AllPass (test_process_model_allowedStep_coreDumpAndRacingSignals allowedStep) := by
  dsimp only [AllPass, test_process_model_allowedStep_coreDumpAndRacingSignals, Bind.bind, Pure.pure, assert]
  let sBase := (ProcessSysState.initial 1000 1000 1000).spawnRunningChild 2100 2100
  let sPlanned := (ProcessSysState.initial 1000 1000 1000).spawnRunningChild 2103 2103 (some (.exited 42))
  cases h1 : allowedStep sBase (.kill 2100 (.raw 6)) .unit with
  | none => exact absurd h1 (by decide)
  | some sAbrt =>
    have hs1 := some_eq_getD h1; clear h1; subst hs1
    dsimp only
    refine ⟨by decide, by decide, ?_⟩
    cases h2 : allowedStep sBase (.kill 2100 .sigterm) .unit with
    | none => exact absurd h2 (by decide)
    | some sTerm1 =>
      have hs2 := some_eq_getD h2; clear h2; subst hs2
      dsimp only
      cases h3 : allowedStep _ (.kill 2100 .sigkill) .unit with
      | none => exact absurd h3 (by decide)
      | some sTermAndKill =>
        have hs3 := some_eq_getD h3; clear h3; subst hs3
        dsimp only
        refine ⟨by decide, by decide, by decide, rfl, rfl, rfl, rfl, ?_⟩
        cases h4 : allowedStep sPlanned (.kill 2103 .sigterm) .unit with
        | none => exact absurd h4 (by decide)
        | some sPlannedRaced =>
          have hs4 := some_eq_getD h4; clear h4; subst hs4
          exact ⟨by decide, by decide, by decide, trivial⟩

/-- Concrete regression proof for `.delayedZombie`, thread-scoped `pidfd_send_signal`, orphaned `SIGTSTP`, `PIDFD_THREAD`, and `esrch*Next`. -/
theorem process_model_delayedZombieThreadScopeOrphanAndExitDead_allPass :
    AllPass (test_process_model_delayedZombieThreadScopeOrphanAndExitDead modelOps allowedStep) := by
  dsimp only [AllPass, test_process_model_delayedZombieThreadScopeOrphanAndExitDead, Bind.bind, Pure.pure, assert]
  repeat (first | exact trivial | exact rfl | exact (by decide) | apply And.intro)

/-- Concrete regression proof for subthread group-exit parity, confirmed-stop queued fatal wake, shadowed-PID pruning, `wait4` clone/thread flags, `SIGCONT` same-session `EPERM` bypass, `O_NOTIFICATION_PIPE`, core-dump signals, and `SIGTTIN`/`SIGTTOU`. -/
theorem process_model_subthreadGroupExitCloneFlagsSigcontAndWatchQueue_allPass :
    AllPass (test_process_model_subthreadGroupExitCloneFlagsSigcontAndWatchQueue modelOps allowedStep) := by
  dsimp only [AllPass, test_process_model_subthreadGroupExitCloneFlagsSigcontAndWatchQueue, Bind.bind, Pure.pure, assert]
  repeat (first | exact trivial | exact rfl | exact (by decide) | apply And.intro)

/-- Ambient `sigchldAutoreap` and `ambientIgnoredSigs` preserve stops while auto-reaping terminated children. -/
theorem process_ops_ambientSigchldAutoreapAndIgnoredSigs_allPass :
    AllPass (test_process_ops_ambientSigchldAutoreapAndIgnoredSigs modelOps) := by
  dsimp only [AllPass, test_process_ops_ambientSigchldAutoreapAndIgnoredSigs, Bind.bind, Pure.pure, assert]
  repeat (first | exact trivial | exact rfl | apply And.intro)

/-- Under `sigchldAutoreap`, `allowedStep` rejects non-seeded exits and reaps auto-reapable children cleanly. -/
theorem process_model_allowedStep_sigchldAutoreapPrecision_allPass :
    AllPass (test_process_model_allowedStep_sigchldAutoreapPrecision allowedStep) := by
  dsimp only [AllPass, test_process_model_allowedStep_sigchldAutoreapPrecision, Bind.bind, Pure.pure, assert]
  let s0 := (((ProcessSysState.initial 1000 1000 1000).withSigchldAutoreap true)
    |>.spawnRunningChild 2210 2210)
    |>.spawnAutonomousChild 2211 2211
    |>.spawnZombieExited 2212 5 2212
  cases h1 : allowedStep s0 (.pidfd_open 1000 {}) (.opened 0) with
  | none => exact absurd h1 (by decide)
  | some sWithSelfPfd =>
    have hs1 := some_eq_getD h1; clear h1; subst hs1
    dsimp only
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
    cases h2 : allowedStep _ (.kill 2211 .sigzero) (.err Errno.ESRCH) with
    | none => exact absurd h2 (by decide)
    | some sAfterEsrch =>
      have hs2 := some_eq_getD h2; clear h2; subst hs2
      dsimp only
      refine ⟨by decide, by decide, by decide, by decide, ?_⟩
      let sToggleBack := (((ProcessSysState.initial 1000 1000 1000).withSigchldAutoreap true).spawnRunningChild 2214 2214).withSigchldAutoreap false
      cases h3 : allowedStep sToggleBack (.kill 2214 .sigkill) .unit with
      | none => exact absurd h3 (by decide)
      | some sToggleKilled =>
        have hs3 := some_eq_getD h3; clear h3; subst hs3
        exact ⟨by decide, by decide, by decide, trivial⟩

/-- Namespace `PID 1` ignores uncaught `SIGKILL`/`SIGSTOP` and pre-`setsid()` `selfPgid = 0` behaves faithfully. -/
theorem process_ops_pidNamespaceUnkillableInitAndZeroPgid_allPass :
    AllPass (test_process_ops_pidNamespaceUnkillableInitAndZeroPgid modelOps) := by
  dsimp only [AllPass, test_process_ops_pidNamespaceUnkillableInitAndZeroPgid, Bind.bind, Pure.pure, assert]
  rw [run_kill_ok _ _ 1 .sigkill rfl rfl]; dsimp only
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  rw [run_kill_ok _ _ 1 .sigstop rfl rfl]; dsimp only
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  rw [run_pidfd_open_ok _ 1 {} rfl]; dsimp only
  rw [run_pidfd_send_signal_ok _ _ _ .sigkill {} rfl rfl]; dsimp only
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  rw [run_kill_ok _ _ 1 .sigzero rfl rfl]; dsimp only
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  rw [run_kill_ok _ _ 0 .sigzero rfl rfl]; dsimp only
  refine ⟨rfl, ?_⟩
  rw [run_pidfd_open_ok _ 1 {} rfl]; dsimp only
  rw [run_pidfd_send_signal_err _ _ .sigzero { processGroup := true } Errno.ESRCH rfl rfl rfl]; dsimp only
  refine ⟨rfl, ?_⟩
  exact ⟨rfl, trivial⟩

/-- On shared open hosts and under ambient `seccomp`, `allowedStep` permits valid host/seccomp outcomes only. -/
theorem process_model_allowedStep_openHostPidsAndAmbientSeccomp_allPass :
    AllPass (test_process_model_allowedStep_openHostPidsAndAmbientSeccomp allowedStep) := by
  dsimp only [AllPass, test_process_model_allowedStep_openHostPidsAndAmbientSeccomp, Bind.bind, Pure.pure, assert]
  let sHost := (ProcessSysState.initial 1000 1000 1000).withOpenHostPids true
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  cases h1 : allowedStep sHost (.pidfd_open 2 {}) (.opened 0) with
  | none => exact absurd h1 (by decide)
  | some sHostWithPfd2 =>
    have hs1 := some_eq_getD h1; clear h1; subst hs1
    dsimp only
    refine ⟨by decide, by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      by decide, by decide, rfl, rfl, ?_⟩
    let sKillStop := (ProcessSysState.initial 1000 1000 1000).spawnRunningChild 2300 2300
    cases h2 : allowedStep sKillStop (.kill 2300 .sigkill) .unit with
    | none => exact absurd h2 (by decide)
    | some sK9 =>
      have hs2 := some_eq_getD h2; clear h2; subst hs2
      cases h3 : allowedStep ((allowedStep sKillStop (.kill 2300 .sigkill) .unit).getD default) (.kill 2300 .sigstop) .unit with
      | none => exact absurd h3 (by decide)
      | some sK9Stop =>
        have hs3 := some_eq_getD h3; clear h3; subst hs3
        dsimp only
        refine ⟨by decide, ?_⟩
        let sZCont := (ProcessSysState.initial 1000 1000 1000).spawnZombieSignaled 2301 6 false 2301
        cases h4 : allowedStep sZCont (.kill 2301 .sigcont) .unit with
        | none => exact absurd h4 (by decide)
        | some sZAfterCont =>
          have hs4 := some_eq_getD h4; clear h4; subst hs4
          exact ⟨by decide, trivial⟩

end LeanSwe.LinuxSyscall.Process
