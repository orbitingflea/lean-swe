import Std.Data.TreeSet
import LeanSwe.LinuxSyscall.Common.Model
import LeanSwe.LinuxSyscall.Process.Types

namespace LeanSwe.LinuxSyscall.Process

open LeanSwe.LinuxSyscall

export LeanSwe.LinuxSyscall (assocGet assocSetAux assocSet assocEraseAllAux assocEraseAll)

/-- Maximum valid positive 32-bit signed Linux `pid_t` (`INT32_MAX = 0x7fffffff`). -/
def maxLinuxPid : UInt32 := 0x7fffffff

/-- Normalize a signal number into the valid `wait4` `WTERMSIG`/`WSTOPSIG` range `1..126` (`9` fallback for malformed states). -/
def normalizeWaitSig (sig : UInt32) : UInt32 :=
  if 1 ≤ sig && sig ≤ 126 then sig else 9

/-- Returns `true` iff Linux signal `n` (`x86_64` and `aarch64`) has default disposition `Ign` (`17 = SIGCHLD`, `23 = SIGURG`, `28 = SIGWINCH`). -/
def isDefaultIgnoredSignal (n : Int) : Bool :=
  n == 17 || n == 23 || n == 28

/-- Returns `true` iff Linux signal `n` (`x86_64` and `aarch64`) has default disposition `Stop` (`19 = SIGSTOP`, `20 = SIGTSTP`, `21 = SIGTTIN`, `22 = SIGTTOU`). -/
def isStopSignal (n : Int) : Bool :=
  n == 19 || n == 20 || n == 21 || n == 22

/-- Returns `true` iff Linux signal `sig` has default disposition `Core` (`3, 4, 5, 6, 7, 8, 11, 24, 25, 31`). -/
def isCoreDefaultSignal (sig : UInt32) : Bool :=
  sig == 3 || sig == 4 || sig == 5 || sig == 6 || sig == 7 ||
  sig == 8 || sig == 11 || sig == 24 || sig == 25 || sig == 31

/-- Returns `true` iff `e` can be synthesized by an installed safe `seccomp` `SECCOMP_RET_ERRNO` filter (`1 <= e <= 4095` and `e != Errno.EFAULT`). -/
def isSeccompSynthesizableErrno (e : Errno) : Bool :=
  e != Errno.EFAULT && 1 ≤ e.toNat && e.toNat ≤ 4095

/-- Non-FD-allocating kernel transient errnos (`EINTR`, `ENOMEM`, `EIO`, `ENOSPC`). -/
def isKernelNonFdTransient (e : Errno) : Bool :=
  e == Errno.EINTR || e == Errno.ENOMEM || e == Errno.EIO || e == Errno.ENOSPC

/-- FD-allocating kernel transient errnos (`EINTR`, `EIO`, `ENOMEM`, `ENFILE`, `EMFILE`, `ENOSPC`). -/
def isKernelFdAllocTransient (e : Errno) : Bool :=
  e.isTransientOsErrno

/-- Terminal exit or signal status stored by a child prior to reaping via `waitpid`. -/
inductive ZombieStatus where
  /-- Terminated normally via `_exit(exitCode)` (`WIFEXITED`). -/
  | exited (exitCode : UInt8)
  /-- Terminated by signal `termSignal` (`WIFSIGNALED`, `1 <= termSignal <= 126`). -/
  | signaled (termSignal : UInt32) (coreDumped : Bool := false)
  deriving Repr, DecidableEq

/-- Convert a `ZombieStatus` for child `pid` into its decoded `WaitResult`. -/
def ZombieStatus.toWaitResult (z : ZombieStatus) (pid : UInt32) : WaitResult :=
  match z with
  | .exited code => .exited pid code
  | .signaled sig core => .signaled pid (normalizeWaitSig sig) core

/-- Autonomous behavior of a live child's own code independent of external signals. -/
inductive AutoBehavior where
  /-- Controlled child (e.g. `pause()`): does not exit or stop on its own. -/
  | controlled
  /-- Child will exit on its own with exact `status` (e.g. `spawnAutonomous`). -/
  | planned (status : ZombieStatus)
  /-- Arbitrary autonomous child that may exit with any status or stop itself. -/
  | arbitrary
  deriving Repr, DecidableEq

/-- Reachable `exit_notify()` outcomes (`kernel/exit.c`) if an in-flight exit completes. -/
inductive ExitReapMode where
  /-- Non-autoreap `SIGCHLD` or non-`SIGCHLD` clone child: exit produces `EXIT_ZOMBIE`. -/
  | zombieOnly
  /-- `SIGCHLD` is `SIG_IGN`/`SA_NOCLDWAIT` on a `SIGCHLD` child: exit auto-reaps to `EXIT_DEAD`. -/
  | autoreapOnly
  /-- `SIGCHLD` toggled while exit was already possible: either `EXIT_ZOMBIE` or `EXIT_DEAD`. -/
  | either
  deriving Repr, DecidableEq

/-- Confirmed scheduling state of a live task. -/
inductive TaskRunState where
  /-- Running or runnable (`TASK_RUNNING` / sleeping). -/
  | running
  /-- Confirmed `TASK_STOPPED` by `stopSig` (`reported = true` once reported by `WUNTRACED`). -/
  | stopped (stopSig : UInt32) (reported : Bool := false)
  deriving Repr, DecidableEq

/-- `SIGNAL_STOP_CONTINUED` (`WCONTINUED`) observability state on a live task. -/
inductive ContState where
  /-- No unreported `SIGCONT` wake event. -/
  | none
  /-- `SIGCONT` raced an unconfirmed stop, or a stop raced a confirmed `SIGCONT`. -/
  | maybe
  /-- `SIGCONT` synchronously woke a confirmed `TASK_STOPPED` task (`WCONTINUED` ready). -/
  | confirmed
  deriving Repr, DecidableEq

/-- Queued asynchronous signals (`struct sigpending`) not yet confirmed delivered by `wait4`. -/
structure PendingSignals where
  /-- `SIGKILL` (`9`, `SIGNAL_GROUP_EXIT`) pending: wakes stops, blocks `do_signal_stop()`. -/
  killed : Bool := false
  /-- Non-`SIGKILL` fatal signals in `shared_pending` (held while `TASK_STOPPED` until `SIGCONT`). -/
  termSigs : List UInt32 := []
  /-- Pending stop signals (`19, 20, 21, 22`) in `shared_pending` (cleared by `SIGCONT`/`SIGKILL`). -/
  stopSigs : List UInt32 := []
  /-- TTY stop signals (`20, 21, 22`) queued while target was in an orphaned PGID (dropped unless moved out before dequeue). -/
  deferredTtyStops : List UInt32 := []
  /-- Deferred TTY stop signals promoted upon leaving an orphaned PGID (unconfirmed in deterministic `modelOps` `WUNTRACED`, but may stop or race `SIGCONT` in `allowedStep`). -/
  racedTtyStops : List UInt32 := []
  deriving Repr, DecidableEq

/-- Full state of a live task not yet confirmed `EXIT_ZOMBIE`, `EXIT_DEAD`, or `reaped`. -/
structure AliveState where
  /-- Confirmed run/stop scheduling state (`TASK_RUNNING` vs `TASK_STOPPED`). -/
  run : TaskRunState := .running
  /-- `SIGNAL_STOP_CONTINUED` observability state. -/
  cont : ContState := .none
  /-- Autonomous child exit behavior. -/
  auto : AutoBehavior := .controlled
  /-- Queued pending fatal and stop signals not yet confirmed delivered. -/
  pending : PendingSignals := {}
  /-- Reachable `exit_notify()` outcome (`EXIT_ZOMBIE` vs `EXIT_DEAD`). -/
  exitReap : ExitReapMode := .zombieOnly
  /-- True when a fatal signal arrived while running alongside a subthread able to trigger `do_group_exit`. -/
  subExitedRace : Bool := false
  deriving Repr, DecidableEq

/-- Return the first valid signal (`1 <= sig <= 126`) in `termSigs`, if any. -/
def firstValidTermSig? (termSigs : List UInt32) : Option UInt32 :=
  termSigs.find? (fun sig => 1 ≤ sig && sig ≤ 126)

/-- Returns `true` iff a live task currently has a deliverable group-fatal signal (`SIGKILL` or running `termSigs`). -/
def AliveState.canDeliverGroupFatal (a : AliveState) : Bool :=
  a.pending.killed || (a.run == .running && (firstValidTermSig? a.pending.termSigs).isSome)

/-- Returns `true` iff a live task can currently reach fatal exit without needing `SIGCONT`. -/
def AliveState.canDeliverFatal (a : AliveState) : Bool :=
  a.pending.killed ||
    (a.run == .running && (!a.pending.termSigs.isEmpty || a.auto != .controlled))

/-- Returns `true` iff a live task can produce a waitable `EXIT_ZOMBIE`. -/
def AliveState.mayZombie (a : AliveState) : Bool :=
  a.canDeliverFatal && a.exitReap != .autoreapOnly

/-- Returns `true` iff a live task can auto-reap to `EXIT_DEAD` / `reaped`. -/
def AliveState.mayAutoreap (a : AliveState) : Bool :=
  a.canDeliverFatal && a.exitReap != .zombieOnly

/-- Returns `true` iff live task `a` may exit normally with `code`. -/
def AliveState.allowsExited (a : AliveState) (code : UInt8) : Bool :=
  a.run == .running &&
    match a.auto with
    | .arbitrary => true
    | .planned (.exited c) => code == c
    | _ => false

/-- Returns `true` iff live task `a` may terminate with `(sig, core)` (`1 <= sig <= 126`). -/
def AliveState.allowsSignaled (a : AliveState) (sig : UInt32) (core : Bool) : Bool :=
  (a.pending.killed && sig == 9 && !core) ||
  (a.run == .running &&
    ((a.pending.termSigs.contains sig && (!core || isCoreDefaultSignal sig)) ||
     match a.auto with
     | .arbitrary => true
     | .planned (.signaled zs zc) => sig == normalizeWaitSig zs && core == zc
     | _ => false))

/-- Returns `true` iff live subthread `a` can autonomously trigger `do_group_exit` (`zap_other_threads`), killing all sibling threads in its thread group. -/
def AliveState.canTriggerGroupExit (a : AliveState) : Bool :=
  a.pending.killed ||
    (a.run == .running && (!a.pending.termSigs.isEmpty || a.auto != .controlled))

/-- Linux `kernel/exit.c` task lifecycle. -/
inductive ProcLifecycle where
  /-- Live task (possibly with pending signals or autonomous exit in flight). -/
  | alive (st : AliveState)
  /-- Confirmed `EXIT_ZOMBIE`: exact `status`, immune to signals unless delayed by active subthreads. -/
  | zombie (status : ZombieStatus)
  /-- `EXIT_ZOMBIE` leader delayed by live subthreads (`delay_group_leader`). -/
  | delayedZombie (status : ZombieStatus) (killed : Bool := false) (termSigs : List UInt32 := [])
      (run : TaskRunState := .running) (cont : ContState := .none)
      (stopSigs : List UInt32 := []) (exitReap : ExitReapMode := .zombieOnly)
      (subExitedRace : Bool := false)
      (deferredTtyStops : List UInt32 := []) (racedTtyStops : List UInt32 := [])
  /-- Auto-reaped `EXIT_DEAD` observed by `wait4` (`ECHILD`), pre-`__unhash_process` window. -/
  | exitDead
  /-- Fully reaped and unhashed (`wait4` -> `ECHILD`, `kill`/`pidfd_*` -> `ESRCH`). -/
  | reaped
  deriving Repr, DecidableEq

/-- Returns `true` iff a `.delayedZombie` state currently has a deliverable group-fatal signal. -/
def delayedZombieCanDeliverFatal (killed : Bool) (termSigs : List UInt32) (run : TaskRunState) : Bool :=
  killed || (run == .running && (firstValidTermSig? termSigs).isSome)

/-- Child exit signal configured at `fork`/`clone` (`SIGCHLD` vs non-`SIGCHLD` `__WCLONE`). -/
inductive ChildExitSignal where
  /-- Standard `fork` child delivering `SIGCHLD` (eligible for `SIG_IGN`/`SA_NOCLDWAIT` auto-reap). -/
  | sigchld
  /-- Clone child with `exit_signal != SIGCHLD` (`__WCLONE`, never auto-reaps). -/
  | nonSigchld
  deriving Repr, DecidableEq

/-- Role of a tracked task in the Linux process/thread hierarchy. -/
inductive ProcRole where
  /-- Direct child thread-group leader (`wait4`-eligible). -/
  | child (exitSignal : ChildExitSignal := .sigchld) (fromSiblingThread : Bool := false)
  /-- Non-child thread-group leader (e.g. namespace `PID 1` init or foreign process). -/
  | foreign (unkillableInit : Bool := false)
  /-- Non-leader thread (`CLONE_THREAD`) belonging to thread-group leader `tgid`. -/
  | thread (tgid : UInt32)
  deriving Repr, DecidableEq

/-- Metadata for a tracked process or thread in `ProcessSysState`. -/
structure ProcEntry where
  /-- Process group ID (`0` represents an outer-namespace PGID inside `CLONE_NEWPID`). -/
  pgid : UInt32
  /-- True iff the calling process has permission to signal this target (`false` yields `EPERM`/`EACCES`). -/
  canSignal : Bool := true
  /-- True when this task belongs to the caller's session (`SIGCONT` bypasses cross-UID `EPERM`). -/
  sameSession : Bool := true
  /-- True when this process belongs to an orphaned process group (default `SIGTSTP`/`SIGTTIN`/`SIGTTOU` are discarded). -/
  orphanedPgid : Bool := false
  /-- Signals whose handler/mask was explicitly reset to `SIG_DFL` and unblocked in this child (overrides `ambientIgnoredSigs`). -/
  unignoredSigs : List UInt32 := []
  /-- Role in the process/thread hierarchy. -/
  role : ProcRole := .child .sigchld false
  /-- `AliveState` snapshots of non-leader subthreads already pruned via `ESRCH` while this leader remained unreaped. -/
  reapedSubthreads : List AliveState := []
  /-- Current Linux task lifecycle state. -/
  lifecycle : ProcLifecycle
  deriving Repr, DecidableEq

/-- Returns `true` iff `e` is a direct child thread-group leader. -/
def ProcEntry.isChildLeader (e : ProcEntry) : Bool :=
  match e.role with | .child _ _ => true | _ => false

/-- Returns `true` iff `e` is a thread-group leader (child or foreign, not a non-leader thread). -/
def ProcEntry.isLeader (e : ProcEntry) : Bool :=
  match e.role with | .thread _ => false | _ => true

/-- Returns `true` iff `e` is a direct child with `SIGCHLD` exit signal. -/
def ProcEntry.isSigchldChild (e : ProcEntry) : Bool :=
  match e.role with | .child .sigchld _ => true | _ => false

/-- Returns `true` iff `e` is a clone child with `exit_signal != SIGCHLD` (`__WCLONE`). -/
def ProcEntry.isCloneChild (e : ProcEntry) : Bool :=
  match e.role with | .child .nonSigchld _ => true | _ => false

/-- Returns `true` iff `e` is a child spawned by a sibling thread (`__WNOTHREAD`). -/
def ProcEntry.fromSiblingThread (e : ProcEntry) : Bool :=
  match e.role with | .child _ fst => fst | _ => false

/-- Returns `true` iff `e` has `SIGNAL_UNKILLABLE` (`PID 1` init inside a PID namespace). -/
def ProcEntry.isUnkillableInit (e : ProcEntry) : Bool :=
  match e.role with | .foreign true => true | _ => false

/-- Ambient parent `SIGCHLD` auto-reap disposition (`SIG_DFL` vs `SIG_IGN`/`SA_NOCLDWAIT`). -/
inductive SigchldDisposition where
  /-- Normal reaping via `wait4` (`EXIT_ZOMBIE` retained until waited). -/
  | default
  /-- `SIGCHLD = SIG_IGN` or `SA_NOCLDWAIT` (`SIGCHLD` children auto-reap to `EXIT_DEAD`). -/
  | autoreap
  deriving Repr, DecidableEq

/-- Open (or explicitly closed) descriptor record tracked by `ProcessSysState`. -/
inductive ProcessFdDesc where
  /-- Read end of a pipe allocated by `pipe2(2)`. -/
  | pipeRead (cloexec : Bool) (nonblock : Bool)
  /-- Write end of a pipe allocated by `pipe2(2)`. -/
  | pipeWrite (cloexec : Bool) (nonblock : Bool)
  /-- Process file descriptor allocated by `pidfd_open(2)` (`FD_CLOEXEC` is always `true`). -/
  | pidfd (targetPid : UInt32) (nonblock : Bool) (isThreadPidfd : Bool := false)
  /-- Descriptor explicitly closed at the `LeanFdBox` layer (`EBADF` before kernel syscall). -/
  | closed
  deriving Repr, DecidableEq

/-- Executable stateful world model for all 7 curated Linux `Process` syscalls. -/
structure ProcessSysState where
  /-- Calling process thread-group ID (`PID`, normalized into `1..0x7fffffff` via `effectiveSelfPid`). -/
  selfPid : UInt32 := 1000
  /-- Calling process group ID (`PGID`, normalized into `0..0x7fffffff` via `effectiveSelfPgid`). -/
  selfPgid : UInt32 := 1000
  /-- Calling process real user ID (`UID`). -/
  selfUid : UInt32 := 1000
  /-- Ambient `SIGCHLD` disposition (`default` vs `autoreap`). -/
  sigchld : SigchldDisposition := .default
  /-- Ambient signals in `1..64` (excluding `9`, `18`, `19`) inherited as `SIG_IGN` or blocked. -/
  ambientIgnoredSigs : List UInt32 := []
  /-- True in a closed PID namespace (`false` on shared hosts with untracked OS processes). -/
  closedPidNamespace : Bool := true
  /-- True when an ambient `seccomp` `SECCOMP_RET_ERRNO` filter may synthesize errnos (`!= EFAULT`). -/
  ambientSeccomp : Bool := false
  /-- True when kernel `CONFIG_WATCH_QUEUE` supports `pipe2(..., O_NOTIFICATION_PIPE)`. -/
  watchQueueSupported : Bool := false
  /-- True when kernel supports `pidfd_open(..., PIDFD_THREAD)`. -/
  pidfdThreadSupported : Bool := true
  /-- Tracked child, foreign, and thread entries keyed by `PID`/`TID`. -/
  procs : List (UInt32 × ProcEntry) := []
  /-- Descriptor table mapping logical `HandleId` to `ProcessFdDesc`. -/
  fds : List (HandleId × ProcessFdDesc) := []
  /-- Next logical handle ID hint. -/
  nextHid : HandleId := 0
  deriving Repr, DecidableEq, Inhabited

/-- Default initial `ProcessSysState`. -/
def ProcessSysState.initial (selfPid : UInt32 := 1000) (selfPgid : UInt32 := 1000) (selfUid : UInt32 := 1000) :
    ProcessSysState :=
  { selfPid
    selfPgid
    selfUid
    sigchld := .default
    ambientIgnoredSigs := []
    closedPidNamespace := true
    ambientSeccomp := false
    watchQueueSupported := false
    pidfdThreadSupported := true
    procs := []
    fds := []
    nextHid := 0 }

/-- Update `exitReap` mode when toggling `SIGCHLD` auto-reap disposition. -/
def ExitReapMode.onSigchldToggle (canFatal enabled : Bool) (mode : ExitReapMode) : ExitReapMode :=
  if !canFatal then
    if enabled then .autoreapOnly else .zombieOnly
  else if enabled && mode == .zombieOnly then
    .either
  else if !enabled && mode == .autoreapOnly then
    .either
  else
    mode

/-- Update `exitReap` on one `AliveState` when toggling `SIGCHLD` auto-reap mode. -/
def AliveState.onSigchldToggle (enabled : Bool) (a : AliveState) : AliveState :=
  { a with exitReap := ExitReapMode.onSigchldToggle a.canDeliverFatal enabled a.exitReap }

/-- Tail-recursive helper collecting thread-group leader PIDs that have a `.controlled` live subthread unable to exit on its own. -/
def collectControlledSubthreadTgidsGo (procs : List (UInt32 × ProcEntry)) (seen acc : Std.TreeSet UInt32 compare) :
    Std.TreeSet UInt32 compare :=
  match procs with
  | [] => acc
  | (pid, entry) :: rest =>
    if seen.contains pid then
      collectControlledSubthreadTgidsGo rest seen acc
    else
      let acc' :=
        match entry.role with
        | .thread tgid =>
          match entry.lifecycle with
          | .alive a => if a.auto == .controlled && !a.canDeliverFatal then acc.insert tgid else acc
          | _ => acc
        | _ => acc
      collectControlledSubthreadTgidsGo rest (seen.insert pid) acc'

/-- Collect the set of thread-group leader PIDs that still have a controlled live subthread. -/
def collectControlledSubthreadTgids (procs : List (UInt32 × ProcEntry)) : Std.TreeSet UInt32 compare :=
  collectControlledSubthreadTgidsGo procs {} {}

/-- Tail-recursive helper collecting thread-group leader PIDs where a live or already-pruned subthread can trigger `do_group_exit` (`zap_other_threads`). -/
def collectGroupExitSubthreadTgidsGo (procs : List (UInt32 × ProcEntry)) (seen acc : Std.TreeSet UInt32 compare) :
    Std.TreeSet UInt32 compare :=
  match procs with
  | [] => acc
  | (pid, entry) :: rest =>
    if seen.contains pid then
      collectGroupExitSubthreadTgidsGo rest seen acc
    else
      let acc' :=
        match entry.role with
        | .thread tgid =>
          match entry.lifecycle with
          | .alive a => if a.canTriggerGroupExit then acc.insert tgid else acc
          | _ => acc
        | _ =>
          if entry.reapedSubthreads.any AliveState.canTriggerGroupExit then acc.insert pid else acc
      collectGroupExitSubthreadTgidsGo rest (seen.insert pid) acc'

/-- Collect the set of thread-group leader PIDs that have a subthread able to trigger `do_group_exit`. -/
def collectGroupExitSubthreadTgids (procs : List (UInt32 × ProcEntry)) : Std.TreeSet UInt32 compare :=
  collectGroupExitSubthreadTgidsGo procs {} {}

/-- Tail-recursive helper collecting thread-group leader PIDs with an active running `.arbitrary` subthread. -/
def collectArbitraryRunningSubthreadTgidsGo (procs : List (UInt32 × ProcEntry))
    (seen acc : Std.TreeSet UInt32 compare) : Std.TreeSet UInt32 compare :=
  match procs with
  | [] => acc
  | (pid, entry) :: rest =>
    if seen.contains pid then
      collectArbitraryRunningSubthreadTgidsGo rest seen acc
    else
      let acc' :=
        match entry.role, entry.lifecycle with
        | .thread tgid, .alive a =>
          if a.run == .running && a.auto == .arbitrary then acc.insert tgid else acc
        | _, _ => acc
      collectArbitraryRunningSubthreadTgidsGo rest (seen.insert pid) acc'

/-- Collect the set of thread-group leader PIDs with an active running `.arbitrary` subthread. -/
def collectArbitraryRunningSubthreadTgids (procs : List (UInt32 × ProcEntry)) : Std.TreeSet UInt32 compare :=
  collectArbitraryRunningSubthreadTgidsGo procs {} {}

/-- Returns `true` iff `pid` has a `.controlled` live subthread and no sibling subthread can trigger `do_group_exit` (`zap_other_threads`). -/
def isHeldByControlledSubthreadSet (ctrlSubTgids groupExitSubTgids : Std.TreeSet UInt32 compare) (pid : UInt32) : Bool :=
  ctrlSubTgids.contains pid && !groupExitSubTgids.contains pid

/-- Configure ambient `SIGCHLD = SIG_IGN` / `SA_NOCLDWAIT` auto-reap mode on `s`. -/
def ProcessSysState.withSigchldAutoreap (s : ProcessSysState) (enabled : Bool := true) : ProcessSysState :=
  let disp : SigchldDisposition := if enabled then .autoreap else .default
  let procs' :=
    if disp == s.sigchld then s.procs
    else
      let ctrlSubTgids := collectControlledSubthreadTgids s.procs
      let groupExitSubTgids := collectGroupExitSubthreadTgids s.procs
      s.procs.map fun (pid, entry) =>
        match entry.role, entry.lifecycle with
        | .child .sigchld _, .alive a =>
          let canFinish := a.canDeliverFatal || (a.run == .running && groupExitSubTgids.contains pid)
          (pid, { entry with lifecycle := .alive { a with exitReap := ExitReapMode.onSigchldToggle canFinish enabled a.exitReap } })
        | .child .sigchld _, .delayedZombie z k ts run cont ss exitReap race ds rs =>
          let hasCtrl := isHeldByControlledSubthreadSet ctrlSubTgids groupExitSubTgids pid
          let canFinish := delayedZombieCanDeliverFatal k ts run || (run == .running && !hasCtrl)
          (pid, { entry with lifecycle := .delayedZombie z k ts run cont ss (ExitReapMode.onSigchldToggle canFinish enabled exitReap) race ds rs })
        | _, _ => (pid, entry)
  { s with sigchld := disp, procs := procs' }

/-- Configure ambient inherited `SIG_IGN` or blocked signal numbers on `s`. -/
def ProcessSysState.withAmbientIgnoredSigs (s : ProcessSysState) (sigs : List UInt32) : ProcessSysState :=
  { s with ambientIgnoredSigs := sigs }

/-- Configure shared open-host PID visibility (`closedPidNamespace := !openHost`) on `s`. -/
def ProcessSysState.withOpenHostPids (s : ProcessSysState) (openHost : Bool := true) : ProcessSysState :=
  { s with closedPidNamespace := !openHost }

/-- Configure ambient `seccomp` `SECCOMP_RET_ERRNO` interception support on `s`. -/
def ProcessSysState.withAmbientSeccomp (s : ProcessSysState) (enabled : Bool := true) : ProcessSysState :=
  { s with ambientSeccomp := enabled }

/-- Configure whether `pipe2(..., O_NOTIFICATION_PIPE)` (`CONFIG_WATCH_QUEUE`) is supported by the host kernel. -/
def ProcessSysState.withWatchQueueSupported (s : ProcessSysState) (supported : Bool := true) : ProcessSysState :=
  { s with watchQueueSupported := supported }

/-- Configure whether `pidfd_open(..., PIDFD_THREAD)` is supported by the host kernel. -/
def ProcessSysState.withPidfdThreadSupported (s : ProcessSysState) (supported : Bool := true) : ProcessSysState :=
  { s with pidfdThreadSupported := supported }

/-- Effective positive `selfPid` in `1..0x7fffffff`. -/
def effectiveSelfPid (s : ProcessSysState) : UInt32 :=
  if 1 ≤ s.selfPid && s.selfPid ≤ maxLinuxPid then s.selfPid else 1000

/-- Effective `selfPgid` in `0..0x7fffffff`. -/
def effectiveSelfPgid (s : ProcessSysState) : UInt32 :=
  if s.selfPgid ≤ maxLinuxPid then s.selfPgid else effectiveSelfPid s

/-- Append `sig` to `xs` if not already present, preserving queue order. -/
def appendUniqueSig (xs : List UInt32) (sig : UInt32) : List UInt32 :=
  if xs.contains sig then xs else xs ++ [sig]

/-- Compute a fresh `HandleId` strictly greater than every existing key in `fds` and `>= hint`. -/
def nextFreeHid (fds : List (HandleId × ProcessFdDesc)) (hint : HandleId) : HandleId :=
  match fds with
  | [] => hint
  | (k, _) :: rest => nextFreeHid rest (max hint (k + 1))

/-- Pure state helper registering or replacing a tracked process entry at `pid`. -/
def ProcessSysState.upsertProc (s : ProcessSysState) (pid : UInt32) (entry : ProcEntry) : ProcessSysState :=
  { s with procs := assocSet s.procs pid entry }

private def initialChildExitReap (s : ProcessSysState) (isCloneChild : Bool) : ExitReapMode :=
  if s.sigchld == .autoreap && !isCloneChild then .autoreapOnly else .zombieOnly

/-- Pure state helper registering a controlled running direct child process `(pid, pgid)`. -/
def ProcessSysState.spawnRunningChild (s : ProcessSysState) (pid : UInt32) (pgid : UInt32 := pid)
    (autoExit? : Option ZombieStatus := none)
    (isCloneChild : Bool := false) (fromSiblingThread : Bool := false)
    (orphanedPgid : Bool := false) : ProcessSysState :=
  let exitSig : ChildExitSignal := if isCloneChild then .nonSigchld else .sigchld
  let autoB : AutoBehavior := match autoExit? with | some z => .planned z | none => .controlled
  s.upsertProc pid
    { pgid := pgid
      canSignal := true
      sameSession := true
      orphanedPgid := orphanedPgid
      role := .child exitSig fromSiblingThread
      lifecycle := .alive { auto := autoB, exitReap := initialChildExitReap s isCloneChild } }

/-- Pure state helper registering an autonomous running direct child process `(pid, pgid)`. -/
def ProcessSysState.spawnAutonomousChild (s : ProcessSysState) (pid : UInt32) (pgid : UInt32 := pid)
    (isCloneChild : Bool := false) (fromSiblingThread : Bool := false)
    (orphanedPgid : Bool := false) : ProcessSysState :=
  let exitSig : ChildExitSignal := if isCloneChild then .nonSigchld else .sigchld
  s.upsertProc pid
    { pgid := pgid
      canSignal := true
      sameSession := true
      orphanedPgid := orphanedPgid
      role := .child exitSig fromSiblingThread
      lifecycle := .alive { auto := .arbitrary, exitReap := initialChildExitReap s isCloneChild } }

/-- Pure state helper registering an already-confirmed `TASK_STOPPED` direct child process. -/
def ProcessSysState.spawnStoppedChild (s : ProcessSysState) (pid : UInt32) (stopSig : UInt32 := 19)
    (reported : Bool := false) (pgid : UInt32 := pid)
    (orphanedPgid : Bool := false) (unignoredSigs : List UInt32 := [normalizeWaitSig stopSig]) : ProcessSysState :=
  s.upsertProc pid
    { pgid := pgid
      canSignal := true
      sameSession := true
      orphanedPgid := orphanedPgid
      unignoredSigs := unignoredSigs
      role := .child .sigchld false
      lifecycle := .alive { run := .stopped (normalizeWaitSig stopSig) reported, exitReap := initialChildExitReap s false } }

/-- Pure state helper registering an already-exited confirmed zombie direct child `(pid, exitCode)`. -/
def ProcessSysState.spawnZombieExited (s : ProcessSysState) (pid : UInt32) (exitCode : UInt8) (pgid : UInt32 := pid)
    (isCloneChild : Bool := false) (fromSiblingThread : Bool := false) : ProcessSysState :=
  let exitSig : ChildExitSignal := if isCloneChild then .nonSigchld else .sigchld
  s.upsertProc pid
    { pgid := pgid
      canSignal := true
      sameSession := true
      role := .child exitSig fromSiblingThread
      lifecycle := .zombie (.exited exitCode) }

/-- Pure state helper registering an already-signaled confirmed zombie direct child `(pid, termSig, coreDumped)`. -/
def ProcessSysState.spawnZombieSignaled (s : ProcessSysState) (pid : UInt32) (termSig : UInt32)
    (coreDumped : Bool := false) (pgid : UInt32 := pid) : ProcessSysState :=
  s.upsertProc pid
    { pgid := pgid
      canSignal := true
      sameSession := true
      role := .child .sigchld false
      lifecycle := .zombie (.signaled (normalizeWaitSig termSig) coreDumped) }

/-- Pure state helper registering an unowned foreign process (`canSignal = false` by default). -/
def ProcessSysState.registerForeignProc (s : ProcessSysState) (pid : UInt32) (pgid : UInt32 := pid)
    (canSignal : Bool := false) (sameSession : Bool := false) : ProcessSysState :=
  s.upsertProc pid
    { pgid := pgid
      canSignal := canSignal
      sameSession := sameSession
      role := .foreign false
      lifecycle := .alive {} }

/-- Pure state helper registering `PID 1` inside a `CLONE_NEWPID` namespace with `SIGNAL_UNKILLABLE`. -/
def ProcessSysState.registerPid1Init (s : ProcessSysState) (pgid : UInt32 := 1)
    (canSignal : Bool := true) (sameSession : Bool := true) : ProcessSysState :=
  s.upsertProc 1
    { pgid := pgid
      canSignal := canSignal
      sameSession := sameSession
      role := .foreign true
      lifecycle := .alive {} }

/-- Pure state helper registering a non-leader thread `tid` belonging to thread-group leader `tgid`. -/
def ProcessSysState.registerNonLeaderThread (s : ProcessSysState) (tid : UInt32) (tgid : UInt32)
    (pgid : UInt32 := tgid) (canSignal : Bool := true) (sameSession : Bool := true) : ProcessSysState :=
  s.upsertProc tid
    { pgid := pgid
      canSignal := canSignal
      sameSession := sameSession
      role := .thread tgid
      lifecycle := .alive {} }

/-- Pure state helper removing `hid` upon closing at the `LeanFdBox` layer without unbounded dead-handle growth. -/
def ProcessSysState.closeFd (s : ProcessSysState) (hid : HandleId) : ProcessSysState :=
  { s with fds := assocEraseAll s.fds hid, nextHid := max s.nextHid (hid + 1) }

/-- Update `fds` after allocating `(readHid, writeHid)` from `pipe2`. -/
def commitPipeFds (s : ProcessSysState) (readHid writeHid : HandleId) (flags : PipeFlags) : ProcessSysState :=
  let fds1 := assocSet s.fds readHid (.pipeRead flags.cloexec flags.nonblock)
  let fds2 := assocSet fds1 writeHid (.pipeWrite flags.cloexec flags.nonblock)
  let nextH := max s.nextHid (max (readHid + 1) (writeHid + 1))
  { s with fds := fds2, nextHid := nextH }

/-- Update `fds` after allocating `hid` from `pidfd_open`. -/
def commitPidfd (s : ProcessSysState) (hid : HandleId) (targetPid : UInt32) (nonblock : Bool)
    (isThreadPidfd : Bool := false) : ProcessSysState :=
  { s with
    fds := assocSet s.fds hid (.pidfd targetPid nonblock isThreadPidfd)
    nextHid := max s.nextHid (hid + 1) }

/-- Exact Linux `kernel/signal.c` transition on a live `AliveState` for a valid, unignored signal. -/
def applySignalToAlive (canAutoreapNow : Bool) (sig : Signal) (a : AliveState)
    (hasGroupExitSub : Bool := false) (hasArbSub : Bool := false) : AliveState :=
  let n := sig.toLinuxNum
  if n == 0 || !(1 ≤ n && n ≤ 64) || isDefaultIgnoredSignal n then
    a
  else
    let sig32 : UInt32 := UInt32.ofNat n.toNat
    let reapNow : ExitReapMode := if canAutoreapNow then .autoreapOnly else .zombieOnly
    let canFinishNow : Bool := a.canDeliverFatal || (a.run == .running && hasGroupExitSub)
    match a.run with
    | .stopped _ _ =>
      if n == 9 then
        { run := .running, cont := .none, auto := .controlled, pending := { killed := true },
          exitReap := reapNow, subExitedRace := false }
      else if n == 18 then
        let hasTerm := (firstValidTermSig? a.pending.termSigs).isSome
        let auto' :=
          if hasTerm then
            match a.auto with | .planned _ => .controlled | other => other
          else
            a.auto
        let hasFatal := !a.pending.termSigs.isEmpty || auto' != .controlled || hasGroupExitSub
        { a with
          run := .running
          cont := .confirmed
          auto := auto'
          subExitedRace := if hasTerm then false else a.subExitedRace
          pending := { a.pending with stopSigs := [], deferredTtyStops := [], racedTtyStops := [] }
          exitReap := if hasFatal then reapNow else a.exitReap }
      else if isStopSignal n then
        a
      else
        { a with pending := { a.pending with termSigs := appendUniqueSig a.pending.termSigs sig32 } }
    | .running =>
      if n == 9 then
        let race' := a.subExitedRace || (!a.canDeliverGroupFatal && hasGroupExitSub)
        { a with
          cont := .none
          subExitedRace := race'
          pending := { a.pending with killed := true, stopSigs := [], deferredTtyStops := [], racedTtyStops := [] }
          exitReap := if canFinishNow then a.exitReap else reapNow }
      else if a.pending.killed then
        a
      else if n == 18 then
        if !a.pending.stopSigs.isEmpty || !a.pending.deferredTtyStops.isEmpty ||
           !a.pending.racedTtyStops.isEmpty || a.auto == .arbitrary || hasArbSub then
          { a with
            cont := if a.cont == .confirmed then .confirmed else .maybe
            pending := { a.pending with stopSigs := [], deferredTtyStops := [], racedTtyStops := [] } }
        else
          a
      else if isStopSignal n then
        { a with
          cont := if a.cont == .confirmed then .maybe else a.cont
          pending := { a.pending with stopSigs := appendUniqueSig a.pending.stopSigs sig32 } }
      else
        let race' := a.subExitedRace || (!a.canDeliverGroupFatal && hasGroupExitSub)
        { a with
          subExitedRace := race'
          pending := { a.pending with termSigs := appendUniqueSig a.pending.termSigs sig32 }
          exitReap := if canFinishNow then a.exitReap else reapNow }

/-- Returns `true` iff `lc` is a confirmed `.zombie` or `.delayedZombie` state. -/
def isZombieLifecycle (lc : ProcLifecycle) : Bool :=
  match lc with
  | .zombie _ | .delayedZombie _ _ _ _ _ _ _ _ _ _ => true
  | _ => false

/-- Returns `true` iff `lc` is a confirmed `.zombie` state (all subthreads already exited). -/
def isPlainZombieLifecycle (lc : ProcLifecycle) : Bool :=
  match lc with
  | .zombie _ => true
  | _ => false

/-- Returns `true` iff `e` is uncontrolled or can die/has exited (`auto != .controlled` or `canDeliverFatal` or zombie/dead). -/
def isEntryUncontrolledOrDying (e : ProcEntry) : Bool :=
  match e.lifecycle with
  | .alive a => a.auto != .controlled || a.canDeliverFatal
  | .delayedZombie _ k ts run _ _ _ _ _ _ => delayedZombieCanDeliverFatal k ts run
  | .zombie _ | .exitDead | .reaped => true

/-- Returns `true` iff signal `n` is ignorable (`n != 9 && n != 18 && n != 19`) and listed in `ignoredSigs`. -/
def isAmbientIgnoredSignal (ignoredSigs : List UInt32) (n : Int) : Bool :=
  if 1 ≤ n && n ≤ 64 && n != 9 && n != 18 && n != 19 then
    ignoredSigs.contains (UInt32.ofNat n.toNat)
  else
    false

/-- Returns `true` iff Linux `check_kill_permission` allows delivering `sig` to `entry`. -/
def canSignalEntry (sig : Signal) (entry : ProcEntry) : Bool :=
  entry.canSignal || (sig.toLinuxNum == 18 && entry.sameSession)

/-- Returns `true` iff `n` is a terminal job-control stop signal (`SIGTSTP`/`SIGTTIN`/`SIGTTOU`), which Linux discards when the target process group is orphaned. -/
def isTtyStopSignal (n : Int) : Bool :=
  n == 20 || n == 21 || n == 22

/-- Tail-recursive helper checking whether any active (non-shadowed) entry in `procs` satisfies `pred`. -/
def anyActiveProcGo (procs : List (UInt32 × ProcEntry)) (seen : Std.TreeSet UInt32 compare)
    (pred : UInt32 → ProcEntry → Bool) : Bool :=
  match procs with
  | [] => false
  | (pid, entry) :: rest =>
    if seen.contains pid then
      anyActiveProcGo rest seen pred
    else if pred pid entry then
      true
    else
      anyActiveProcGo rest (seen.insert pid) pred

/-- Returns `true` iff at least one active (first-occurrence) entry in `procs` satisfies `pred`. -/
def anyActiveProc (procs : List (UInt32 × ProcEntry)) (pred : UInt32 → ProcEntry → Bool) : Bool :=
  anyActiveProcGo procs {} pred

/-- Tail-recursive helper checking whether every active (first-occurrence) entry in `procs` satisfying `filterPred` also satisfies `holdPred`. -/
def allActiveProcWhereGo (procs : List (UInt32 × ProcEntry)) (seen : Std.TreeSet UInt32 compare)
    (filterPred holdPred : UInt32 → ProcEntry → Bool) : Bool :=
  match procs with
  | [] => true
  | (pid, entry) :: rest =>
    if seen.contains pid then
      allActiveProcWhereGo rest seen filterPred holdPred
    else if filterPred pid entry && !holdPred pid entry then
      false
    else
      allActiveProcWhereGo rest (seen.insert pid) filterPred holdPred

/-- Returns `true` iff every active (first-occurrence) entry in `procs` satisfying `filterPred` also satisfies `holdPred`. -/
def allActiveProcWhere (procs : List (UInt32 × ProcEntry))
    (filterPred holdPred : UInt32 → ProcEntry → Bool) : Bool :=
  allActiveProcWhereGo procs {} filterPred holdPred

/-- Returns `true` iff thread-group leader `leaderPid` has at least one active non-leader subthread (`delay_group_leader`). -/
def hasActiveSubthread (procs : List (UInt32 × ProcEntry)) (leaderPid : UInt32) : Bool :=
  anyActiveProc procs fun _ e =>
    match e.role with
    | .thread tgid => tgid == leaderPid && e.lifecycle != .reaped && e.lifecycle != .exitDead
    | _ => false

/-- Tail-recursive helper collecting all leader PIDs that have an active non-leader subthread. -/
def collectActiveSubthreadTgidsGo (procs : List (UInt32 × ProcEntry)) (seen acc : Std.TreeSet UInt32 compare) :
    Std.TreeSet UInt32 compare :=
  match procs with
  | [] => acc
  | (pid, entry) :: rest =>
    if seen.contains pid then
      collectActiveSubthreadTgidsGo rest seen acc
    else
      let acc' :=
        match entry.role with
        | .thread tgid =>
          if entry.lifecycle != .reaped && entry.lifecycle != .exitDead then acc.insert tgid else acc
        | _ => acc
      collectActiveSubthreadTgidsGo rest (seen.insert pid) acc'

/-- Collect the set of thread-group leader PIDs currently blocked on `delay_group_leader`. -/
def collectActiveSubthreadTgids (procs : List (UInt32 × ProcEntry)) : Std.TreeSet UInt32 compare :=
  collectActiveSubthreadTgidsGo procs {} {}

/-- Tail-recursive helper collecting active leader PIDs in `procs` satisfying `pred` into a `TreeSet`. -/
def collectActivePidSetGo (procs : List (UInt32 × ProcEntry)) (seen acc : Std.TreeSet UInt32 compare)
    (pred : UInt32 → ProcEntry → Bool) : Std.TreeSet UInt32 compare :=
  match procs with
  | [] => acc
  | (pid, entry) :: rest =>
    if seen.contains pid then
      collectActivePidSetGo rest seen acc pred
    else
      let acc' := if pred pid entry then acc.insert pid else acc
      collectActivePidSetGo rest (seen.insert pid) acc' pred

/-- Returns `true` iff `leaderPid` has at least one `.controlled` subthread that cannot exit on its own or pending fatal signals. -/
def hasRawControlledLiveSubthread (procs : List (UInt32 × ProcEntry)) (leaderPid : UInt32) : Bool :=
  anyActiveProc procs fun _ e =>
    match e.role with
    | .thread tgid =>
      tgid == leaderPid &&
        match e.lifecycle with
        | .alive a => a.auto == .controlled && !a.canDeliverFatal
        | _ => false
    | _ => false

/-- Returns `true` iff `leaderPid` has an active or already-pruned subthread able to trigger `do_group_exit` (`zap_other_threads`). -/
def hasGroupExitSubthread (procs : List (UInt32 × ProcEntry)) (leaderPid : UInt32) : Bool :=
  anyActiveProc procs fun pid e =>
    match e.role with
    | .thread tgid =>
      tgid == leaderPid &&
        match e.lifecycle with
        | .alive a => a.canTriggerGroupExit
        | _ => false
    | _ =>
      pid == leaderPid && e.reapedSubthreads.any AliveState.canTriggerGroupExit

/-- Returns `true` iff `leaderPid` is held open by a `.controlled` live subthread with no sibling subthread able to trigger `do_group_exit`. -/
def hasControlledLiveSubthread (procs : List (UInt32 × ProcEntry)) (leaderPid : UInt32) : Bool :=
  hasRawControlledLiveSubthread procs leaderPid && !hasGroupExitSubthread procs leaderPid

private def applySignalToDelayedZombie (canAutoreapNow hasCtrlSub hasArbSub : Bool) (n : Int) (sig32 : UInt32)
    (z : ZombieStatus) (killed : Bool) (termSigs : List UInt32) (run : TaskRunState)
    (cont : ContState) (stopSigs : List UInt32) (exitReap : ExitReapMode)
    (subExitedRace : Bool) (deferredTtyStops racedTtyStops : List UInt32) : ProcLifecycle :=
  if n == 0 || !(1 ≤ n && n ≤ 64) || isDefaultIgnoredSignal n then
    .delayedZombie z killed termSigs run cont stopSigs exitReap subExitedRace deferredTtyStops racedTtyStops
  else
    let reapNow : ExitReapMode := if canAutoreapNow then .autoreapOnly else .zombieOnly
    let canFinish := delayedZombieCanDeliverFatal killed termSigs run || (run == .running && !hasCtrlSub)
    if n == 9 then
      match run with
      | .stopped _ _ =>
        .delayedZombie z true [] .running .none [] reapNow false [] []
      | .running =>
        .delayedZombie z true termSigs .running .none [] (if canFinish then exitReap else reapNow) subExitedRace [] []
    else if killed then
      .delayedZombie z killed termSigs run cont stopSigs exitReap subExitedRace deferredTtyStops racedTtyStops
    else if n == 18 then
      match run with
      | .stopped _ _ =>
        let hasTerm := (firstValidTermSig? termSigs).isSome
        let hasFinish := hasTerm || !hasCtrlSub
        let raceOut := if hasTerm then false else subExitedRace
        .delayedZombie z killed termSigs .running .confirmed [] (if hasFinish then reapNow else exitReap) raceOut [] []
      | _ =>
        let hasPendingStop :=
          !stopSigs.isEmpty || !deferredTtyStops.isEmpty || !racedTtyStops.isEmpty || hasArbSub
        let cont' := if hasPendingStop && cont != .confirmed then .maybe else cont
        .delayedZombie z killed termSigs run cont' [] exitReap subExitedRace [] []
    else if isStopSignal n then
      match run with
      | .stopped _ _ => .delayedZombie z killed termSigs run cont stopSigs exitReap subExitedRace deferredTtyStops racedTtyStops
      | .running =>
        let cont' := if cont == .confirmed then .maybe else cont
        .delayedZombie z killed termSigs run cont' (appendUniqueSig stopSigs sig32) exitReap subExitedRace deferredTtyStops racedTtyStops
    else
      let exitReap' := if run == .running && !canFinish then reapNow else exitReap
      .delayedZombie z killed (appendUniqueSig termSigs sig32) run cont stopSigs exitReap' subExitedRace deferredTtyStops racedTtyStops

/-- Deliver `sig` to `entry` at `targetPid`, honoring `SIGNAL_UNKILLABLE`, `ambientIgnoredSigs`, orphaned-PGID TTY drop, and `delay_group_leader` scope. -/
def deliverSignalToEntry (s : ProcessSysState) (targetPid : UInt32) (sig : Signal)
    (entry : ProcEntry) (threadScoped : Bool := false)
    (activeSubTgids : Std.TreeSet UInt32 compare := collectActiveSubthreadTgids s.procs)
    (ctrlSubTgids : Std.TreeSet UInt32 compare := collectControlledSubthreadTgids s.procs)
    (groupExitSubTgids : Std.TreeSet UInt32 compare := collectGroupExitSubthreadTgids s.procs)
    (arbSubTgids : Std.TreeSet UInt32 compare := collectArbitraryRunningSubthreadTgids s.procs) : ProcEntry :=
  let n := sig.toLinuxNum
  let sig32 := if 1 ≤ n && n ≤ 64 then UInt32.ofNat n.toNat else 0
  let ambientIgn := isAmbientIgnoredSignal s.ambientIgnoredSigs n && !entry.unignoredSigs.contains sig32
  if entry.isUnkillableInit || ambientIgn then
    entry
  else if entry.orphanedPgid && isTtyStopSignal n then
    match entry.lifecycle with
    | .alive a =>
      if a.run == .running && !a.pending.killed && sig32 != 0 then
        { entry with
          lifecycle := .alive { a with pending := { a.pending with deferredTtyStops := appendUniqueSig a.pending.deferredTtyStops sig32 } } }
      else
        entry
    | .delayedZombie z k ts run cont ss exitReap race ds rs =>
      if !threadScoped && activeSubTgids.contains targetPid && run == .running && !k && sig32 != 0 then
        { entry with
          lifecycle := .delayedZombie z k ts run cont ss exitReap race (appendUniqueSig ds sig32) rs }
      else
        entry
    | _ => entry
  else
    match entry.lifecycle with
    | .alive a =>
      let canAuto := s.sigchld == .autoreap && entry.isSigchldChild
      let hasGeSub := entry.isLeader && groupExitSubTgids.contains targetPid
      let hasArb := entry.isLeader && arbSubTgids.contains targetPid
      { entry with lifecycle := .alive (applySignalToAlive canAuto sig a hasGeSub hasArb) }
    | .zombie _ => entry
    | .delayedZombie z k ts run cont ss exitReap race ds rs =>
      if threadScoped || !activeSubTgids.contains targetPid then
        entry
      else
        let canAuto := s.sigchld == .autoreap && entry.isSigchldChild
        let hasCtrl := isHeldByControlledSubthreadSet ctrlSubTgids groupExitSubTgids targetPid
        let hasArb := arbSubTgids.contains targetPid
        let isFatalSig := n != 0 && 1 ≤ n && n ≤ 64 && !isDefaultIgnoredSignal n && n != 18 && !isStopSignal n
        let race' := race || (!delayedZombieCanDeliverFatal k ts run && run == .running && isFatalSig && !hasCtrl)
        { entry with
          lifecycle := applySignalToDelayedZombie canAuto hasCtrl hasArb n sig32 z k ts run cont ss exitReap race' ds rs }
    | other => { entry with lifecycle := other }

/-- Update PGID and orphaned status, promoting `deferredTtyStops` into `racedTtyStops` when moving out of an orphaned PGID. -/
def ProcEntry.setPgid (e : ProcEntry) (newPg : UInt32) (isOrphaned : Bool) : ProcEntry :=
  let lc' :=
    if e.orphanedPgid && !isOrphaned then
      match e.lifecycle with
      | .alive a =>
        let mergedRaced := a.pending.deferredTtyStops.foldl appendUniqueSig a.pending.racedTtyStops
        let cont' :=
          if !a.pending.deferredTtyStops.isEmpty && a.cont == .confirmed then .maybe else a.cont
        .alive { a with
          cont := cont'
          pending := { a.pending with racedTtyStops := mergedRaced, deferredTtyStops := [] } }
      | .delayedZombie z k ts run cont ss exitReap race ds rs =>
        let mergedRaced := ds.foldl appendUniqueSig rs
        let cont' :=
          if !ds.isEmpty && cont == .confirmed then .maybe else cont
        .delayedZombie z k ts run cont' ss exitReap race [] mergedRaced
      | other => other
    else
      e.lifecycle
  { e with pgid := newPg, orphanedPgid := isOrphaned, lifecycle := lc' }

/-- Tail-recursive helper applying `sig` to every active (first-occurrence) entry in `procs` satisfying `pred`. -/
def applySignalWhereGo (s : ProcessSysState)
    (activeSubTgids ctrlSubTgids groupExitSubTgids arbSubTgids : Std.TreeSet UInt32 compare)
    (procs : List (UInt32 × ProcEntry)) (seen : Std.TreeSet UInt32 compare)
    (pred : UInt32 → ProcEntry → Bool) (sig : Signal) (acc : List (UInt32 × ProcEntry)) : List (UInt32 × ProcEntry) :=
  match procs with
  | [] => acc.reverse
  | (pid, entry) :: rest =>
    if seen.contains pid then
      applySignalWhereGo s activeSubTgids ctrlSubTgids groupExitSubTgids arbSubTgids rest seen pred sig ((pid, entry) :: acc)
    else
      let entry' :=
        if pred pid entry then
          deliverSignalToEntry s pid sig entry false activeSubTgids ctrlSubTgids groupExitSubTgids arbSubTgids
        else entry
      applySignalWhereGo s activeSubTgids ctrlSubTgids groupExitSubTgids arbSubTgids rest (seen.insert pid) pred sig ((pid, entry') :: acc)

/-- Apply `sig` to every active (first-occurrence) entry in `procs` satisfying `pred`. -/
def applySignalWhere (s : ProcessSysState) (procs : List (UInt32 × ProcEntry))
    (pred : UInt32 → ProcEntry → Bool) (sig : Signal) : List (UInt32 × ProcEntry) :=
  applySignalWhereGo s (collectActiveSubthreadTgids procs) (collectControlledSubthreadTgids procs)
    (collectGroupExitSubthreadTgids procs) (collectArbitraryRunningSubthreadTgids procs) procs {} pred sig []

/-- Shared pre-syscall boundary (`Impl.lean` NPTL `32`/`33` guard and `fd_box.h` closed/none `LeanFdBox` check). -/
def validateReqBeforeKernel (s : ProcessSysState) (req : ProcessReq) : Option Errno :=
  match req with
  | .kill _ sig =>
    if sig.isNptlReserved then some Errno.EINVAL else none
  | .pidfd_send_signal hid sig _ =>
    if sig.isNptlReserved then
      some Errno.EINVAL
    else
      match assocGet s.fds hid with
      | none | some .closed => some Errno.EBADF
      | some _ => none
  | _ => none

/-- Evaluate `PIDTYPE_PGID` group signal delivery across all active thread-group leaders in `targetPgid`. -/
def evalKillProcessGroup (s : ProcessSysState) (targetPgid : UInt32) (sig : Signal) :
    Except Errno ProcessSysState :=
  if sig.isNptlReserved then
    .error Errno.EINVAL
  else
    let selfPid := effectiveSelfPid s
    let selfPgid := effectiveSelfPgid s
    let selfInPgid : Bool := selfPgid == targetPgid
    let isGroupMember (pid : UInt32) (e : ProcEntry) : Bool :=
      pid != selfPid && e.isLeader && e.lifecycle != .reaped && e.lifecycle != .exitDead && e.pgid == targetPgid
    let hasAny : Bool := selfInPgid || anyActiveProc s.procs isGroupMember
    if !hasAny then
      .error Errno.ESRCH
    else if !sig.isValid then
      .error Errno.EINVAL
    else
      let canAny : Bool := selfInPgid ||
        anyActiveProc s.procs (fun pid e => isGroupMember pid e && canSignalEntry sig e)
      if !canAny then
        .error Errno.EPERM
      else
        let procs' := applySignalWhere s s.procs
          (fun pid e => isGroupMember pid e && canSignalEntry sig e) sig
        .ok { s with procs := procs' }

/-- Shared single-target signal delivery core used by both `kill(pid > 0, sig)` and single-target `pidfd_send_signal`. -/
def deliverSignalToTarget (s : ProcessSysState) (targetPid : UInt32) (sig : Signal)
    (threadScoped : Bool := false) : Except Errno ProcessSysState :=
  if sig.isNptlReserved then
    .error Errno.EINVAL
  else
    let selfPid := effectiveSelfPid s
    if targetPid == selfPid then
      if !sig.isValid then .error Errno.EINVAL else .ok s
    else
      match assocGet s.procs targetPid with
      | none => .error Errno.ESRCH
      | some entry =>
        if entry.lifecycle == .reaped || entry.lifecycle == .exitDead then
          .error Errno.ESRCH
        else
          match entry.role with
          | .thread leaderPid =>
            if leaderPid == selfPid then
              if !sig.isValid then .error Errno.EINVAL else .ok s
            else
              match assocGet s.procs leaderPid with
              | none =>
                if !sig.isValid then .error Errno.EINVAL
                else if !canSignalEntry sig entry then .error Errno.EPERM
                else .ok { s with procs := assocSet s.procs targetPid (deliverSignalToEntry s targetPid sig entry threadScoped) }
              | some leader =>
                if leader.lifecycle == .reaped || leader.lifecycle == .exitDead || isPlainZombieLifecycle leader.lifecycle then
                  .error Errno.ESRCH
                else if !sig.isValid then
                  .error Errno.EINVAL
                else if !canSignalEntry sig leader then
                  .error Errno.EPERM
                else
                  let procs1 := assocSet s.procs leaderPid (deliverSignalToEntry s leaderPid sig leader false)
                  .ok { s with procs := procs1 }
          | _ =>
            if !sig.isValid then
              .error Errno.EINVAL
            else if !canSignalEntry sig entry then
              .error Errno.EPERM
            else
              let entry' := deliverSignalToEntry s targetPid sig entry threadScoped
              let procs1 := assocSet s.procs targetPid entry'
              .ok { s with procs := procs1 }

/-- Pure evaluator for Linux `kill(pidOrNegPgid, sig)`. -/
def evalKill (s : ProcessSysState) (pidOrNegPgid : Int32) (sig : Signal) : Except Errno ProcessSysState :=
  if sig.isNptlReserved then
    .error Errno.EINVAL
  else if pidOrNegPgid == Int32.minValue then
    .error Errno.ESRCH
  else if pidOrNegPgid > 0 then
    deliverSignalToTarget s pidOrNegPgid.toUInt32 sig
  else if pidOrNegPgid == 0 then
    evalKillProcessGroup s (effectiveSelfPgid s) sig
  else if pidOrNegPgid == -1 then
    let selfPid := effectiveSelfPid s
    let isOtherLeader (pid : UInt32) (e : ProcEntry) : Bool :=
      pid != selfPid && pid > 1 && e.isLeader &&
      e.lifecycle != .reaped && e.lifecycle != .exitDead
    if !anyActiveProc s.procs isOtherLeader then
      .error Errno.ESRCH
    else if !sig.isValid then
      .error Errno.EINVAL
    else
      let procs' := applySignalWhere s s.procs
        (fun pid e => isOtherLeader pid e && canSignalEntry sig e) sig
      .ok { s with procs := procs' }
  else
    evalKillProcessGroup s (UInt32.ofNat (-pidOrNegPgid.toInt).toNat) sig

/-- Validate `pidfd_open(pid, flags)` target and flags following Linux `7.1.6` precedence. -/
def checkPidfdOpenTarget (s : ProcessSysState) (pid : UInt32) (flags : PidfdOpenFlags) : Except Errno Unit :=
  let selfPid := effectiveSelfPid s
  if !flags.isValid || (flags.thread && !s.pidfdThreadSupported) then
    .error Errno.EINVAL
  else if pid == 0 || pid > maxLinuxPid then
    .error Errno.EINVAL
  else if pid == selfPid then
    .ok ()
  else
    match assocGet s.procs pid with
    | none => .error Errno.ESRCH
    | some entry =>
      if entry.lifecycle == .reaped || entry.lifecycle == .exitDead then
        .error Errno.ESRCH
      else
        match entry.role with
        | .thread leaderPid =>
          if leaderPid != selfPid then
            match assocGet s.procs leaderPid with
            | some leader =>
              if leader.lifecycle == .reaped || leader.lifecycle == .exitDead || isPlainZombieLifecycle leader.lifecycle then .error Errno.ESRCH
              else if flags.thread then .ok ()
              else .error Errno.ENOENT
            | none =>
              if flags.thread then .ok () else .error Errno.ENOENT
          else
            if flags.thread then .ok () else .error Errno.ENOENT
        | _ => .ok ()

/-- Pure evaluator for `pidfd_send_signal(hid, sig, flags)`. -/
def evalPidfdSendSignal (s : ProcessSysState) (hid : HandleId) (sig : Signal) (flags : PidfdSignalFlags) :
    Except Errno ProcessSysState :=
  if sig.isNptlReserved then
    .error Errno.EINVAL
  else
    match assocGet s.fds hid with
    | none | some .closed => .error Errno.EBADF
    | some (.pipeRead _ _) | some (.pipeWrite _ _) =>
      if !flags.isValid then .error Errno.EINVAL else .error Errno.EBADF
    | some (.pidfd targetPid _ isThreadPidfd) =>
      if !flags.isValid then
        .error Errno.EINVAL
      else if targetPid == 0 || targetPid > maxLinuxPid then
        .error Errno.ESRCH
      else if flags.processGroup then
        evalKillProcessGroup s targetPid sig
      else
        let threadScoped := if flags.threadGroup then false else if flags.thread then true else isThreadPidfd
        deliverSignalToTarget s targetPid sig threadScoped

/-- Returns `true` iff child `(cPid, childPgid)` matches the `wait4` `pid` selector. -/
def matchesWaitSelector (selfPgid : UInt32) (pid : Int32) (cPid : UInt32) (childPgid : UInt32) : Bool :=
  if pid > 0 then
    cPid == pid.toUInt32
  else if pid == -1 then
    true
  else if pid == 0 then
    childPgid == selfPgid
  else if pid == Int32.minValue then
    false
  else
    childPgid == UInt32.ofNat (-pid.toInt).toNat

/-- Tail-recursive helper collecting active (first-occurrence) unreaped direct child thread-group leaders matching `pid` and `WaitFlags`. -/
def matchingUnreapedChildrenGo (selfPid selfPgid : UInt32) (pid : Int32) (flags : WaitFlags)
    (procs : List (UInt32 × ProcEntry)) (seen : Std.TreeSet UInt32 compare)
    (acc : List (UInt32 × ProcEntry)) : List (UInt32 × ProcEntry) :=
  match procs with
  | [] => acc.reverse
  | (cPid, entry) :: rest =>
    if seen.contains cPid then
      matchingUnreapedChildrenGo selfPid selfPgid pid flags rest seen acc
    else
      let cloneEligible : Bool := flags.wall || (flags.wclone == entry.isCloneChild)
      let threadEligible : Bool := !flags.wnothread || !entry.fromSiblingThread
      let keep : Bool :=
        cPid != selfPid && 1 ≤ cPid && cPid ≤ maxLinuxPid &&
        entry.isChildLeader &&
        entry.lifecycle != .reaped && entry.lifecycle != .exitDead &&
        cloneEligible && threadEligible &&
        matchesWaitSelector selfPgid pid cPid entry.pgid
      let acc' := if keep then (cPid, entry) :: acc else acc
      matchingUnreapedChildrenGo selfPid selfPgid pid flags rest (seen.insert cPid) acc'

/-- Return all active unreaped direct child thread-group leaders in `s` matching `wait4` selector `pid` and `flags`. -/
def matchingUnreapedChildren (s : ProcessSysState) (pid : Int32) (flags : WaitFlags) : List (UInt32 × ProcEntry) :=
  matchingUnreapedChildrenGo (effectiveSelfPid s) (effectiveSelfPgid s) pid flags s.procs {} []

/-- Update child `cPid`'s lifecycle in `s`. -/
def setProcLifecycle (s : ProcessSysState) (cPid : UInt32) (entry : ProcEntry) (lc : ProcLifecycle) : ProcessSysState :=
  { s with procs := assocSet s.procs cPid { entry with lifecycle := lc } }

/-- Remove a single reaped process or non-leader thread `pid` from `s.procs`. -/
def reapSingleProc (s : ProcessSysState) (pid : UInt32) : ProcessSysState :=
  { s with procs := assocEraseAll s.procs pid }

private def matchesThreadGroup (rPid pid : UInt32) (entry : ProcEntry) : Bool :=
  pid == rPid || match entry.role with | .thread t => t == rPid | _ => false

private def markThreadGroupLifecycleLoop (rPid : UInt32) (lc : ProcLifecycle)
    (procs : List (UInt32 × ProcEntry)) (seen pruned : Std.TreeSet UInt32 compare)
    (acc : List (UInt32 × ProcEntry)) : List (UInt32 × ProcEntry) :=
  match procs with
  | [] => acc.reverse
  | (pid, entry) :: rest =>
    if seen.contains pid then
      let acc' := if pruned.contains pid then acc else (pid, entry) :: acc
      markThreadGroupLifecycleLoop rPid lc rest seen pruned acc'
    else if matchesThreadGroup rPid pid entry then
      if lc == .reaped then
        markThreadGroupLifecycleLoop rPid lc rest (seen.insert pid) (pruned.insert pid) acc
      else
        markThreadGroupLifecycleLoop rPid lc rest (seen.insert pid) pruned ((pid, { entry with lifecycle := lc }) :: acc)
    else
      markThreadGroupLifecycleLoop rPid lc rest (seen.insert pid) pruned ((pid, entry) :: acc)

/-- Tail-recursive helper marking thread-group leader `rPid` and all active non-leader threads with `tgid == rPid` with lifecycle `lc` (or pruning them when `lc == .reaped`). -/
def markThreadGroupLifecycleGo (rPid : UInt32) (lc : ProcLifecycle)
    (procs : List (UInt32 × ProcEntry)) (seen : Std.TreeSet UInt32 compare)
    (acc : List (UInt32 × ProcEntry)) : List (UInt32 × ProcEntry) :=
  markThreadGroupLifecycleLoop rPid lc procs seen {} acc

/-- Reap and prune thread-group leader `rPid` and all non-leader threads in its thread group from `s.procs`. -/
def reapThreadGroup (s : ProcessSysState) (rPid : UInt32) : ProcessSysState :=
  { s with procs := markThreadGroupLifecycleGo rPid .reaped s.procs {} [] }

/-- Transition thread-group leader `rPid` and all non-leader threads in its thread group to `.exitDead`. -/
def exitDeadThreadGroup (s : ProcessSysState) (rPid : UInt32) : ProcessSysState :=
  { s with procs := markThreadGroupLifecycleGo rPid .exitDead s.procs {} [] }

private def matchesAnyThreadGroup (targets : Std.TreeSet UInt32 compare) (pid : UInt32) (entry : ProcEntry) : Bool :=
  targets.contains pid || match entry.role with | .thread t => targets.contains t | _ => false

private def markThreadGroupsLifecycleLoop (targets : Std.TreeSet UInt32 compare) (lc : ProcLifecycle)
    (procs : List (UInt32 × ProcEntry)) (seen pruned : Std.TreeSet UInt32 compare)
    (acc : List (UInt32 × ProcEntry)) : List (UInt32 × ProcEntry) :=
  match procs with
  | [] => acc.reverse
  | (pid, entry) :: rest =>
    if seen.contains pid then
      let acc' := if pruned.contains pid then acc else (pid, entry) :: acc
      markThreadGroupsLifecycleLoop targets lc rest seen pruned acc'
    else if matchesAnyThreadGroup targets pid entry then
      if lc == .reaped then
        markThreadGroupsLifecycleLoop targets lc rest (seen.insert pid) (pruned.insert pid) acc
      else
        markThreadGroupsLifecycleLoop targets lc rest (seen.insert pid) pruned ((pid, { entry with lifecycle := lc }) :: acc)
    else
      markThreadGroupsLifecycleLoop targets lc rest (seen.insert pid) pruned ((pid, entry) :: acc)

/-- Single-pass tail-recursive helper marking every thread group in `targets` with lifecycle `lc` (or pruning when `lc == .reaped`). -/
def markThreadGroupsLifecycleGo (targets : Std.TreeSet UInt32 compare) (lc : ProcLifecycle)
    (procs : List (UInt32 × ProcEntry)) (seen : Std.TreeSet UInt32 compare)
    (acc : List (UInt32 × ProcEntry)) : List (UInt32 × ProcEntry) :=
  markThreadGroupsLifecycleLoop targets lc procs seen {} acc

/-- Transition every child thread group in `matching` to `.exitDead` in a single `O(N log N)` pass. -/
def exitDeadMatchingThreadGroups (s : ProcessSysState) (matching : List (UInt32 × ProcEntry)) : ProcessSysState :=
  let targets := matching.foldl (fun acc (cPid, _) => acc.insert cPid) ({} : Std.TreeSet UInt32 compare)
  if targets.isEmpty then s else { s with procs := markThreadGroupsLifecycleGo targets .exitDead s.procs {} [] }

/-- Reap every active thread group whose leader in `s.procs` satisfies `pred` in a single `O(N log N)` pass. -/
def reapActiveLeadersWhere (s : ProcessSysState) (pred : UInt32 → ProcEntry → Bool) : ProcessSysState :=
  let targets := collectActivePidSetGo s.procs {} {} pred
  if targets.isEmpty then s else { s with procs := markThreadGroupsLifecycleGo targets .reaped s.procs {} [] }

/-- Returns `true` iff `(pid, e)` is a `SIGCHLD` child that can auto-reap to `EXIT_DEAD`/`reaped`. -/
def canAutoreapEntry (ctrlSubTgids groupExitSubTgids : Std.TreeSet UInt32 compare) (pid : UInt32) (e : ProcEntry) : Bool :=
  match e.role, e.lifecycle with
  | .child .sigchld _, .alive a =>
    a.exitReap != .zombieOnly &&
    (a.canDeliverFatal || (a.run == .running && groupExitSubTgids.contains pid))
  | .child .sigchld _, .delayedZombie _ k ts run _ _ exitReap _ _ _ =>
    let hasCtrl := isHeldByControlledSubthreadSet ctrlSubTgids groupExitSubTgids pid
    exitReap != .zombieOnly &&
    (delayedZombieCanDeliverFatal k ts run || (run == .running && !hasCtrl))
  | .child .sigchld _, .exitDead => true
  | .child .sigchld _, .reaped => true
  | _, _ => false

/-- Tail-recursive check whether every entry in `matching` can have exited and auto-reaped given `ctrlSubTgids` and `groupExitSubTgids`. -/
def allAutoreapableSet (ctrlSubTgids groupExitSubTgids : Std.TreeSet UInt32 compare) (matching : List (UInt32 × ProcEntry)) : Bool :=
  match matching with
  | [] => true
  | (cPid, e) :: rest =>
    if !canAutoreapEntry ctrlSubTgids groupExitSubTgids cPid e then false else allAutoreapableSet ctrlSubTgids groupExitSubTgids rest

/-- Check whether every entry in `matching` can have exited and auto-reaped in `procs`. -/
def allAutoreapable (procs : List (UInt32 × ProcEntry)) (matching : List (UInt32 × ProcEntry)) : Bool :=
  allAutoreapableSet (collectControlledSubthreadTgids procs) (collectGroupExitSubthreadTgids procs) matching

/-- Shared `ECHILD` auto-reap transition used identically by `evalModelWaitpid` and `allowedStepWaitpid`. -/
def autoReapEchildState (s : ProcessSysState) (matching : List (UInt32 × ProcEntry)) : Option ProcessSysState :=
  if allAutoreapable s.procs matching then
    some (if s.ambientSeccomp then s else exitDeadMatchingThreadGroups s matching)
  else
    none

/-- If `pid` is an unreaped autoreapable direct child thread-group leader, return `some (reapThreadGroup s pid)`. -/
def autoreapSinglePidEsrch? (s : ProcessSysState) (pid : UInt32) : Option ProcessSysState :=
  let selfPid := effectiveSelfPid s
  if pid == 0 || pid > maxLinuxPid || pid == selfPid then
    none
  else
    match assocGet s.procs pid with
    | some entry =>
      if entry.isChildLeader && entry.lifecycle != .reaped && entry.lifecycle != .exitDead &&
         canAutoreapEntry (collectControlledSubthreadTgids s.procs) (collectGroupExitSubthreadTgids s.procs) pid entry then
        some (reapThreadGroup s pid)
      else
        none
    | none => none

/-- Compute the post-`ESRCH` reaped state for a process group `targetPgid` under auto-reap. -/
def autoreapGroupEsrch? (s : ProcessSysState) (targetPgid : UInt32) : Option ProcessSysState :=
  if effectiveSelfPgid s == targetPgid then
    none
  else
    let selfPid := effectiveSelfPid s
    let ctrlSubTgids := collectControlledSubthreadTgids s.procs
    let groupExitSubTgids := collectGroupExitSubthreadTgids s.procs
    let isGroupMember (pid : UInt32) (e : ProcEntry) : Bool :=
      pid != selfPid && e.isLeader && e.lifecycle != .reaped && e.lifecycle != .exitDead && e.pgid == targetPgid
    let isAutoreapChild (pid : UInt32) (e : ProcEntry) : Bool :=
      e.isChildLeader && canAutoreapEntry ctrlSubTgids groupExitSubTgids pid e
    if anyActiveProc s.procs isGroupMember && allActiveProcWhere s.procs isGroupMember isAutoreapChild then
      some (reapActiveLeadersWhere s isGroupMember)
    else
      none

/-- Compute the post-`ESRCH` reaped state for `kill(pidOrNegPgid, sig)`. -/
def autoreapKillEsrch? (s : ProcessSysState) (pidOrNegPgid : Int32) : Option ProcessSysState :=
  if pidOrNegPgid == Int32.minValue || pidOrNegPgid == 0 then
    none
  else if pidOrNegPgid > 0 then
    autoreapSinglePidEsrch? s pidOrNegPgid.toUInt32
  else if pidOrNegPgid == -1 then
    let selfPid := effectiveSelfPid s
    let ctrlSubTgids := collectControlledSubthreadTgids s.procs
    let groupExitSubTgids := collectGroupExitSubthreadTgids s.procs
    let isOtherLeader (pid : UInt32) (e : ProcEntry) : Bool :=
      pid != selfPid && pid > 1 && e.isLeader && e.lifecycle != .reaped && e.lifecycle != .exitDead
    let isAutoreapChild (pid : UInt32) (e : ProcEntry) : Bool :=
      e.isChildLeader && canAutoreapEntry ctrlSubTgids groupExitSubTgids pid e
    if anyActiveProc s.procs isOtherLeader && allActiveProcWhere s.procs isOtherLeader isAutoreapChild then
      some (reapActiveLeadersWhere s isOtherLeader)
    else
      none
  else
    autoreapGroupEsrch? s (UInt32.ofNat (-pidOrNegPgid.toInt).toNat)

/-- Remove non-leader thread `tid` from `s.procs`, preserving its `AliveState` on `leaderPid` so `waitpid` retains `synchronize_group_exit` outcomes. -/
def reapNonLeaderSubthread (s : ProcessSysState) (tid leaderPid : UInt32) (entry : ProcEntry) : ProcessSysState :=
  let procs1 := assocEraseAll s.procs tid
  let procs2 :=
    match entry.lifecycle, assocGet procs1 leaderPid with
    | .alive a, some leader =>
      assocSet procs1 leaderPid { leader with reapedSubthreads := a :: leader.reapedSubthreads }
    | _, _ =>
      procs1
  { s with procs := procs2 }

/-- Prune non-leader thread `tid` when `ESRCH` indicates an uncontrolled or dying thread/group may have exited independently. -/
def nonLeaderEsrch? (s : ProcessSysState) (tid : UInt32) : Option ProcessSysState :=
  let selfPid := effectiveSelfPid s
  if tid == 0 || tid > maxLinuxPid || tid == selfPid then
    none
  else
    match assocGet s.procs tid with
    | some entry =>
      match entry.role with
      | .thread leaderPid =>
        if entry.lifecycle == .reaped || entry.lifecycle == .exitDead then
          none
        else
          let threadControlled :=
            match entry.lifecycle with
            | .alive a => a.auto == .controlled && !a.canDeliverFatal
            | _ => false
          let leaderDyingOrUncontrolled :=
            if leaderPid == selfPid then false
            else match assocGet s.procs leaderPid with
            | none => true
            | some leader =>
              isEntryUncontrolledOrDying leader ||
                match leader.lifecycle with
                | .alive a => a.run == .running && hasGroupExitSubthread s.procs leaderPid
                | .delayedZombie _ _ _ run _ _ _ _ _ _ => run == .running && hasGroupExitSubthread s.procs leaderPid
                | _ => false
          if !threadControlled || leaderDyingOrUncontrolled then
            some (reapNonLeaderSubthread s tid leaderPid entry)
          else
            none
      | _ => none
    | none => none

/-- Returns `true` iff `leaderPid` has an active subthread whose `AliveState` allows exiting normally with `code`. -/
def hasSubthreadAllowingExited (procs : List (UInt32 × ProcEntry)) (leaderPid : UInt32) (code : UInt8) : Bool :=
  anyActiveProc procs fun _ e =>
    match e.role, e.lifecycle with
    | .thread tgid, .alive a => tgid == leaderPid && a.allowsExited code
    | _, _ => false

/-- Returns `true` iff `leaderPid` has an active subthread whose `AliveState` allows terminating with `(sig, core)`. -/
def hasSubthreadAllowingSignaled (procs : List (UInt32 × ProcEntry)) (leaderPid : UInt32)
    (sig : UInt32) (core : Bool) : Bool :=
  anyActiveProc procs fun _ e =>
    match e.role, e.lifecycle with
    | .thread tgid, .alive a => tgid == leaderPid && a.allowsSignaled sig core
    | _, _ => false

/-- Returns `true` iff `leaderPid` has a running `.arbitrary` subthread that may stop its thread group autonomously. -/
def hasArbitraryRunningSubthread (procs : List (UInt32 × ProcEntry)) (leaderPid : UInt32) : Bool :=
  anyActiveProc procs fun _ e =>
    match e.role, e.lifecycle with
    | .thread tgid, .alive a => tgid == leaderPid && a.run == .running && a.auto == .arbitrary
    | _, _ => false

/-- Single source of truth for what `WaitResult` is valid for one child `(cPid, entry)` and its next state. -/
def waitChildStep (s : ProcessSysState) (cPid : UInt32) (entry : ProcEntry)
    (flags : WaitFlags) (res : WaitResult) : Option ProcessSysState :=
  match res with
  | .stillRunning => none
  | .exited rPid code =>
    if rPid != cPid then none
    else
      match entry.lifecycle with
      | .zombie (.exited zCode) =>
        if code == zCode then some (reapThreadGroup s cPid) else none
      | .delayedZombie z k ts run _ _ exitReap race _ _ =>
        let zExMatch : Bool :=
          match z with
          | .exited zCode => code == zCode
          | _ => false
        let codeMatch : Bool :=
          zExMatch || hasSubthreadAllowingExited s.procs cPid code ||
          entry.reapedSubthreads.any (fun a => a.allowsExited code)
        let hasGroupExit := delayedZombieCanDeliverFatal k ts run
        if exitReap != .autoreapOnly && (k || run == .running) &&
           (!hasControlledLiveSubthread s.procs cPid || hasGroupExit) &&
           (if !hasGroupExit then codeMatch else race && codeMatch) then
          some (reapThreadGroup s cPid)
        else
          none
      | .alive a =>
        let leaderOk := a.mayZombie && a.allowsExited code
        let subCodeMatch :=
          hasSubthreadAllowingExited s.procs cPid code ||
          entry.reapedSubthreads.any (fun sub => sub.allowsExited code)
        let hasGroupFatal := a.canDeliverGroupFatal
        let subOk :=
          a.exitReap != .autoreapOnly && (a.pending.killed || a.run == .running) &&
          (if !hasGroupFatal then subCodeMatch else a.subExitedRace && subCodeMatch)
        if leaderOk || subOk then some (reapThreadGroup s cPid) else none
      | _ => none
  | .signaled rPid sig core =>
    if rPid != cPid || !(1 ≤ sig && sig ≤ 126) then none
    else
      match entry.lifecycle with
      | .zombie (.signaled zSig zCore) =>
        if sig == normalizeWaitSig zSig && core == zCore then some (reapThreadGroup s cPid) else none
      | .delayedZombie z k ts run _ _ exitReap race _ _ =>
        let zMatch : Bool :=
          match z with
          | .signaled zSig zCore => sig == normalizeWaitSig zSig && core == zCore
          | _ => false
        let zOrSubMatch : Bool :=
          zMatch || hasSubthreadAllowingSignaled s.procs cPid sig core ||
          entry.reapedSubthreads.any (fun a => a.allowsSignaled sig core)
        let sigMatch : Bool :=
          (k && sig == 9 && !core) || (ts.contains sig && (!core || isCoreDefaultSignal sig))
        let hasGroupExit := delayedZombieCanDeliverFatal k ts run
        if exitReap != .autoreapOnly && (k || run == .running) &&
           (!hasControlledLiveSubthread s.procs cPid || hasGroupExit) &&
           (if !hasGroupExit then zOrSubMatch else sigMatch || (race && zOrSubMatch)) then
          some (reapThreadGroup s cPid)
        else
          none
      | .alive a =>
        let leaderOk := a.mayZombie && a.allowsSignaled sig core
        let subSigMatch :=
          hasSubthreadAllowingSignaled s.procs cPid sig core ||
          entry.reapedSubthreads.any (fun sub => sub.allowsSignaled sig core)
        let hasGroupFatal := a.canDeliverGroupFatal
        let subOk :=
          a.exitReap != .autoreapOnly && (a.pending.killed || a.run == .running) &&
          (if !hasGroupFatal then subSigMatch else a.subExitedRace && subSigMatch)
        if leaderOk || subOk then some (reapThreadGroup s cPid) else none
      | _ => none
  | .stopped rPid stopSig =>
    if rPid != cPid || !(flags.untraced && 1 ≤ stopSig && stopSig ≤ 126) then none
    else
      match entry.lifecycle with
      | .alive a =>
        let stopAllowed : Bool :=
          match a.run with
          | .stopped rawSig false => stopSig == normalizeWaitSig rawSig
          | .running =>
            !a.pending.killed &&
            (a.pending.stopSigs.contains stopSig || a.pending.racedTtyStops.contains stopSig ||
             a.auto == .arbitrary || hasArbitraryRunningSubthread s.procs cPid)
          | _ => false
        if stopAllowed then
          some (setProcLifecycle s cPid entry
            (.alive { a with run := .stopped stopSig true, cont := .none, subExitedRace := false,
                             pending := { a.pending with stopSigs := [], racedTtyStops := [] } }))
        else
          none
      | .delayedZombie z k ts run _ ss exitReap _ ds rs =>
        let stopAllowed : Bool :=
          match run with
          | .stopped rawSig false => stopSig == normalizeWaitSig rawSig
          | .running =>
            !k && (ss.contains stopSig || rs.contains stopSig ||
                   hasArbitraryRunningSubthread s.procs cPid)
          | _ => false
        if hasActiveSubthread s.procs cPid && stopAllowed then
          some (setProcLifecycle s cPid entry
            (.delayedZombie z k ts (.stopped stopSig true) .none [] exitReap false ds []))
        else
          none
      | _ => none
  | .continued rPid =>
    if rPid != cPid || !flags.continued then none
    else
      match entry.lifecycle with
      | .alive a =>
        if a.run == .running && !a.pending.killed && a.cont != .none then
          some (setProcLifecycle s cPid entry (.alive { a with cont := .none }))
        else
          none
      | .delayedZombie z k ts run cont ss exitReap race ds rs =>
        if hasActiveSubthread s.procs cPid && run == .running && !k && cont != .none then
          some (setProcLifecycle s cPid entry
            (.delayedZombie z k ts .running .none ss exitReap race ds rs))
        else
          none
      | _ => none

/-- Check whether one child entry `(cPid, entry)` already has a confirmed waitable event given precomputed subthread sets. -/
def hasConfirmedWaitableEntrySet (activeSubTgids ctrlSubTgids groupExitSubTgids : Std.TreeSet UInt32 compare)
    (cPid : UInt32) (entry : ProcEntry) (flags : WaitFlags) : Bool :=
  match entry.lifecycle with
  | .zombie _ => true
  | .delayedZombie _ k ts run cont _ exitReap _ _ _ =>
    if activeSubTgids.contains cPid then
      match run with
      | .stopped _ false => flags.untraced
      | .running =>
        flags.continued && cont == .confirmed &&
        !delayedZombieCanDeliverFatal k ts run &&
        isHeldByControlledSubthreadSet ctrlSubTgids groupExitSubTgids cPid
      | _ => false
    else
      exitReap == .zombieOnly && (k || run == .running)
  | .alive a =>
    match a.run with
    | .stopped _ false => flags.untraced
    | .running =>
      flags.continued && a.cont == .confirmed &&
      !a.canDeliverFatal && !groupExitSubTgids.contains cPid
    | _ => false
  | _ => false

/-- Tail-recursive scan checking whether `matching` contains any confirmed waitable child using precomputed subthread sets. -/
def hasConfirmedWaitableWithSet (activeSubTgids ctrlSubTgids groupExitSubTgids : Std.TreeSet UInt32 compare)
    (matching : List (UInt32 × ProcEntry)) (flags : WaitFlags) : Bool :=
  match matching with
  | [] => false
  | (cPid, entry) :: rest =>
    if hasConfirmedWaitableEntrySet activeSubTgids ctrlSubTgids groupExitSubTgids cPid entry flags then true
    else hasConfirmedWaitableWithSet activeSubTgids ctrlSubTgids groupExitSubTgids rest flags

/-- Check whether one child entry `(cPid, entry)` already has a confirmed waitable event. -/
def hasConfirmedWaitableEntry (procs : List (UInt32 × ProcEntry)) (cPid : UInt32)
    (entry : ProcEntry) (flags : WaitFlags) : Bool :=
  hasConfirmedWaitableEntrySet (collectActiveSubthreadTgids procs)
    (collectControlledSubthreadTgids procs) (collectGroupExitSubthreadTgids procs) cPid entry flags

/-- Returns `true` iff `matching` contains at least one child whose waitable event is already confirmed. -/
def hasConfirmedWaitable (procs : List (UInt32 × ProcEntry))
    (matching : List (UInt32 × ProcEntry)) (flags : WaitFlags) : Bool :=
  hasConfirmedWaitableWithSet (collectActiveSubthreadTgids procs)
    (collectControlledSubthreadTgids procs) (collectGroupExitSubthreadTgids procs) matching flags

/-- Relational step checker for a decoded `WaitResult` when `matching` is non-empty. -/
def allowedStepWaitResult (s : ProcessSysState) (matching : List (UInt32 × ProcEntry))
    (flags : WaitFlags) (res : WaitResult) : Option ProcessSysState :=
  match res with
  | .stillRunning =>
    if flags.nohang && !hasConfirmedWaitable s.procs matching flags then some s else none
  | .exited rPid _ | .signaled rPid _ _ | .stopped rPid _ | .continued rPid =>
    match assocGet matching rPid with
    | none => none
    | some entry => waitChildStep s rPid entry flags res

/-- Select an immediately waitable `WaitResult` for a single child `(cPid, entry)`, if any. -/
def pickImmediateWaitStep (activeSubTgids : Std.TreeSet UInt32 compare)
    (cPid : UInt32) (entry : ProcEntry) (flags : WaitFlags) : Option WaitResult :=
  match entry.lifecycle with
  | .zombie z => some (z.toWaitResult cPid)
  | .delayedZombie z k ts run cont ss exitReap _ _ _ =>
    if activeSubTgids.contains cPid then
      match run with
      | .stopped rawSig false =>
        if flags.untraced then some (.stopped cPid (normalizeWaitSig rawSig)) else none
      | .running =>
        if flags.untraced && !k then
          match ss.find? (fun sig => 1 ≤ sig && sig ≤ 126) with
          | some sig => some (.stopped cPid sig)
          | none =>
            if flags.continued && cont != .none then
              some (.continued cPid)
            else
              none
        else if flags.continued && !k && cont != .none then
          some (.continued cPid)
        else
          none
      | _ => none
    else
      if !(exitReap != .autoreapOnly && (k || run == .running)) then
        none
      else if k then
        some (.signaled cPid 9 false)
      else
        match firstValidTermSig? ts with
        | some sig => some (.signaled cPid sig false)
        | none => some (z.toWaitResult cPid)
  | .alive a =>
    match a.run with
    | .stopped rawSig false =>
      if flags.untraced then some (.stopped cPid (normalizeWaitSig rawSig)) else none
    | .running =>
      if flags.untraced && !a.pending.killed then
        match a.pending.stopSigs.find? (fun sig => 1 ≤ sig && sig ≤ 126) with
        | some sig => some (.stopped cPid sig)
        | none =>
          if flags.continued && a.cont != .none then
            some (.continued cPid)
          else if a.mayZombie then
            a.pending.termSigs.find? (fun sig => 1 ≤ sig && sig ≤ 126) |>.map fun sig => .signaled cPid sig false
          else
            none
      else if flags.continued && !a.pending.killed && a.cont != .none then
        some (.continued cPid)
      else if a.mayZombie then
        if a.pending.killed then
          some (.signaled cPid 9 false)
        else
          a.pending.termSigs.find? (fun sig => 1 ≤ sig && sig ≤ 126) |>.map fun sig => .signaled cPid sig false
      else
        none
    | _ => none
  | _ => none

/-- Select the first immediately waitable candidate `WaitResult` in `matching` for deterministic `modelOps`. -/
def pickImmediateWaitResultSet (activeSubTgids : Std.TreeSet UInt32 compare)
    (matching : List (UInt32 × ProcEntry)) (flags : WaitFlags) : Option WaitResult :=
  match matching with
  | [] => none
  | (cPid, entry) :: rest =>
    match pickImmediateWaitStep activeSubTgids cPid entry flags with
    | some w => some w
    | none => pickImmediateWaitResultSet activeSubTgids rest flags

/-- Select the first immediately waitable candidate `WaitResult` in `matching` for deterministic `modelOps`. -/
def pickImmediateWaitResult (procs : List (UInt32 × ProcEntry))
    (matching : List (UInt32 × ProcEntry)) (flags : WaitFlags) : Option WaitResult :=
  pickImmediateWaitResultSet (collectActiveSubthreadTgids procs) matching flags

/-- Select a deterministic group-exit `WaitResult` from one subthread `AliveState` on leader `cPid`, if any. -/
def pickAliveAutoExit? (cPid : UInt32) (sub : AliveState) : Option WaitResult :=
  if sub.pending.killed then
    some (.signaled cPid 9 false)
  else if sub.run == .running then
    match firstValidTermSig? sub.pending.termSigs with
    | some sig => some (.signaled cPid sig false)
    | none =>
      match sub.auto with
      | .planned z => some (z.toWaitResult cPid)
      | .arbitrary => some (.exited cPid 0)
      | .controlled => none
  else
    none

/-- Tail-recursive scan selecting a deterministic group-exit `WaitResult` from active subthreads of `cPid`. -/
def pickActiveSubthreadAutoExitGo (procs : List (UInt32 × ProcEntry))
    (seen : Std.TreeSet UInt32 compare) (cPid : UInt32) : Option WaitResult :=
  match procs with
  | [] => none
  | (pid, e) :: rest =>
    if seen.contains pid then
      pickActiveSubthreadAutoExitGo rest seen cPid
    else
      match e.role, e.lifecycle with
      | .thread tgid, .alive sub =>
        if tgid == cPid then
          match pickAliveAutoExit? cPid sub with
          | some w => some w
          | none => pickActiveSubthreadAutoExitGo rest (seen.insert pid) cPid
        else
          pickActiveSubthreadAutoExitGo rest (seen.insert pid) cPid
      | _, _ =>
        pickActiveSubthreadAutoExitGo rest (seen.insert pid) cPid

/-- Select a deterministic group-exit `WaitResult` from active or `ESRCH`-pruned subthreads of `(cPid, reapedSubs)`. -/
def pickSubthreadAutoExit? (procs : List (UInt32 × ProcEntry))
    (cPid : UInt32) (reapedSubs : List AliveState) : Option WaitResult :=
  match pickActiveSubthreadAutoExitGo procs {} cPid with
  | some w => some w
  | none => reapedSubs.findSome? (pickAliveAutoExit? cPid)

/-- Select the first running or group-exiting child for blocking `waitpid` using precomputed `ctrlSubTgids` and `groupExitSubTgids`. -/
def pickBlockingAutoExitSet (procs : List (UInt32 × ProcEntry))
    (ctrlSubTgids groupExitSubTgids : Std.TreeSet UInt32 compare)
    (matching : List (UInt32 × ProcEntry)) : Option WaitResult :=
  match matching with
  | [] => none
  | (cPid, entry) :: rest =>
    match entry.lifecycle with
    | .delayedZombie z k ts run _ _ exitReap _ _ _ =>
      if exitReap != .autoreapOnly && (k || run == .running) then
        if k then
          some (.signaled cPid 9 false)
        else
          match firstValidTermSig? ts with
          | some sig => some (.signaled cPid sig false)
          | none =>
            if !isHeldByControlledSubthreadSet ctrlSubTgids groupExitSubTgids cPid then some (z.toWaitResult cPid)
            else pickBlockingAutoExitSet procs ctrlSubTgids groupExitSubTgids rest
      else
        pickBlockingAutoExitSet procs ctrlSubTgids groupExitSubTgids rest
    | .alive a =>
      if a.run == .running && a.exitReap != .autoreapOnly then
        match a.auto with
        | .planned z => some (z.toWaitResult cPid)
        | .arbitrary => some (.exited cPid 0)
        | .controlled =>
          if !a.canDeliverGroupFatal then
            match pickSubthreadAutoExit? procs cPid entry.reapedSubthreads with
            | some w => some w
            | none => pickBlockingAutoExitSet procs ctrlSubTgids groupExitSubTgids rest
          else
            pickBlockingAutoExitSet procs ctrlSubTgids groupExitSubTgids rest
      else
        pickBlockingAutoExitSet procs ctrlSubTgids groupExitSubTgids rest
    | _ => pickBlockingAutoExitSet procs ctrlSubTgids groupExitSubTgids rest

/-- Select the first running or group-exiting child for blocking `waitpid`. -/
def pickBlockingAutoExit (procs : List (UInt32 × ProcEntry)) (matching : List (UInt32 × ProcEntry)) : Option WaitResult :=
  pickBlockingAutoExitSet procs (collectControlledSubthreadTgids procs) (collectGroupExitSubthreadTgids procs) matching

/-- Deterministic `waitpid` transition used by `modelOps`, sharing `allowedStepWaitResult` and `autoReapEchildState`. -/
def evalModelWaitpid (s : ProcessSysState) (pid : Int32) (flags : WaitFlags) :
    Except Errno WaitResult × ProcessSysState :=
  if !flags.isValid then
    (.error Errno.EINVAL, s)
  else if pid == Int32.minValue then
    (.error Errno.ESRCH, s)
  else
    let matching := matchingUnreapedChildren s pid flags
    if matching.isEmpty then
      (.error Errno.ECHILD, s)
    else
      match pickImmediateWaitResult s.procs matching flags with
      | some wres =>
        (.ok wres, (allowedStepWaitResult s matching flags wres).getD s)
      | none =>
        if s.sigchld == .autoreap && allAutoreapable s.procs matching then
          (.error Errno.ECHILD, if s.ambientSeccomp then s else (autoReapEchildState s matching).getD s)
        else if flags.nohang then
          (.ok .stillRunning, s)
        else
          match pickBlockingAutoExit s.procs matching with
          | some wres => (.ok wres, (allowedStepWaitResult s matching flags wres).getD s)
          | none => (.error Errno.EINTR, s)

/-- Relational step checker for `ProcessReq.waitpid` (assumes `validateReqBeforeKernel` is `none`). -/
def allowedStepWaitpid (s : ProcessSysState) (pid : Int32) (flags : WaitFlags)
    (out : ProcessOutcome) : Option ProcessSysState :=
  if !flags.isValid then
    match out with
    | .err code =>
      if code == Errno.EINVAL || isKernelNonFdTransient code ||
         (s.ambientSeccomp && isSeccompSynthesizableErrno code) then some s
      else none
    | _ => none
  else if pid == Int32.minValue then
    match out with
    | .err code =>
      if code == Errno.ESRCH || isKernelNonFdTransient code ||
         (s.ambientSeccomp && isSeccompSynthesizableErrno code) then some s
      else none
    | _ => none
  else
    let matching := matchingUnreapedChildren s pid flags
    if matching.isEmpty then
      match out with
      | .err code =>
        if code == Errno.ECHILD || isKernelNonFdTransient code ||
           (s.ambientSeccomp && isSeccompSynthesizableErrno code) then some s
        else none
      | _ => none
    else
      match out with
      | .err code =>
        if isKernelNonFdTransient code then
          some s
        else if s.ambientSeccomp && isSeccompSynthesizableErrno code then
          some s
        else if code == Errno.ECHILD then
          autoReapEchildState s matching
        else
          none
      | .waited res =>
        allowedStepWaitResult s matching flags res
      | _ => none

/-- Look up whether `pid` (or its thread-group leader) is currently in `.exitDead`, returning `(isLeader, canSignal, sameSession)`. -/
def exitDeadSingleTarget? (s : ProcessSysState) (pid : UInt32) : Option (Bool × Bool × Bool) :=
  let selfPid := effectiveSelfPid s
  if pid == 0 || pid > maxLinuxPid || pid == selfPid then
    none
  else
    match assocGet s.procs pid with
    | none => none
    | some entry =>
      match entry.role with
      | .thread leaderPid =>
        if leaderPid == selfPid then
          none
        else
          match assocGet s.procs leaderPid with
          | none =>
            if entry.lifecycle == .exitDead then some (false, entry.canSignal, entry.sameSession) else none
          | some leader =>
            if entry.lifecycle == .exitDead || leader.lifecycle == .exitDead then
              some (false, leader.canSignal, leader.sameSession)
            else
              none
      | _ =>
        if entry.lifecycle == .exitDead then some (true, entry.canSignal, entry.sameSession) else none

/-- Check whether `out` is a valid transient signal outcome (`unit` / `EINVAL` / `EPERM`) given `(canSignal, sameSession)` when `expectedErr == ESRCH`. -/
def transientSingleSignalOutcomeAllowed (canSig sameSess : Bool) (sig : Signal) (out : ProcessOutcome) : Bool :=
  let canSigEff := canSig || (sig.toLinuxNum == 18 && sameSess)
  match out with
  | .unit => sig.isValid && canSigEff
  | .err code =>
    if !sig.isValid then code == Errno.EINVAL
    else if !canSigEff then code == Errno.EPERM || code == Errno.EACCES
    else false
  | _ => false

/-- Check whether `out` is a valid `EXIT_DEAD` pre-`__unhash_process` signal outcome over a predicate matching `.exitDead` leaders. -/
def exitDeadGroupSignalAllowed (s : ProcessSysState) (pred : UInt32 → ProcEntry → Bool)
    (expectedErr : Errno) (sig : Signal) (out : ProcessOutcome) : Bool :=
  if sig.isNptlReserved || !anyActiveProc s.procs pred then
    false
  else if expectedErr == Errno.ESRCH then
    match out with
    | .unit => sig.isValid && anyActiveProc s.procs (fun pid e => pred pid e && canSignalEntry sig e)
    | .err code =>
      if !sig.isValid then
        code == Errno.EINVAL
      else if !anyActiveProc s.procs (fun pid e => pred pid e && canSignalEntry sig e) then
        code == Errno.EPERM || code == Errno.EACCES
      else
        false
    | _ => false
  else if expectedErr == Errno.EPERM then
    match out with
    | .unit => sig.isValid && anyActiveProc s.procs (fun pid e => pred pid e && canSignalEntry sig e)
    | _ => false
  else
    false

/-- Check whether `out` is a valid `EXIT_DEAD` pre-`__unhash_process` outcome for `kill(pidOrNegPgid, sig)`. -/
def exitDeadKillAllowed (s : ProcessSysState) (pidOrNegPgid : Int32) (expectedErr : Errno)
    (sig : Signal) (out : ProcessOutcome) : Bool :=
  if sig.isNptlReserved || pidOrNegPgid == Int32.minValue then
    false
  else if pidOrNegPgid > 0 then
    if expectedErr != Errno.ESRCH then
      false
    else
      match exitDeadSingleTarget? s pidOrNegPgid.toUInt32 with
      | some (_, canSig, sameSess) => transientSingleSignalOutcomeAllowed canSig sameSess sig out
      | none => false
  else
    let selfPid := effectiveSelfPid s
    let selfPgid := effectiveSelfPgid s
    if pidOrNegPgid == -1 then
      let pred (pid : UInt32) (e : ProcEntry) : Bool :=
        pid != selfPid && pid > 1 && e.isLeader && e.lifecycle == .exitDead
      if expectedErr != Errno.ESRCH || !anyActiveProc s.procs pred then
        false
      else
        match out with
        | .unit => sig.isValid
        | .err code =>
          if !sig.isValid then code == Errno.EINVAL
          else code == Errno.EACCES && !anyActiveProc s.procs (fun pid e => pred pid e && canSignalEntry sig e)
        | _ => false
    else
      let targetPgid : UInt32 :=
        if pidOrNegPgid == 0 then selfPgid else UInt32.ofNat (-pidOrNegPgid.toInt).toNat
      let pred (pid : UInt32) (e : ProcEntry) : Bool :=
        pid != selfPid && e.isLeader && e.lifecycle == .exitDead && e.pgid == targetPgid
      exitDeadGroupSignalAllowed s pred expectedErr sig out

/-- Reap an `.exitDead` single target (or thread group) once `ESRCH` confirms `__unhash_process` completed. -/
def reapExitDeadSingleTarget (s : ProcessSysState) (pid : UInt32) : ProcessSysState :=
  let selfPid := effectiveSelfPid s
  if pid == 0 || pid > maxLinuxPid || pid == selfPid then
    s
  else
    match assocGet s.procs pid with
    | none => s
    | some entry =>
      match entry.role with
      | .thread leaderPid =>
        if entry.lifecycle == .exitDead then reapSingleProc s pid
        else
          match assocGet s.procs leaderPid with
          | some leader => if leader.lifecycle == .exitDead then reapThreadGroup s leaderPid else s
          | none => s
      | _ =>
        if entry.lifecycle == .exitDead then reapThreadGroup s pid else s

/-- Reap every `.exitDead` leader matching `pred` once `ESRCH` confirms `__unhash_process` completed. -/
def reapExitDeadGroup (s : ProcessSysState) (pred : UInt32 → ProcEntry → Bool) : ProcessSysState :=
  reapActiveLeadersWhere s (fun pid e => pred pid e && e.lifecycle == .exitDead)

/-- Shared post-`ESRCH` state transition for `pidfd_open`. -/
def esrchPidfdOpenNext (s : ProcessSysState) (pid : UInt32) (flags : PidfdOpenFlags) : ProcessSysState :=
  let flagsValidKernel := flags.isValid && (!flags.thread || s.pidfdThreadSupported)
  if !s.ambientSeccomp && flagsValidKernel then
    let s1 := reapExitDeadSingleTarget s pid
    (nonLeaderEsrch? s1 pid).getD s1
  else
    s

/-- Shared post-`ESRCH` state transition for `kill`. -/
def esrchKillNext (s : ProcessSysState) (pidOrNegPgid : Int32) : ProcessSysState :=
  if !s.ambientSeccomp then
    if pidOrNegPgid > 0 then
      let targetPid := pidOrNegPgid.toUInt32
      let s1 := reapExitDeadSingleTarget s targetPid
      (nonLeaderEsrch? s1 targetPid).getD s1
    else if pidOrNegPgid == -1 then
      let selfPid := effectiveSelfPid s
      reapExitDeadGroup s fun pid e => pid != selfPid && pid > 1 && e.isLeader
    else if pidOrNegPgid < -1 && pidOrNegPgid != Int32.minValue then
      let selfPid := effectiveSelfPid s
      let tpg := UInt32.ofNat (-pidOrNegPgid.toInt).toNat
      reapExitDeadGroup s fun pid e => pid != selfPid && e.isLeader && e.pgid == tpg
    else
      s
  else
    s

/-- Shared post-`ESRCH` state transition for `pidfd_send_signal`. -/
def esrchPidfdSendNext (s : ProcessSysState) (hid : HandleId) (flags : PidfdSignalFlags) : ProcessSysState :=
  if !s.ambientSeccomp then
    match assocGet s.fds hid with
    | some (.pidfd targetPid _ _) =>
      if flags.processGroup then
        let selfPid := effectiveSelfPid s
        reapExitDeadGroup s fun pid e => pid != selfPid && e.isLeader && e.pgid == targetPid
      else
        let s1 := reapExitDeadSingleTarget s targetPid
        (nonLeaderEsrch? s1 targetPid).getD s1
    | _ => s
  else
    s

/-- Returns `true` iff `pid` is a non-leader thread whose thread-group leader may have died asynchronously (`canDeliverFatal`). -/
def hasDyingNonLeaderLeader (s : ProcessSysState) (pid : UInt32) : Bool :=
  (nonLeaderEsrch? s pid).isSome

/-- Relational step checker for `ProcessReq.pidfd_open` (assumes `validateReqBeforeKernel` is `none`). -/
def allowedStepPidfdOpen (s : ProcessSysState) (pid : UInt32) (flags : PidfdOpenFlags)
    (out : ProcessOutcome) : Option ProcessSysState :=
  let selfPid := effectiveSelfPid s
  let flagsValidKernel := flags.isValid && (!flags.thread || s.pidfdThreadSupported)
  let validPid := 1 ≤ pid && pid ≤ maxLinuxPid
  let isUntrackedHostPid : Bool :=
    !s.closedPidNamespace && flagsValidKernel && validPid && pid != selfPid && (assocGet s.procs pid).isNone
  let exitDeadTarget := if flagsValidKernel then exitDeadSingleTarget? s pid else none
  let dyingNonLeader := if flagsValidKernel then hasDyingNonLeaderLeader s pid else false
  let exitDeadCanOpen : Bool :=
    match exitDeadTarget with
    | some (isLeader, _, _) => isLeader || flags.thread
    | none => false
  let exitDeadNonLeaderNoThread : Bool :=
    match exitDeadTarget with
    | some (isLeader, _, _) => !isLeader && !flags.thread
    | none => false
  match checkPidfdOpenTarget s pid flags with
  | .error expectedErr =>
    let mayAllocateFd : Bool :=
      isUntrackedHostPid || exitDeadCanOpen || (dyingNonLeader && flags.thread)
    match out with
    | .err code =>
      if code == expectedErr then
        some (if expectedErr == Errno.ESRCH then esrchPidfdOpenNext s pid flags else s)
      else if s.ambientSeccomp && isSeccompSynthesizableErrno code then
        some s
      else if expectedErr == Errno.ENOENT && !s.pidfdThreadSupported && code == Errno.EINVAL then
        some s
      else if expectedErr == Errno.ENOENT && code == Errno.ESRCH then
        nonLeaderEsrch? s pid
      else if expectedErr == Errno.ESRCH &&
              (exitDeadNonLeaderNoThread || (dyingNonLeader && !flags.thread)) &&
              (code == Errno.ENOENT || (!s.pidfdThreadSupported && code == Errno.EINVAL)) then
        some s
      else if isUntrackedHostPid && (code == Errno.ENOENT || (!s.pidfdThreadSupported && code == Errno.EINVAL)) then
        some s
      else if (if mayAllocateFd then isKernelFdAllocTransient code else isKernelNonFdTransient code) then
        some s
      else
        none
    | .opened hid =>
      if isUntrackedHostPid && (assocGet s.fds hid).isNone then
        some (commitPidfd s hid pid flags.nonblock flags.thread)
      else if expectedErr == Errno.ESRCH && exitDeadCanOpen &&
              (assocGet s.fds hid).isNone then
        some (commitPidfd s hid pid flags.nonblock flags.thread)
      else if expectedErr == Errno.ESRCH && dyingNonLeader && flags.thread &&
              (assocGet s.fds hid).isNone then
        some (commitPidfd s hid pid flags.nonblock flags.thread)
      else
        none
    | _ => none
  | .ok () =>
    match out with
    | .opened hid =>
      if (assocGet s.fds hid).isNone then
        some (commitPidfd s hid pid flags.nonblock flags.thread)
      else
        none
    | .err code =>
      if s.ambientSeccomp && isSeccompSynthesizableErrno code then
        some s
      else if isKernelFdAllocTransient code then
        some s
      else if code == Errno.ESRCH then
        match autoreapSinglePidEsrch? s pid with
        | some s' => some s'
        | none => nonLeaderEsrch? s pid
      else
        none
    | _ => none

/-- Returns `true` iff `pidOrNegPgid` can target an untracked open-host process or group on `!s.closedPidNamespace`. -/
def isOpenHostKillSelector (s : ProcessSysState) (pidOrNegPgid : Int32) : Bool :=
  if s.closedPidNamespace || pidOrNegPgid == Int32.minValue || pidOrNegPgid == 0 then
    false
  else if pidOrNegPgid > 0 then
    let targetPid := pidOrNegPgid.toUInt32
    targetPid != effectiveSelfPid s && 1 ≤ targetPid && targetPid ≤ maxLinuxPid &&
    (assocGet s.procs targetPid).isNone
  else
    true

/-- Relational step checker for `ProcessReq.kill` (assumes `validateReqBeforeKernel` is `none`). -/
def allowedStepKill (s : ProcessSysState) (pidOrNegPgid : Int32) (sig : Signal)
    (out : ProcessOutcome) : Option ProcessSysState :=
  match evalKill s pidOrNegPgid sig with
  | .ok s' =>
    match out with
    | .unit => some s'
    | .err code =>
      if s.ambientSeccomp && isSeccompSynthesizableErrno code then
        some s
      else if isKernelNonFdTransient code then
        some s
      else if pidOrNegPgid == -1 && code == Errno.EACCES &&
              (!s.closedPidNamespace ||
               !anyActiveProc s.procs (fun pid e =>
                 pid != effectiveSelfPid s && pid > 1 && e.isLeader &&
                 e.lifecycle != .reaped && e.lifecycle != .exitDead && canSignalEntry sig e)) then
        some s
      else if code == Errno.ESRCH then
        match autoreapKillEsrch? s pidOrNegPgid with
        | some s' => some s'
        | none => if pidOrNegPgid > 0 then nonLeaderEsrch? s pidOrNegPgid.toUInt32 else none
      else
        none
    | _ => none
  | .error expectedErr =>
    match out with
    | .err code =>
      if code == expectedErr then
        some (if expectedErr == Errno.ESRCH then esrchKillNext s pidOrNegPgid else s)
      else if s.ambientSeccomp && isSeccompSynthesizableErrno code then
        some s
      else if isKernelNonFdTransient code then
        some s
      else if expectedErr == Errno.EPERM && code == Errno.EACCES then
        some s
      else if (expectedErr == Errno.EPERM || expectedErr == Errno.EINVAL) && code == Errno.ESRCH then
        match autoreapKillEsrch? s pidOrNegPgid with
        | some s' => some s'
        | none => if pidOrNegPgid > 0 then nonLeaderEsrch? s pidOrNegPgid.toUInt32 else none
      else if expectedErr == Errno.ESRCH && isOpenHostKillSelector s pidOrNegPgid &&
              (if !sig.isValid then code == Errno.EINVAL
               else code == Errno.EPERM || code == Errno.EACCES) then
        some s
      else if exitDeadKillAllowed s pidOrNegPgid expectedErr sig out then
        some s
      else
        none
    | .unit =>
      if sig.isValid && isOpenHostKillSelector s pidOrNegPgid &&
         (expectedErr == Errno.ESRCH || expectedErr == Errno.EPERM) then
        some s
      else if exitDeadKillAllowed s pidOrNegPgid expectedErr sig out then
        some s
      else
        none
    | _ => none

/-- Check whether `out` is a valid `EXIT_DEAD` pre-`__unhash_process` outcome for `pidfd_send_signal`. -/
def exitDeadPidfdSendAllowed (s : ProcessSysState) (hid : HandleId) (expectedErr : Errno)
    (sig : Signal) (flags : PidfdSignalFlags) (out : ProcessOutcome) : Bool :=
  if sig.isNptlReserved || !flags.isValid then
    false
  else
    match assocGet s.fds hid with
    | some (.pidfd targetPid _ _) =>
      if !(1 ≤ targetPid && targetPid ≤ maxLinuxPid) then
        false
      else if flags.processGroup then
        let selfPid := effectiveSelfPid s
        let pred (pid : UInt32) (e : ProcEntry) : Bool :=
          pid != selfPid && e.isLeader && e.lifecycle == .exitDead && e.pgid == targetPid
        exitDeadGroupSignalAllowed s pred expectedErr sig out
      else if expectedErr != Errno.ESRCH then
        false
      else
        match exitDeadSingleTarget? s targetPid with
        | some (_, canSig, sameSess) => transientSingleSignalOutcomeAllowed canSig sameSess sig out
        | none => false
    | _ => false

/-- Relational step checker for `ProcessReq.pidfd_send_signal` (assumes `validateReqBeforeKernel` is `none`). -/
def allowedStepPidfdSendSignal (s : ProcessSysState) (hid : HandleId) (sig : Signal)
    (flags : PidfdSignalFlags) (out : ProcessOutcome) : Option ProcessSysState :=
  let autoreapThis? : Option ProcessSysState :=
    match assocGet s.fds hid with
    | some (.pidfd targetPid _ _) =>
      if flags.isValid && 1 ≤ targetPid && targetPid ≤ maxLinuxPid then
        if flags.processGroup then
          autoreapGroupEsrch? s targetPid
        else
          match autoreapSinglePidEsrch? s targetPid with
          | some s' => some s'
          | none => nonLeaderEsrch? s targetPid
      else
        none
    | _ => none
  let isOpenHostSingle : Bool :=
    match assocGet s.fds hid with
    | some (.pidfd targetPid _ _) =>
      !s.closedPidNamespace && flags.isValid && !flags.processGroup &&
      1 ≤ targetPid && targetPid ≤ maxLinuxPid &&
      targetPid != effectiveSelfPid s && (assocGet s.procs targetPid).isNone
    | _ => false
  let isOpenHostGroup : Bool :=
    match assocGet s.fds hid with
    | some (.pidfd targetPid _ _) =>
      !s.closedPidNamespace && flags.isValid && flags.processGroup &&
      1 ≤ targetPid && targetPid ≤ maxLinuxPid &&
      targetPid != effectiveSelfPgid s
    | _ => false
  match evalPidfdSendSignal s hid sig flags with
  | .ok s' =>
    match out with
    | .unit => some s'
    | .err code =>
      if s.ambientSeccomp && isSeccompSynthesizableErrno code then
        some s
      else if isKernelNonFdTransient code then
        some s
      else if code == Errno.ESRCH then
        autoreapThis?
      else
        none
    | _ => none
  | .error expectedErr =>
    match out with
    | .err code =>
      if code == expectedErr then
        some (if expectedErr == Errno.ESRCH then esrchPidfdSendNext s hid flags else s)
      else if s.ambientSeccomp && isSeccompSynthesizableErrno code then
        some s
      else if isKernelNonFdTransient code then
        some s
      else if expectedErr == Errno.EPERM && code == Errno.EACCES then
        some s
      else if (expectedErr == Errno.EPERM || expectedErr == Errno.EINVAL) && code == Errno.ESRCH then
        autoreapThis?
      else if (isOpenHostSingle || isOpenHostGroup) && expectedErr == Errno.ESRCH &&
              (if !sig.isValid then code == Errno.EINVAL
               else code == Errno.EPERM || code == Errno.EACCES) then
        some s
      else if exitDeadPidfdSendAllowed s hid expectedErr sig flags out then
        some s
      else
        none
    | .unit =>
      if sig.isValid && isOpenHostSingle && expectedErr == Errno.ESRCH then
        some s
      else if sig.isValid && isOpenHostGroup &&
              (expectedErr == Errno.ESRCH || expectedErr == Errno.EPERM) then
        some s
      else if exitDeadPidfdSendAllowed s hid expectedErr sig flags out then
        some s
      else
        none
    | _ => none

/-- Relational step checker for one `(ProcessSysState, ProcessReq, ProcessOutcome)` transition on Linux `7.1.6` (`x86_64` and `aarch64`). -/
def allowedStep (s : ProcessSysState) (req : ProcessReq) (out : ProcessOutcome) : Option ProcessSysState :=
  match validateReqBeforeKernel s req with
  | some preErr =>
    match out with
    | .err code => if code == preErr then some s else none
    | _ => none
  | none =>
    match req with
    | .pipe2 flags =>
      if !flags.isValid then
        match out with
        | .err code =>
          if code == Errno.EINVAL || isKernelNonFdTransient code ||
             (s.ambientSeccomp && isSeccompSynthesizableErrno code) then some s
          else none
        | _ => none
      else if flags.notificationPipe && !s.watchQueueSupported then
        match out with
        | .err code =>
          if code == errnoENOPKG || isKernelFdAllocTransient code ||
             (s.ambientSeccomp && isSeccompSynthesizableErrno code) then some s
          else none
        | _ => none
      else
        match out with
        | .piped rHid wHid =>
          if rHid != wHid && (assocGet s.fds rHid).isNone && (assocGet s.fds wHid).isNone then
            some (commitPipeFds s rHid wHid flags)
          else
            none
        | .err code =>
          if isKernelFdAllocTransient code || (s.ambientSeccomp && isSeccompSynthesizableErrno code) then
            some s
          else
            none
        | _ => none
    | .getpid =>
      match out with
      | .u32 gotPid =>
        if gotPid == effectiveSelfPid s then some s else none
      | .err code =>
        if isKernelNonFdTransient code || (s.ambientSeccomp && isSeccompSynthesizableErrno code) then some s else none
      | _ => none
    | .getuid =>
      match out with
      | .u32 gotUid =>
        if gotUid == s.selfUid then some s else none
      | .err code =>
        if isKernelNonFdTransient code || (s.ambientSeccomp && isSeccompSynthesizableErrno code) then some s else none
      | _ => none
    | .pidfd_open pid flags =>
      allowedStepPidfdOpen s pid flags out
    | .kill pidOrNegPgid sig =>
      allowedStepKill s pidOrNegPgid sig out
    | .pidfd_send_signal hid sig flags =>
      allowedStepPidfdSendSignal s hid sig flags out
    | .waitpid pid flags =>
      allowedStepWaitpid s pid flags out

/-- Deterministic `StateM ProcessSysState` execution of `ProcessOpsM` refined by `allowedStep`. -/
def modelOps : ProcessOpsM (StateM ProcessSysState) HandleId :=
  { pipe2 := fun flags => do
      let s ← get
      if !flags.isValid then
        return .error Errno.EINVAL
      else if flags.notificationPipe && !s.watchQueueSupported then
        return .error errnoENOPKG
      else
        let rHid := nextFreeHid s.fds s.nextHid
        let wHid := rHid + 1
        set (commitPipeFds s rHid wHid flags)
        return .ok (rHid, wHid)

    waitpid := fun pid flags => do
      let s ← get
      let (res, s') := evalModelWaitpid s pid flags
      set s'
      return res

    kill := fun pidOrNegPgid sig => do
      let s ← get
      match validateReqBeforeKernel s (.kill pidOrNegPgid sig) with
      | some e => return .error e
      | none =>
        match evalKill s pidOrNegPgid sig with
        | .ok s' =>
          set s'
          return .ok ()
        | .error e =>
          set (if e == Errno.ESRCH then esrchKillNext s pidOrNegPgid else s)
          return .error e

    pidfd_open := fun pid flags => do
      let s ← get
      match checkPidfdOpenTarget s pid flags with
      | .error e =>
        set (if e == Errno.ESRCH then esrchPidfdOpenNext s pid flags else s)
        return .error e
      | .ok () =>
        let hid := nextFreeHid s.fds s.nextHid
        set (commitPidfd s hid pid flags.nonblock flags.thread)
        return .ok hid

    pidfd_send_signal := fun hid sig flags => do
      let s ← get
      match validateReqBeforeKernel s (.pidfd_send_signal hid sig flags) with
      | some e => return .error e
      | none =>
        match evalPidfdSendSignal s hid sig flags with
        | .ok s' =>
          set s'
          return .ok ()
        | .error e =>
          set (if e == Errno.ESRCH then esrchPidfdSendNext s hid flags else s)
          return .error e

    getpid := do
      let s ← get
      return .ok (effectiveSelfPid s)

    getuid := do
      let s ← get
      return .ok s.selfUid }

/-- Convert `Except Errno (HandleId × HandleId)` into `ProcessOutcome`. -/
def outcomeOfPiped : Except Errno (HandleId × HandleId) → ProcessOutcome
  | .ok (rHid, wHid) => .piped rHid wHid
  | .error e => .err e

/-- Convert `Except Errno WaitResult` into `ProcessOutcome`. -/
def outcomeOfWaited : Except Errno WaitResult → ProcessOutcome
  | .ok wr => .waited wr
  | .error e => .err e

/-- Convert `Except Errno Unit` into `ProcessOutcome`. -/
def outcomeOfUnit : Except Errno Unit → ProcessOutcome
  | .ok () => .unit
  | .error e => .err e

/-- Convert `Except Errno HandleId` into `ProcessOutcome`. -/
def outcomeOfOpened : Except Errno HandleId → ProcessOutcome
  | .ok hid => .opened hid
  | .error e => .err e

/-- Convert `Except Errno UInt32` into `ProcessOutcome`. -/
def outcomeOfU32 : Except Errno UInt32 → ProcessOutcome
  | .ok v => .u32 v
  | .error e => .err e

/-- Execute one `ProcessReq` against any `ProcessOpsM (StateM S) HandleId` bundle and package the result as a `ProcessOutcome`. -/
def execProcessReq {S : Type} (ops : ProcessOpsM (StateM S) HandleId) (req : ProcessReq) : StateM S ProcessOutcome :=
  match req with
  | .pipe2 flags => do
    return outcomeOfPiped (← ops.pipe2 flags)
  | .waitpid pid flags => do
    return outcomeOfWaited (← ops.waitpid pid flags)
  | .kill pidOrNegPgid sig => do
    return outcomeOfUnit (← ops.kill pidOrNegPgid sig)
  | .pidfd_open pid flags => do
    return outcomeOfOpened (← ops.pidfd_open pid flags)
  | .pidfd_send_signal hid sig flags => do
    return outcomeOfUnit (← ops.pidfd_send_signal hid sig flags)
  | .getpid => do
    return outcomeOfU32 (← ops.getpid)
  | .getuid => do
    return outcomeOfU32 (← ops.getuid)

/-- Non-circular raw C-ABI postcondition contract on a low-level `PosixProcessOpsM` shim against `Model.allowedStep`. -/
structure RawPosixShimSound (raw : PosixProcessOpsM (StateM ProcessSysState) HandleId) : Prop where
  /-- Low-level `pipe2` shim refines `Model.allowedStep`. -/
  pipe2_sound : ∀ s pf,
    let r := (raw.pipe2 pf.toBits).run s
    allowedStep s (.pipe2 pf) (outcomeOfPiped r.1) = some r.2
  /-- Low-level `waitpid` shim refines `Model.allowedStep`. -/
  waitpid_sound : ∀ s pid wf,
    let r := (raw.waitpid pid wf.toBits).run s
    allowedStep s (.waitpid pid wf) (outcomeOfWaited (r.1.map WaitResult.ofRawWait4)) = some r.2
  /-- Low-level `kill` shim (after NPTL-reserved signal filtering) refines `Model.allowedStep`. -/
  kill_sound : ∀ s pid sig, sig.isNptlReserved = false →
    let r := (raw.kill pid sig.toRaw.1 sig.toRaw.2).run s
    allowedStep s (.kill pid sig) (outcomeOfUnit r.1) = some r.2
  /-- Low-level `pidfd_open` shim refines `Model.allowedStep`. -/
  pidfd_open_sound : ∀ s pid pof,
    let r := (raw.pidfd_open pid pof.toBits).run s
    allowedStep s (.pidfd_open pid pof) (outcomeOfOpened r.1) = some r.2
  /-- Low-level `pidfd_send_signal` shim (after NPTL-reserved signal filtering) refines `Model.allowedStep`. -/
  pidfd_send_signal_sound : ∀ s hid sig psf, sig.isNptlReserved = false →
    let r := (raw.pidfd_send_signal hid sig.toRaw.1 sig.toRaw.2 psf.toBits).run s
    allowedStep s (.pidfd_send_signal hid sig psf) (outcomeOfUnit r.1) = some r.2
  /-- Low-level `getpid` shim refines `Model.allowedStep`. -/
  getpid_sound : ∀ s,
    let r := raw.getpid.run s
    allowedStep s .getpid (outcomeOfU32 r.1) = some r.2
  /-- Low-level `getuid` shim refines `Model.allowedStep`. -/
  getuid_sound : ∀ s,
    let r := raw.getuid.run s
    allowedStep s .getuid (outcomeOfU32 r.1) = some r.2

/-- Return `true` iff `out` is a curated catastrophic OS fault (`ENOMEM`, `EIO`, `ENFILE`). -/
def isCriticalFault : ProcessOutcome → Bool
  | .err e => Errno.isCriticalOsErrno e
  | _ => false

/-- Return `true` iff `out` is an interrupted syscall outcome (`.err Errno.EINTR`). -/
def isEintrOutcome : ProcessOutcome → Bool
  | .err e => e == Errno.EINTR
  | _ => false

/-- Healthy execution environment wrapping `ProcessSysState` with a finite `EINTR` interruption budget (`ambientSeccomp = false`). -/
structure HealthyEnv where
  /-- Underlying `Process` world state. -/
  state : ProcessSysState := ProcessSysState.initial
  /-- Remaining bound on `EINTR` signal interruptions (`0` forbids `EINTR`). -/
  eintrBudget : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Initial healthy `Process` environment with optional `eintrBudget`. -/
def HealthyEnv.initial (eintrBudget : Nat := 0) : HealthyEnv :=
  { state := ProcessSysState.initial, eintrBudget := eintrBudget }

/-- Return `true` iff `env` has no ambient `seccomp` `SECCOMP_RET_ERRNO` filter interception. -/
def HealthyEnv.wf (env : HealthyEnv) : Bool :=
  !env.state.ambientSeccomp

/-- Relational healthy-OS step checker for `LeanSwe.LinuxSyscall.Process`, excluding critical OS faults and ambient `seccomp` while bounding `EINTR` via `eintrBudget`. -/
def healthyStep (env : HealthyEnv) (req : ProcessReq) (out : ProcessOutcome) : Option HealthyEnv :=
  if !env.wf || isCriticalFault out then
    none
  else
    match allowedStep env.state req out with
    | none => none
    | some s' =>
      if isEintrOutcome out then
        if env.eintrBudget > 0 then
          some { state := s', eintrBudget := env.eintrBudget - 1 }
        else
          none
      else
        some { state := s', eintrBudget := env.eintrBudget }

/-- Universal healthy-world refinement predicate over an arbitrary state `W` projected via `proj`. -/
def RefinesHealthyProcessAt {W : Type} (proj : W → HealthyEnv)
    (ops : ProcessOpsM (StateM W) HandleId) : Prop :=
  ∀ (w : W) (req : ProcessReq),
    (proj w).wf = true →
    let (out, w') := (execProcessReq ops req).run w
    healthyStep (proj w) req out = some (proj w')

/-- Direct healthy-world refinement predicate specialized to `StateM HealthyEnv`. -/
abbrev RefinesHealthyProcess (ops : ProcessOpsM (StateM HealthyEnv) HandleId) : Prop :=
  RefinesHealthyProcessAt id ops

end LeanSwe.LinuxSyscall.Process
