import Std.Data.TreeSet
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Process.Model
import LeanSwe.LinuxSyscall.Process.Interface
import Fuzz.LinuxSyscall.Rng
import Fuzz.LinuxSyscall.ProcessEnv

namespace Fuzz.LinuxSyscall.ProcessFuzz

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Process

/-- Symbolic process-selector argument resolved dynamically against live episode children and threads. -/
inductive SymPidTarget where
  /-- Exact calling process PID (`effectiveSelfPid s`). -/
  | selfPid
  /-- Process-group selector `0` (`selfPgid`). -/
  | zero
  /-- Broadcast selector `-1`. -/
  | negOne
  /-- Literal `PID 1`. -/
  | pidOne
  /-- Literal `PID 2`. -/
  | pidTwo
  /-- Minimum signed 32-bit integer (`INT32_MIN`). -/
  | intMin
  /-- Negated calling process group (`-selfPgid`). -/
  | negSelfPgid
  /-- Active or historical spawned child at index `idx`. -/
  | childPid (idx : Nat)
  /-- Negated process group of spawned child at index `idx`. -/
  | negChildPgid (idx : Nat)
  /-- Spawned helper thread TID (in self or child) at index `idx`. -/
  | threadTid (idx : Nat)
  /-- Non-leader thread TID sampled from an open-host `/proc/<pid>/task/<tid>` entry at index `idx`. -/
  | hostThreadTid (idx : Nat)
  /-- Untracked positive PID value `v`. -/
  | untracked (v : UInt32)
  deriving Repr, DecidableEq

/-- Symbolic descriptor reference resolved dynamically against open and closed handles in the episode. -/
inductive SymFdTarget where
  /-- Currently open `pidfd` at index `idx`. -/
  | openPidfd (idx : Nat)
  /-- Currently open pipe descriptor at index `idx` (tests `EBADF` on non-pidfd). -/
  | openPipe (idx : Nat)
  /-- Previously closed descriptor at index `idx` (tests `EBADF` on closed `LeanFdBox`). -/
  | closedFd (idx : Nat)
  /-- Unregistered fallback pipe descriptor when no other descriptor is selected. -/
  | fallbackClosed
  deriving Repr, DecidableEq

/-- Kind of OS helper process or thread spawned inside an episode. -/
inductive SpawnKind where
  /-- Controlled sleeping child (`pause()`). -/
  | controlled
  /-- Autonomous child exiting with `exitCode` after `delayUs` microseconds. -/
  | autonomous (delayUs : UInt32) (exitCode : UInt8)
  /-- Stopped child pre-synchronized via `waitid(WSTOPPED | WNOWAIT)`. -/
  | stopped (stopSig : UInt32)
  /-- Pre-terminated zombie via `_exit(exitCode)`. -/
  | zombieExit (exitCode : UInt8)
  /-- Pre-terminated zombie via signal `termSig` (`allowCore` controls `RLIMIT_CORE`). -/
  | zombieSig (termSig : UInt32) (allowCore : Bool)
  /-- Non-leader POSIX helper thread in the current process. -/
  | thread
  /-- `clone(..., 0)` child (`__WCLONE`, non-`SIGCHLD` exit signal), sleeping. -/
  | cloneControlled
  /-- `clone(..., 0)` immediate-exit zombie (`__WCLONE`, non-`SIGCHLD`). -/
  | cloneZombie (exitCode : UInt8)
  /-- Controlled child process containing a live non-leader kernel worker thread. -/
  | threadedChild
  /-- Delayed-zombie child whose leader called `SYS_exit(exitCode)` while a non-leader worker thread sleeps (`subDelayUs = 0` pauses; `> 0` exits with `subExitCode`). -/
  | delayedZombie (exitCode : UInt8) (subDelayUs : UInt32 := 0) (subExitCode : UInt8 := exitCode)
  /-- Persistent sibling thread that forks a controlled child (`fromSiblingThread = true` for `__WNOTHREAD`). -/
  | siblingChild
  /-- Orphaned grandchild reparented directly to caller when `subreaper` or `PID 1`. -/
  | reparentedGrandchild
  deriving Repr, DecidableEq

/-- Symbolic action executed during a fuzz episode and preserved verbatim across delta-shrinking. -/
inductive FuzzAction where
  /-- Configure `SIGCHLD` disposition (`0..4`: `DFL`, `IGN`, `NOCLDWAIT`, `NOCLDSTOP`, `NOCLDWAIT|NOCLDSTOP`). -/
  | setSigchld (mode : UInt8)
  /-- Toggle `RLIMIT_CORE` soft limit (`0` vs `rlim_max`). -/
  | setCoreLimit (enable : Bool)
  /-- Configure `SIG_IGN` on `sig` (`1..64`, excluding `9`/`19`/`32`/`33`). -/
  | setAmbientSigIgn (sig : UInt32) (ign : Bool)
  /-- Configure `pthread_sigmask` `SIG_BLOCK` / `SIG_UNBLOCK` on `sig`. -/
  | setSigBlocked (sig : UInt32) (blocked : Bool)
  /-- Configure `PR_SET_CHILD_SUBREAPER` on caller. -/
  | setSubreaper (enable : Bool)
  /-- Temporarily tighten `RLIMIT_NOFILE` (`0 = restore`, `1 = 0 free FDs`, `2 = 1 free FD`). -/
  | setNofileMode (mode : UInt8)
  /-- Move caller PGID to `selfPid` (`setpgid(0, 0)`) when `!doSetsid`. -/
  | moveSelfPgid
  /-- Spawn a helper child or thread (`pgidChoice` selects inherited/own/existing child pgid). -/
  | spawn (kind : SpawnKind) (pgidChoice : Nat)
  /-- Move active child `idx` into own PGID (`toSelf = false`) or caller PGID (`toSelf = true`). -/
  | movePgid (childIdx : Nat) (toSelf : Bool)
  /-- Explicitly close open descriptor handle `fdIdx`. -/
  | closeHandle (fdIdx : Nat)
  /-- Execute `pipe2(flags)`. -/
  | doPipe2 (flags : PipeFlags)
  /-- Execute `waitpid(target, flags)`. -/
  | doWaitpid (target : SymPidTarget) (flags : WaitFlags)
  /-- Execute `kill(target, sig)`. -/
  | doKill (target : SymPidTarget) (sig : Signal)
  /-- Execute `pidfd_open(target, flags)`. -/
  | doPidfdOpen (target : SymPidTarget) (flags : PidfdOpenFlags)
  /-- Execute `pidfd_send_signal(fd, sig, flags)`. -/
  | doPidfdSend (fd : SymFdTarget) (sig : Signal) (flags : PidfdSignalFlags)
  /-- Execute `getpid()`. -/
  | doGetpid
  /-- Execute `getuid()`. -/
  | doGetuid
  deriving Repr, DecidableEq, Inhabited

/-- Single self-contained fuzz episode containing environment settings and symbolic actions. -/
structure FuzzEpisode where
  /-- Whether running inside an isolated `CLONE_NEWUSER | CLONE_NEWPID` PID namespace. -/
  closedNamespace : Bool
  /-- Whether `setsid()` was called before starting (`selfPgid == selfPid` vs `0`). -/
  doSetsid : Bool
  /-- Whether running as `PID 2` with unkillable `PID 1` in `procs`. -/
  asPid2 : Bool := false
  /-- Whether `PID 1` owns a distinct UID (`dropToNobody` succeeded in `PID 2`). -/
  pid1Foreign : Bool := false
  /-- Whether `CONFIG_WATCH_QUEUE` (`O_NOTIFICATION_PIPE`) is supported on this kernel. -/
  watchQueueSupported : Bool := false
  /-- Whether `PIDFD_THREAD` (`pidfd_open(..., O_EXCL)`) is supported on this kernel. -/
  pidfdThreadSupported : Bool := false
  /-- Signals configured as `SIG_IGN` before spawning any child in the episode. -/
  ambientSigIgn : Array UInt32 := #[]
  /-- Signals blocked via `sigprocmask(SIG_BLOCK)` before spawning any child in the episode. -/
  ambientSigBlocked : Array UInt32 := #[]
  /-- Whether `CAP_KILL` was dropped prior to running the episode. -/
  dropCapKill : Bool := false
  /-- Whether a pre-installed `seccomp` `SECCOMP_RET_ERRNO` filter is active during the episode. -/
  ambientSeccomp : Bool := false
  /-- Optional `seccomp` syscall filter selector (`0..7`) when `ambientSeccomp = true`. -/
  seccompOpKind? : Option UInt8 := none
  /-- Configured `seccomp` `SECCOMP_RET_ERRNO` code (`1..4095`) when `ambientSeccomp = true`. -/
  seccompErrno : UInt32 := 0
  /-- Cached `getpid()` captured prior to installing `seccomp` (used when `SYS_getpid` is filtered). -/
  initSelfPid? : Option UInt32 := none
  /-- Cached `getuid()` captured prior to installing `seccomp` (used when `SYS_getuid` is filtered). -/
  initSelfUid? : Option UInt32 := none
  /-- Ordered list of actions executed during the episode. -/
  actions : Array FuzzAction
  deriving Repr, DecidableEq

private structure TrackedFd where
  hid : HandleId
  raw : RawFd
  isPidfd : Bool
  isClosed : Bool

private structure TrackedChild where
  pid : UInt32
  pgid : UInt32
  isSubreaperGrandchild : Bool := false

private structure TrackedThread where
  tid : UInt32
  tgid : UInt32
  ctlWr : UInt32
  handle : UInt64
  joinable : Bool

private structure LiveState where
  model : ProcessSysState
  children : Array TrackedChild
  threads : Array TrackedThread
  handles : Array TrackedFd
  dummyPipe? : Option (RawFd × RawFd)
  subreaper : Bool
  nofileTight : Bool
  blockedSigs : Array UInt32
  sigIgnMask : Array UInt32
  everBlockedSigs : Array UInt32
  hostThreadTids : Array UInt32
  initHostPgid : UInt32
  selfSid : UInt32
  selfOrphanedPgid : Bool

/-- Mutable hit counter tracking exercised `(syscall, outcomeCategory)` pairs across the fuzzer run. -/
abbrev HitMap := List ((String × String) × Nat)

private def expandedSigPool : Array UInt32 :=
  #[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 15, 17, 18, 20, 21, 22, 23, 24, 25, 28, 31, 34, 35, 64]

private def recordHit (hits : HitMap) (sysName bucket : String) : HitMap :=
  let key := (sysName, bucket)
  match hits with
  | [] => [(key, 1)]
  | (k, n) :: rest =>
    if k == key then (k, n + 1) :: rest
    else (k, n) :: recordHit rest sysName bucket

private def mergeHitMaps (a b : HitMap) : HitMap :=
  b.foldl (fun acc ((sys, bkt), cnt) =>
    let rec addCount : HitMap → HitMap
      | [] => [((sys, bkt), cnt)]
      | (k, n) :: rest => if k == (sys, bkt) then (k, n + cnt) :: rest else (k, n) :: addCount rest
    addCount acc) a

private def formatHitsCompact (hits : HitMap) : String :=
  let parts := hits.map fun ((sys, bkt), cnt) => s!"{sys}/{bkt}={cnt}"
  String.intercalate "," parts

private def parseHitsCompact (line : String) : HitMap :=
  let entries := line.splitOn ","
  entries.foldl (fun acc item =>
    match item.splitOn "=" with
    | [left, cntStr] =>
      match left.splitOn "/" with
      | [sys, bkt] =>
        match cntStr.toNat? with
        | some cnt => ((sys, bkt), cnt) :: acc
        | none => acc
      | _ => acc
    | _ => acc) []

private def outcomeBucket (out : ProcessOutcome) : String :=
  match out with
  | .err code => s!"{Errno.name code}"
  | .waited .stillRunning => "ok:stillRunning"
  | .waited (.exited _ _) => "ok:exited"
  | .waited (.signaled _ _ _) => "ok:signaled"
  | .waited (.stopped _ _) => "ok:stopped"
  | .waited (.continued _) => "ok:continued"
  | _ => "ok"

private def isSyscallAction : FuzzAction → Bool
  | .doPipe2 _ | .doWaitpid _ _ | .doKill _ _ | .doPidfdOpen _ _
  | .doPidfdSend _ _ _ | .doGetpid | .doGetuid => true
  | _ => false

private def pickNonZeroExtraBits (r : Rng) (boundary : Array UInt32) : UInt32 × Rng :=
  let (useBoundary, r1) := r.chance 1 2
  if useBoundary then
    r1.pickArray boundary 1
  else
    let (u, r2) := r1.nextU32
    (if u == 0 then 1 else u, r2)

private def pickSignal (r : Rng) : Signal × Rng :=
  let (roll, r1) := r.nextNat 100
  if roll < 56 then
    let syms : Array Signal :=
      #[.sigzero, .raw 0, .sighup, .sigint, .raw 3, .raw 6, .sigkill, .sigusr1, .sigusr2,
        .sigterm, .raw 17, .sigcont, .sigcont, .sigcont, .sigcont, .sigcont,
        .sigstop, .sigstop, .sigstop, .raw 20, .raw 21, .raw 22, .raw 23, .raw 28, .raw 34, .raw 64]
    r1.pickArray syms .sigzero
  else if roll < 86 then
    let (rawNum, r2) := r1.nextRange 0 64
    (.raw (Int32.ofInt (Int.ofNat rawNum)), r2)
  else if roll < 93 then
    let bads : Array Int32 := #[-1, -100, 65, 99, 999, Int32.minValue]
    let (bad, r2) := r1.pickArray bads (-1)
    (.raw bad, r2)
  else
    let (u, r2) := r1.nextU32
    (.raw u.toInt32, r2)

private def genPipeFlags (r : Rng) : PipeFlags × Rng :=
  let (cloexec, r1) := r.chance 2 3
  let (nonblock, r2) := r1.chance 1 2
  let (direct, r3) := r2.chance 1 4
  let (notificationPipe, r4) := r3.chance 1 5
  let (inv, r5) := r4.chance 1 6
  let (extra, r6) :=
    if inv then pickNonZeroExtraBits r5 #[1, 2, 0x40000000, 0x80000000]
    else (0, r5)
  ({ cloexec, nonblock, direct, notificationPipe, extraBits := extra }, r6)

private def genWaitFlags (r : Rng) : WaitFlags × Rng :=
  let (nohang, r1) := r.chance 3 4
  let (untraced, r2) := r1.chance 3 5
  let (continued, r3) := r2.chance 3 4
  let (wall, r4) := r3.chance 1 3
  let (wclone, r5) := r4.chance 1 4
  let (wnothread, r6) := r5.chance 1 4
  let (inv, r7) := r6.chance 1 8
  let (extra, r8) :=
    if inv then pickNonZeroExtraBits r7 #[1, 4, 0x10, 0x04000000, 0x40000000, 0x80000000]
    else (0, r7)
  ({ nohang, untraced, continued, wall, wclone, wnothread, extraBits := extra }, r8)

private def genPidfdOpenFlags (r : Rng) : PidfdOpenFlags × Rng :=
  let (nonblock, r1) := r.chance 1 2
  let (thread, r2) := r1.chance 1 2
  let (inv, r3) := r2.chance 1 6
  let (extra, r4) :=
    if inv then pickNonZeroExtraBits r3 #[1, 2, 0x40000000, 0x80000000]
    else (0, r3)
  ({ nonblock, thread, extraBits := extra }, r4)

private def genPidfdSignalFlags (r : Rng) : PidfdSignalFlags × Rng :=
  let (roll, r1) := r.nextNat 15
  if roll < 3 then ({}, r1)
  else if roll < 5 then ({ thread := true }, r1)
  else if roll < 8 then ({ threadGroup := true }, r1)
  else if roll < 10 then ({ processGroup := true }, r1)
  else if roll < 12 then
    let (thread, r2) := r1.chance 2 3
    let (threadGroup, r3) := r2.chance 1 2
    let (processGroup, r4) := r3.chance 2 3
    let base : PidfdSignalFlags := { thread, threadGroup, processGroup }
    if base.isValid then ({ thread := true, processGroup := true }, r4)
    else (base, r4)
  else
    let (thread, r2) := r1.chance 1 3
    let (processGroup, r3) := r2.chance 1 3
    let (extra, r4) := pickNonZeroExtraBits r3 #[1, 2, 0x40000000, 0x80000000]
    ({ thread, processGroup, extraBits := extra }, r4)

private def genPidTarget (r : Rng) (closedNs asPid2 : Bool) : SymPidTarget × Rng :=
  let (roll, r1) := r.nextNat 100
  if roll < 32 then
    let (idx, r2) := r1.nextNat 65536
    (.childPid idx, r2)
  else if roll < 47 then
    let (idx, r2) := r1.nextNat 65536
    (.negChildPgid idx, r2)
  else if roll < 60 then
    let (idx, r2) := r1.nextNat 65536
    (.threadTid idx, r2)
  else if roll < 66 && !closedNs then
    let (idx, r2) := r1.nextNat 65536
    (.hostThreadTid idx, r2)
  else if roll < 71 then
    (.selfPid, r1)
  else if roll < 75 then
    (.zero, r1)
  else if roll < 81 then
    if closedNs && !asPid2 then (.negOne, r1) else (.pidOne, r1)
  else if roll < 85 then
    (.negOne, r1)
  else if roll < 90 then
    (.negSelfPgid, r1)
  else if roll < 94 then
    (.intMin, r1)
  else if roll < 97 then
    (.pidTwo, r1)
  else
    let (useBoundary, r2) := r1.chance 1 2
    let (u, r3) :=
      if useBoundary then r2.pickArray #[0, 99999999, 0x7fffffff, 0x80000000] 99999999
      else r2.nextU32
    (.untracked u, r3)

private def genFdTarget (r : Rng) : SymFdTarget × Rng :=
  let (roll, r1) := r.nextNat 100
  if roll < 65 then
    let (idx, r2) := r1.nextNat 65536
    (.openPidfd idx, r2)
  else if roll < 80 then
    let (idx, r2) := r1.nextNat 65536
    (.closedFd idx, r2)
  else if roll < 92 then
    let (idx, r2) := r1.nextNat 65536
    (.openPipe idx, r2)
  else
    (.fallbackClosed, r1)

private def genSpawnAction (r : Rng) : FuzzAction × Rng :=
  let (roll, r1) := r.nextNat 100
  let (pgChoice, r2) := r1.nextNat 65536
  if roll < 18 then
    (.spawn .controlled pgChoice, r2)
  else if roll < 30 then
    let (delay, r3) := r2.pickArray #[0, 200, 1500] 200
    let (codeNat, r4) := r3.nextNat 256
    (.spawn (.autonomous delay (UInt8.ofNat codeNat)) pgChoice, r4)
  else if roll < 44 then
    let (stopSig, r3) := r2.pickArray #[19, 20, 21, 22] 19
    (.spawn (.stopped stopSig) pgChoice, r3)
  else if roll < 53 then
    let (codeNat, r3) := r2.nextNat 256
    (.spawn (.zombieExit (UInt8.ofNat codeNat)) pgChoice, r3)
  else if roll < 64 then
    let coreSigs : Array UInt32 := #[3, 4, 5, 6, 7, 8, 9, 11, 15, 24, 25, 31]
    let (sig, r3) := r2.pickArray coreSigs 6
    let (allowCore, r4) := r3.chance 1 3
    (.spawn (.zombieSig sig allowCore) pgChoice, r4)
  else if roll < 71 then
    (.spawn .thread pgChoice, r2)
  else if roll < 75 then
    (.spawn .threadedChild pgChoice, r2)
  else if roll < 84 then
    let (codeNat, r3) := r2.nextNat 256
    let (subDelay, r4) := r3.pickArray #[0, 8000, 15000] 0
    let (subCodeNat, r5) := r4.nextNat 256
    let code8 := UInt8.ofNat codeNat
    let subCode8 := if subDelay == 0 then code8 else UInt8.ofNat subCodeNat
    (.spawn (.delayedZombie code8 subDelay subCode8) pgChoice, r5)
  else if roll < 87 then
    (.spawn .cloneControlled pgChoice, r2)
  else if roll < 90 then
    let (codeNat, r3) := r2.nextNat 256
    (.spawn (.cloneZombie (UInt8.ofNat codeNat)) pgChoice, r3)
  else if roll < 93 then
    (.spawn .siblingChild pgChoice, r2)
  else
    (.spawn .reparentedGrandchild pgChoice, r2)

private def genAction (r : Rng) (closedNs asPid2 : Bool) (secOp? : Option UInt8 := none) : FuzzAction × Rng :=
  let (boost, r0) := r.nextNat 10
  if boost < 3 && secOp? == some 0 then
    let (flags, r2) := genPipeFlags r0
    (.doPipe2 flags, r2)
  else if boost < 3 && secOp? == some 1 then
    let (t, r2) := genPidTarget r0 closedNs asPid2
    let (flags, r3) := genWaitFlags r2
    (.doWaitpid t flags, r3)
  else if boost < 3 && secOp? == some 2 then
    let (t, r2) := genPidTarget r0 closedNs asPid2
    let (sig, r3) := pickSignal r2
    (.doKill t sig, r3)
  else if boost < 3 && secOp? == some 3 then
    let (t, r2) := genPidTarget r0 closedNs asPid2
    let (flags, r3) := genPidfdOpenFlags r2
    (.doPidfdOpen t flags, r3)
  else if boost < 3 && secOp? == some 4 then
    let (f, r2) := genFdTarget r0
    let (sig, r3) := pickSignal r2
    let (flags, r4) := genPidfdSignalFlags r3
    (.doPidfdSend f sig flags, r4)
  else if boost < 3 && secOp? == some 5 then
    (.doGetpid, r0)
  else if boost < 3 && secOp? == some 6 then
    (.doGetuid, r0)
  else if boost < 3 && secOp? == some 7 then
    let (flags, r2) := genWaitFlags r0
    (.doWaitpid .negOne flags, r2)
  else
  let (roll, r1) := r0.nextNat 100
  if roll < 15 then
    genSpawnAction r1
  else if roll < 24 then
    let (flags, r2) := genPipeFlags r1
    (.doPipe2 flags, r2)
  else if roll < 40 then
    let (t, r2) := genPidTarget r1 closedNs asPid2
    let (flags, r3) := genWaitFlags r2
    (.doWaitpid t flags, r3)
  else if roll < 55 then
    let (t, r2) := genPidTarget r1 closedNs asPid2
    let (sig, r3) := pickSignal r2
    (.doKill t sig, r3)
  else if roll < 66 then
    let (t, r2) := genPidTarget r1 closedNs asPid2
    let (flags, r3) := genPidfdOpenFlags r2
    (.doPidfdOpen t flags, r3)
  else if roll < 78 then
    let (f, r2) := genFdTarget r1
    let (sig, r3) := pickSignal r2
    let (flags, r4) := genPidfdSignalFlags r3
    (.doPidfdSend f sig flags, r4)
  else if roll < 82 then
    let (idx, r2) := r1.nextNat 65536
    (.closeHandle idx, r2)
  else if roll < 85 then
    let (idx, r2) := r1.nextNat 65536
    let (toSelf, r3) := r2.chance 1 2
    (.movePgid idx toSelf, r3)
  else if roll < 88 then
    let (mode, r2) := r1.nextNat 5
    (.setSigchld (UInt8.ofNat mode), r2)
  else if roll < 90 then
    let (sig, r2) := r1.pickArray expandedSigPool 18
    let (ign, r3) := r2.chance 1 2
    (.setAmbientSigIgn sig ign, r3)
  else if roll < 92 then
    let (sig, r2) := r1.pickArray expandedSigPool 18
    let (blk, r3) := r2.chance 1 2
    (.setSigBlocked sig blk, r3)
  else if roll < 95 then
    let (en, r2) := r1.chance 4 5
    (.setSubreaper en, r2)
  else if roll < 96 then
    let (mode, r2) := r1.nextNat 3
    (.setNofileMode (UInt8.ofNat mode), r2)
  else if roll < 97 then
    let (doMove, r2) := r1.chance 1 3
    if doMove then (.moveSelfPgid, r2) else (.doGetuid, r2)
  else if roll < 98 then
    let (enable, r2) := r1.chance 1 4
    (.setCoreLimit enable, r2)
  else if roll < 99 then
    (.doGetpid, r1)
  else
    (.doGetuid, r1)

private def generateEpisode (r : Rng) (closedNs doSetsid asPid2 watchQueue pidfdThread : Bool)
    (maxActions : Nat) (ambientSeccomp : Bool := false) (pid1Foreign : Bool := false)
    (initSelfPid? : Option UInt32 := none) (initSelfUid? : Option UInt32 := none)
    (secOp? : Option UInt8 := none) (dropCapKill : Bool := false) (secErrno : UInt32 := 0) :
    FuzzEpisode × Rng := Id.run do
  let (useIgn, rA) := r.chance 2 5
  let (ignSigs, rB) : Array UInt32 × Rng :=
    if useIgn then
      let (s1, r1) := rA.pickArray expandedSigPool 18
      let (two, r2) := r1.chance 1 3
      if two then
        let (s2, r3) := r2.pickArray expandedSigPool 10
        (if s1 == s2 then #[s1] else #[s1, s2], r3)
      else (#[s1], r2)
    else (#[], rA)
  let (useBlk, rC) := rB.chance 1 4
  let (blkSigs, rD) : Array UInt32 × Rng :=
    if useBlk then
      let (b1, r1) := rC.pickArray expandedSigPool 18
      (#[b1], r1)
    else (#[], rC)
  let mut curR := rD
  let mut acts : Array FuzzAction := #[]
  let (earlySub, curR0) := curR.chance 1 2
  curR := curR0
  if earlySub then
    acts := acts.push (.setSubreaper true)
  for i in [:maxActions] do
    let (doEarlySig, rStep) := curR.chance 1 3
    if i < 2 && doEarlySig then
      let (sig, r1) := rStep.pickArray expandedSigPool 18
      let (useSigBlk, r2) := r1.chance 1 2
      let (enable, r3) := r2.chance 1 2
      curR := r3
      acts := acts.push (if useSigBlk then .setSigBlocked sig enable else .setAmbientSigIgn sig enable)
    else if i == 2 && earlySub then
      let (doGc, r1) := rStep.chance 1 2
      if doGc then
        let (pgChoice, r2) := r1.nextNat 65536
        curR := r2
        acts := acts.push (.spawn .reparentedGrandchild pgChoice)
      else
        let (sa, r2) := genSpawnAction r1
        curR := r2
        acts := acts.push sa
    else if i < 3 then
      let (sa, r') := genSpawnAction rStep
      curR := r'
      acts := acts.push sa
    else
      let (act, r') := genAction curR closedNs asPid2 secOp?
      curR := r'
      acts := acts.push act
  return (
    { closedNamespace := closedNs
      doSetsid
      asPid2
      pid1Foreign
      watchQueueSupported := watchQueue
      pidfdThreadSupported := pidfdThread
      ambientSigIgn := ignSigs
      ambientSigBlocked := blkSigs
      dropCapKill
      ambientSeccomp
      seccompOpKind? := if ambientSeccomp then secOp? else none
      seccompErrno := if ambientSeccomp then secErrno else 0
      initSelfPid?
      initSelfUid?
      actions := acts },
    curR)

private def resolvePid (st : LiveState) (t : SymPidTarget) : Int32 :=
  let selfPid := effectiveSelfPid st.model
  let selfPgid := effectiveSelfPgid st.model
  match t with
  | .selfPid => selfPid.toInt32
  | .zero => 0
  | .negOne => -1
  | .pidOne => 1
  | .pidTwo => 2
  | .intMin => Int32.minValue
  | .negSelfPgid =>
    if selfPgid == 0 then 0 else -selfPgid.toInt32
  | .childPid idx =>
    if st.children.isEmpty then 99999999
    else (st.children.getD (idx % st.children.size) { pid := 99999999, pgid := 0 }).pid.toInt32
  | .negChildPgid idx =>
    if st.children.isEmpty then -99999999
    else
      let pg := (st.children.getD (idx % st.children.size) { pid := 0, pgid := 99999999 }).pgid
      if pg == 0 then 0 else -pg.toInt32
  | .threadTid idx =>
    if st.threads.isEmpty then 99999998
    else (st.threads.getD (idx % st.threads.size) { tid := 99999998, tgid := 0, ctlWr := 0, handle := 0, joinable := false }).tid.toInt32
  | .hostThreadTid idx =>
    if st.hostThreadTids.isEmpty then 99999997
    else (st.hostThreadTids.getD (idx % st.hostThreadTids.size) 99999997).toInt32
  | .untracked v => v.toInt32

private def resolveU32Pid (st : LiveState) (t : SymPidTarget) : UInt32 :=
  (resolvePid st t).toUInt32

private def resolveFd (st : LiveState) (f : SymFdTarget) : Option (HandleId × RawFd) :=
  let openPidfds := st.handles.filter fun h => h.isPidfd && !h.isClosed
  let openPipes := st.handles.filter fun h => !h.isPidfd && !h.isClosed
  let closedOnes := st.handles.filter fun h => h.isClosed
  match f with
  | .openPidfd idx =>
    if openPidfds.isEmpty then none
    else (openPidfds[idx % openPidfds.size]?).map fun h => (h.hid, h.raw)
  | .openPipe idx =>
    if openPipes.isEmpty then none
    else (openPipes[idx % openPipes.size]?).map fun h => (h.hid, h.raw)
  | .closedFd idx =>
    if closedOnes.isEmpty then none
    else (closedOnes[idx % closedOnes.size]?).map fun h => (h.hid, h.raw)
  | .fallbackClosed =>
    if closedOnes.isEmpty then none
    else (closedOnes[0]?).map fun h => (h.hid, h.raw)

private def isHarmlessSelfSignal (st : LiveState) (sig : Signal) (targetsOuterPgrp : Bool := false) : Bool :=
  if !sig.isValid || sig.isNptlReserved then true
  else
    let n := sig.toLinuxNum
    n == 0 || n == 18 || isDefaultIgnoredSignal n ||
      (!targetsOuterPgrp && st.model.closedPidNamespace && effectiveSelfPid st.model == 1 &&
        !st.everBlockedSigs.any (fun s => Int.ofNat s.toNat == n))

private def isSafeAction (st : LiveState) (act : FuzzAction) : Bool :=
  let selfP := effectiveSelfPid st.model
  let selfPg := effectiveSelfPgid st.model
  let isKillableSelfTarget (p : Int32) : Bool :=
    p == selfP.toInt32 || p == 0 || (selfPg != 0 && p == -selfPg.toInt32) ||
      (!st.model.closedPidNamespace && st.initHostPgid != 0 && p == -st.initHostPgid.toInt32) ||
      st.threads.any (fun t => t.tgid == selfP && t.tid == p.toUInt32) ||
      (p > 0 && match assocGet st.model.procs p.toUInt32 with
        | some pe => match pe.role with | .thread tgid => tgid == selfP | _ => false
        | none => false)
  match act with
  | .doKill t sig =>
    let p := resolvePid st t
    if isKillableSelfTarget p then
      let targetsOuterOrThread := (p == 0 && selfPg == 0) || (p > 0 && p.toUInt32 != selfP)
      isHarmlessSelfSignal st sig targetsOuterOrThread
    else if !st.model.closedPidNamespace then
      let rawSig := sig.toLinuxNum
      if !sig.isValid || sig.isNptlReserved then true
      else if p == Int32.minValue then true
      else if rawSig == 0 then
        p == -1 || p > 0 || st.children.any (fun c =>
          c.pgid != selfPg && c.pgid != st.initHostPgid && c.pgid == UInt32.ofNat (-p.toInt).toNat)
      else if p > 0 then
        p.toUInt32 > maxLinuxPid || st.children.any (·.pid == p.toUInt32) ||
          st.threads.any (fun th => th.tid == p.toUInt32 && th.tgid != selfP)
      else
        p != -1 && st.children.any (fun c =>
          c.pgid != selfPg && c.pgid != st.initHostPgid && UInt32.ofNat (-p.toInt).toNat == c.pgid)
    else
      true
  | .doPidfdSend f sig flags =>
    if !flags.isValid || !sig.isValid || sig.isNptlReserved then true
    else
      match resolveFd st f with
      | none => true
      | some (hid, _) =>
        match assocGet st.model.fds hid with
        | some (.pidfd tPid _ _) =>
          if flags.processGroup then
            let tPg := match assocGet st.model.procs tPid with | some pe => pe.pgid | none => tPid
            if tPid == selfP || tPid == selfPg || tPg == selfPg ||
                (!st.model.closedPidNamespace && st.initHostPgid != 0 &&
                  (tPid == st.initHostPgid || tPg == st.initHostPgid)) then
              let targetsOuterOrThread := (tPg == 0 && selfPg == 0) || (tPid != selfP)
              isHarmlessSelfSignal st sig targetsOuterOrThread
            else if !st.model.closedPidNamespace then
              st.children.any (fun c => c.pid == tPid && c.pgid != selfPg && c.pgid != st.initHostPgid)
            else true
          else
            let tTgid := match assocGet st.model.procs tPid with
              | some pe => match pe.role with | .thread tgid => tgid | _ => tPid
              | none => tPid
            if tPid == selfP || tTgid == selfP then isHarmlessSelfSignal st sig (tPid != selfP)
            else if !st.model.closedPidNamespace then
              if sig.toLinuxNum == 0 then true
              else st.children.any (·.pid == tPid) || st.threads.any (fun th => th.tid == tPid && th.tgid != selfP)
            else true
        | _ => true
  | _ => true

private def cleanupLiveState (st : LiveState) : IO Unit := do
  if st.nofileTight then
    let _ ← ProcessEnv.setNofileMode 0
  let _ ← ProcessEnv.setSubreaper false
  let _ ← ProcessEnv.setSigchldAutoreap 0
  let _ ← ProcessEnv.setCoreLimit false
  ProcessEnv.clearSigMask
  for sNum in expandedSigPool do
    if sNum != 17 then
      let _ ← ProcessEnv.setSigIgn sNum false
  for h in st.handles do
    if !h.isClosed then
      let _ ← ProcessEnv.closeFd h.raw
  if let some (r, w) := st.dummyPipe? then
    let _ ← ProcessEnv.closeFd r
    let _ ← ProcessEnv.closeFd w
  for c in st.children do
    ProcessEnv.cleanupChild c.pid
  for t in st.threads do
    if t.joinable then
      ProcessEnv.joinThread t.ctlWr t.handle

private def pickSpawnPgidReq (st : LiveState) (pgidChoice : Nat) : Int32 :=
  let mod := pgidChoice % 4
  if mod == 0 then 0
  else if mod == 1 then -1
  else
    match st.children[pgidChoice % (max 1 st.children.size)]? with
    | some c => if c.pgid == 0 then -1 else c.pgid.toInt32
    | none => -1

private def recordSpawnedChild (st : LiveState) (m' : ProcessSysState) (pid pgid : UInt32)
    (isSubreaperGrandchild : Bool := false) : LiveState :=
  { st with model := m', children := st.children.push { pid, pgid, isSubreaperGrandchild } }

private def effectiveIgnored (m : ProcessSysState) (blocked : Array UInt32) : List UInt32 :=
  blocked.foldl (fun acc s => if acc.contains s then acc else s :: acc) m.ambientIgnoredSigs

private def parseLastNspid (statusText : String) : Option UInt32 :=
  (statusText.splitOn "\n").findSome? fun line =>
    if line.startsWith "NSpid:" then
      let rest := (line.drop 6).toString
      let tokens := (rest.splitOn "\t").flatMap (·.splitOn " ") |>.filter (!·.isEmpty)
      tokens.getLast?.bind (·.toNat?) |>.map UInt32.ofNat
    else
      none

private def isReparentedToSiblingThread (selfPid : UInt32) : IO Bool := do
  try
    let txt ← IO.FS.readFile "/proc/thread-self/status"
    return match parseLastNspid txt with
      | some tid => tid != selfPid
      | none => false
  catch _ =>
    return false

private def unionSigArrays (a b : Array UInt32) : List UInt32 :=
  b.foldl (fun acc s => if acc.contains s then acc else s :: acc) a.toList

private def hexVal (c : Char) : Option UInt64 :=
  if '0' ≤ c && c ≤ '9' then some (UInt64.ofNat (c.toNat - '0'.toNat))
  else if 'a' ≤ c && c ≤ 'f' then some (UInt64.ofNat (10 + c.toNat - 'a'.toNat))
  else if 'A' ≤ c && c ≤ 'F' then some (UInt64.ofNat (10 + c.toNat - 'A'.toNat))
  else none

private def readAmbientMaskField (fieldPrefix : String) : IO (List UInt32) := do
  try
    let txt ←
      try IO.FS.readFile "/proc/thread-self/status"
      catch _ => IO.FS.readFile "/proc/self/status"
    let maskOpt := (txt.splitOn "\n").findSome? fun line =>
      if line.startsWith fieldPrefix then
        let rest := (line.drop fieldPrefix.length).toString
        let tokens := (rest.splitOn "\t").flatMap (·.splitOn " ") |>.filter (!·.isEmpty)
        tokens.getLast?.bind fun tok =>
          tok.foldl (fun (acc? : Option UInt64) ch =>
            match acc?, hexVal ch with
            | some acc, some v => some ((acc <<< (4 : UInt64)) ||| v)
            | _, _ => none) (some (0 : UInt64))
      else
        none
    match maskOpt with
    | none => return []
    | some mask =>
      let mut sigs : List UInt32 := []
      for i in [0:64] do
        let s := i + 1
        if s != 9 && s != 19 then
          if (mask &&& ((1 : UInt64) <<< (UInt64.ofNat i))) != 0 then
            sigs := UInt32.ofNat s :: sigs
      return sigs
  catch _ =>
    return []

private def readPendingSignals : IO (List UInt32) := do
  let thrPnd ← readAmbientMaskField "SigPnd:"
  let shdPnd ← readAmbientMaskField "ShdPnd:"
  return shdPnd.foldl (fun acc s => if acc.contains s then acc else s :: acc) thrPnd

private def runOneAction (st : LiveState) (hits : HitMap) (act : FuzzAction) :
    IO (Except String (LiveState × HitMap)) := do
  if !isSafeAction st act then
    return .ok (st, hits)
  match act with
  | .setSigchld mode =>
    let _ ← ProcessEnv.setSigchldAutoreap mode
    let isAuto := mode == 1 || mode == 2 || mode == 4
    return .ok ({ st with model := st.model.withSigchldAutoreap isAuto }, hits)
  | .setCoreLimit enable =>
    let _ ← ProcessEnv.setCoreLimit enable
    return .ok (st, hits)
  | .setAmbientSigIgn sig ign =>
    if !st.children.isEmpty || !st.threads.isEmpty then
      return .ok (st, hits)
    if sig == 9 || sig == 17 || sig == 19 || sig == 32 || sig == 33 then
      return .ok (st, hits)
    let _ ← ProcessEnv.setSigIgn sig ign
    let ign' :=
      if ign then (if st.sigIgnMask.contains sig then st.sigIgnMask else st.sigIgnMask.push sig)
      else st.sigIgnMask.filter (· != sig)
    return .ok ({ st with sigIgnMask := ign', model := st.model.withAmbientIgnoredSigs (unionSigArrays ign' st.blockedSigs) }, hits)
  | .setSigBlocked sig blocked =>
    if !st.children.isEmpty || !st.threads.isEmpty then
      return .ok (st, hits)
    if sig == 9 || sig == 19 || sig == 32 || sig == 33 then
      return .ok (st, hits)
    let _ ← ProcessEnv.setSigBlock sig blocked
    let blk' :=
      if blocked then (if st.blockedSigs.contains sig then st.blockedSigs else st.blockedSigs.push sig)
      else st.blockedSigs.filter (· != sig)
    let everBlk' :=
      if blocked && !st.everBlockedSigs.contains sig then st.everBlockedSigs.push sig
      else st.everBlockedSigs
    return .ok ({ st with blockedSigs := blk', everBlockedSigs := everBlk', model := st.model.withAmbientIgnoredSigs (unionSigArrays st.sigIgnMask blk') }, hits)
  | .setSubreaper enable =>
    match ← ProcessEnv.setSubreaper enable with
    | .ok () => return .ok ({ st with subreaper := enable }, hits)
    | .error _ => return .ok (st, hits)
  | .setNofileMode mode =>
    match ← ProcessEnv.setNofileMode mode with
    | .ok () => return .ok ({ st with nofileTight := (mode != 0) }, hits)
    | .error _ => return .ok (st, hits)
  | .moveSelfPgid =>
    if st.model.selfPgid == effectiveSelfPid st.model then
      return .ok (st, hits)
    let oldPg := st.model.selfPgid
    let wasOrph := st.selfOrphanedPgid
    match ← ProcessEnv.setpgid 0 0 with
    | .error _ => return .ok (st, hits)
    | .ok () =>
      let newPg ← ProcessEnv.getpgrp
      let newOrph ← ProcessEnv.isSelfPgidOrphaned
      let procs' :=
        if wasOrph && newPg != oldPg then
          st.model.procs.map fun (p, e) =>
            if e.pgid == oldPg && e.sameSession then (p, e.setPgid e.pgid false) else (p, e)
        else
          st.model.procs
      return .ok ({ st with selfOrphanedPgid := newOrph, model := { st.model with selfPgid := newPg, procs := procs' } }, hits)
  | .spawn kind pgChoice =>
    if st.nofileTight then return .ok (st, hits)
    let pgReq := pickSpawnPgidReq st pgChoice
    let isOrphanedChild (pg : UInt32) : Bool := st.selfOrphanedPgid && pg == st.model.selfPgid
    match kind with
    | .controlled =>
      match ← ProcessEnv.spawnControlled pgReq false with
      | .ok (pid, pgid) =>
        return .ok (recordSpawnedChild st (st.model.spawnRunningChild pid pgid none false false (isOrphanedChild pgid)) pid pgid, hits)
      | .error _ => return .ok (st, hits)
    | .autonomous delayUs exitCode =>
      match ← ProcessEnv.spawnAutonomous pgReq delayUs exitCode with
      | .ok (pid, pgid) =>
        return .ok (recordSpawnedChild st (st.model.spawnRunningChild pid pgid (some (.exited exitCode)) false false (isOrphanedChild pgid)) pid pgid, hits)
      | .error _ => return .ok (st, hits)
    | .stopped stopSig =>
      let wantsOrphanedPgid := st.selfOrphanedPgid && (pgReq < 0 || pgReq.toUInt32 == st.model.selfPgid)
      let effectivePgReq := if stopSig != 19 && (pgReq < 0 || wantsOrphanedPgid) then 0 else pgReq
      match ← ProcessEnv.spawnStopped effectivePgReq stopSig with
      | .ok (pid, pgid) =>
        return .ok (recordSpawnedChild st (st.model.spawnStoppedChild pid stopSig false pgid (isOrphanedChild pgid) [stopSig]) pid pgid, hits)
      | .error _ => return .ok (st, hits)
    | .zombieExit code =>
      if st.model.sigchld == .autoreap then
        return .ok (st, hits)
      match ← ProcessEnv.spawnZombie pgReq false code.toUInt32 false with
      | .ok ((pid, pgid), _) =>
        return .ok (recordSpawnedChild st (st.model.spawnZombieExited pid code pgid) pid pgid, hits)
      | .error _ => return .ok (st, hits)
    | .zombieSig sig allowCore =>
      if st.model.sigchld == .autoreap then
        return .ok (st, hits)
      match ← ProcessEnv.spawnZombie pgReq true sig allowCore with
      | .ok ((pid, pgid), dumped) =>
        return .ok (recordSpawnedChild st (st.model.spawnZombieSignaled pid sig dumped pgid) pid pgid, hits)
      | .error _ => return .ok (st, hits)
    | .thread =>
      match ← ProcessEnv.spawnThread with
      | .ok (tid, (ctlWr, handle)) =>
        let sp := effectiveSelfPid st.model
        let m1 := st.model.registerNonLeaderThread tid sp st.model.selfPgid
        return .ok ({ st with model := m1, threads := st.threads.push { tid, tgid := sp, ctlWr, handle, joinable := true } }, hits)
      | .error _ => return .ok (st, hits)
    | .cloneControlled =>
      match ← ProcessEnv.spawnCloneChild pgReq false 0 with
      | .ok (pid, pgid) =>
        return .ok (recordSpawnedChild st (st.model.spawnRunningChild pid pgid none true false (isOrphanedChild pgid)) pid pgid, hits)
      | .error _ => return .ok (st, hits)
    | .cloneZombie code =>
      match ← ProcessEnv.spawnCloneChild pgReq true code with
      | .ok (pid, pgid) =>
        return .ok (recordSpawnedChild st (st.model.spawnZombieExited pid code pgid true false) pid pgid, hits)
      | .error _ => return .ok (st, hits)
    | .threadedChild =>
      match ← ProcessEnv.spawnThreadedChild pgReq with
      | .ok (pid, (pgid, wTid)) =>
        let st1 := recordSpawnedChild st (st.model.spawnRunningChild pid pgid none false false (isOrphanedChild pgid)) pid pgid
        if wTid == 0 then return .ok (st1, hits)
        let m2 := st1.model.registerNonLeaderThread wTid pid pgid
        return .ok ({ st1 with model := m2, threads := st1.threads.push { tid := wTid, tgid := pid, ctlWr := 0, handle := 0, joinable := false } }, hits)
      | .error _ => return .ok (st, hits)
    | .delayedZombie exitCode subDelayUs subExitCode =>
      match ← ProcessEnv.spawnDelayedZombie pgReq exitCode subDelayUs subExitCode with
      | .ok (pid, (pgid, wTid)) =>
        let exitReap := if st.model.sigchld == .autoreap then ExitReapMode.autoreapOnly else ExitReapMode.zombieOnly
        let dzEntry : ProcEntry :=
          { pgid := pgid
            canSignal := true
            sameSession := true
            orphanedPgid := isOrphanedChild pgid
            role := .child .sigchld false
            lifecycle := .delayedZombie (.exited exitCode) false [] .running .none [] exitReap false }
        let st1 := recordSpawnedChild st (st.model.upsertProc pid dzEntry) pid pgid
        if wTid == 0 then return .ok (st1, hits)
        let m2 :=
          if subDelayUs == 0 then
            st1.model.registerNonLeaderThread wTid pid pgid
          else
            let wEntry : ProcEntry :=
              { pgid := pgid
                canSignal := true
                sameSession := true
                orphanedPgid := isOrphanedChild pgid
                role := .thread pid
                lifecycle := .alive { auto := .planned (.exited subExitCode) } }
            st1.model.upsertProc wTid wEntry
        return .ok ({ st1 with model := m2, threads := st1.threads.push { tid := wTid, tgid := pid, ctlWr := 0, handle := 0, joinable := false } }, hits)
      | .error _ => return .ok (st, hits)
    | .siblingChild =>
      match ← ProcessEnv.spawnSiblingChild pgReq with
      | .ok ((cPid, cPg), (sTid, handle)) =>
        let sp := effectiveSelfPid st.model
        let st1 :=
          if sTid != 0 then
            let m1 := st.model.registerNonLeaderThread sTid sp st.model.selfPgid
            { st with model := m1, threads := st.threads.push { tid := sTid, tgid := sp, ctlWr := 0, handle, joinable := true } }
          else st
        if cPid == 0 then return .ok (st1, hits)
        let st2 := recordSpawnedChild st1 (st1.model.spawnRunningChild cPid cPg none false true (isOrphanedChild cPg)) cPid cPg
        return .ok (st2, hits)
      | .error _ => return .ok (st, hits)
    | .reparentedGrandchild =>
      if (!st.subreaper && effectiveSelfPid st.model != 1) || st.model.sigchld == .autoreap then
        return .ok (st, hits)
      match ← ProcessEnv.spawnReparentedGrandchild pgReq with
      | .ok (gcPid, gcPg) =>
        if gcPid == 0 then return .ok (st, hits)
        let fromSib ← isReparentedToSiblingThread (effectiveSelfPid st.model)
        return .ok (recordSpawnedChild st (st.model.spawnRunningChild gcPid gcPg none false fromSib (isOrphanedChild gcPg)) gcPid gcPg true, hits)
      | .error _ => return .ok (st, hits)
  | .movePgid childIdx toSelf =>
    if st.children.isEmpty then return .ok (st, hits)
    let c := st.children.getD (childIdx % st.children.size) { pid := 0, pgid := 0 }
    let targetPg := if toSelf then st.model.selfPgid else c.pid
    if targetPg == 0 then return .ok (st, hits)
    match ← ProcessEnv.setpgid c.pid targetPg with
    | .error _ => return .ok (st, hits)
    | .ok () =>
      let children' := st.children.map fun item =>
        if item.pid == c.pid then { item with pgid := targetPg } else item
      let newOrph := st.selfOrphanedPgid && targetPg == st.model.selfPgid
      let procs' := st.model.procs.map fun (p, e) =>
        if p == c.pid || e.role == .thread c.pid then
          (p, e.setPgid targetPg newOrph)
        else
          (p, e)
      return .ok ({ st with children := children', model := { st.model with procs := procs' } }, hits)
  | .closeHandle fdIdx =>
    let isKernelCloseDetachErr (e : Errno) : Bool :=
      e == Errno.EBADF || e == Errno.EINTR || e == Errno.EIO || e == Errno.ENOSPC ||
      e == ⟨122⟩ || e == Errno.ENOMEM || e == ⟨116⟩ || e == ⟨104⟩
    let openList := st.handles.filter (!·.isClosed)
    match openList[fdIdx % max 1 openList.size]? with
    | none => return .ok (st, hits)
    | some target =>
      let closeRes ← ProcessEnv.closeFd target.raw
      if let .error e := closeRes then
        if e == Errno.EBUSY then
          return .error "MISMATCH closeFd cls=EBUSY unexpected pinned LeanFdBox"
      let detached : Bool :=
        match closeRes with
        | .ok () => true
        | .error e => isKernelCloseDetachErr e
      if !detached then
        return .ok (st, hits)
      let handles' := st.handles.map fun h =>
        if h.hid == target.hid then { h with isClosed := true } else h
      let model' := st.model.closeFd target.hid
      return .ok ({ st with handles := handles', model := model' }, hits)
  | .doPipe2 flags =>
    let rHid := nextFreeHid st.model.fds st.model.nextHid
    let wHid := rHid + 1
    let res ← pipe2 flags
    let out : ProcessOutcome :=
      match res with
      | .ok _ => .piped rHid wHid
      | .error e => .err e
    match allowedStep st.model (.pipe2 flags) out with
    | none =>
      if let .ok (rFd, wFd) := res then
        let _ ← ProcessEnv.closeFd rFd
        let _ ← ProcessEnv.closeFd wFd
      return .error s!"MISMATCH pipe2 cls={outcomeBucket out} flags={repr flags} out={repr out} wq={st.model.watchQueueSupported} seccomp={st.model.ambientSeccomp}"
    | some m' =>
      match res with
      | .ok (rFd, wFd) =>
        let closeBoth : IO Unit := do
          let _ ← ProcessEnv.closeFd rFd
          let _ ← ProcessEnv.closeFd wFd
        let (fdR, flR) ←
          match ← ProcessEnv.getFdFlags rFd with
          | .ok p => pure p
          | .error e =>
            closeBoth
            return .error s!"MISMATCH pipe2 cls=fd_flags_err end=r err={repr e} flags={repr flags}"
        let (fdW, flW) ←
          match ← ProcessEnv.getFdFlags wFd with
          | .ok p => pure p
          | .error e =>
            closeBoth
            return .error s!"MISMATCH pipe2 cls=fd_flags_err end=w err={repr e} flags={repr flags}"
        let expClo : UInt32 := if flags.cloexec then 1 else 0
        let expNb : UInt32 := if flags.nonblock then 0x800 else 0
        let hasDirectW := (flW &&& 0x4000) != 0 || (flW &&& 0x10000) != 0
        let directOk := flags.notificationPipe || (hasDirectW == flags.direct)
        if (fdR &&& 1) != expClo || (fdW &&& 1) != expClo ||
            (flR &&& 3) != 0 || (flW &&& 3) != 1 ||
            (flR &&& 0x800) != expNb || (flW &&& 0x800) != expNb || !directOk then
          closeBoth
          return .error s!"MISMATCH pipe2 cls=fd_flags flags={repr flags} r=({fdR},{flR}) w=({fdW},{flW})"
        let handles' :=
          st.handles.push { hid := rHid, raw := rFd, isPidfd := false, isClosed := false }
            |>.push { hid := wHid, raw := wFd, isPidfd := false, isClosed := false }
        return .ok ({ st with model := m', handles := handles' }, recordHit hits "pipe2" (outcomeBucket out))
      | .error _ =>
        return .ok ({ st with model := m' }, recordHit hits "pipe2" (outcomeBucket out))
  | .doWaitpid t rawFlags =>
    let pid := resolvePid st t
    let matching := matchingUnreapedChildren st.model pid rawFlags
    let hasPendingStop (a : AliveState) : Bool :=
      !a.pending.stopSigs.isEmpty || !a.pending.deferredTtyStops.isEmpty || !a.pending.racedTtyStops.isEmpty
    let isWillExit (a : AliveState) : Bool :=
      match a.auto with
      | .planned _ => true
      | _ => false
    let willDefinitelyDie (a : AliveState) : Bool :=
      a.pending.killed ||
        (a.run == .running && !hasPendingStop a && (isWillExit a || !a.pending.termSigs.isEmpty))
    let dzHasPendingStop (ss ds rs : List UInt32) : Bool :=
      !ss.isEmpty || !ds.isEmpty || !rs.isEmpty
    let dzWillDefinitelyFinish (cPid : UInt32) (k : Bool) (ts : List UInt32) (run : TaskRunState)
        (ss ds rs : List UInt32) : Bool :=
      k || (run == .running && !dzHasPendingStop ss ds rs &&
        ((firstValidTermSig? ts).isSome || !hasControlledLiveSubthread st.model.procs cPid))
    let willDefinitelyZombieWake : UInt32 × ProcEntry → Bool
      | (cPid, pe) =>
        match pe.lifecycle with
        | .zombie _ => true
        | .alive a => !a.mayAutoreap && willDefinitelyDie a
        | .delayedZombie _ k ts run _ ss exitReap _ ds rs =>
          exitReap == .zombieOnly && dzWillDefinitelyFinish cPid k ts run ss ds rs
        | _ => false
    let allGuaranteedAutoreap : Bool := matching.all fun (cPid, pe) =>
      match pe.lifecycle with
      | .alive a => a.mayAutoreap && willDefinitelyDie a
      | .delayedZombie _ k ts run _ ss exitReap _ ds rs =>
        exitReap == .autoreapOnly && dzWillDefinitelyFinish cPid k ts run ss ds rs
      | .exitDead => true
      | _ => false
    let canBlockOnEntry : UInt32 × ProcEntry → Bool
      | (cPid, pe) =>
        match pe.lifecycle with
        | .alive a =>
          match a.run with
          | .running =>
            (a.auto == .controlled || hasPendingStop a) &&
              !a.pending.killed &&
              (a.pending.termSigs.isEmpty || hasPendingStop a) &&
              (!rawFlags.untraced || !a.pending.stopSigs.contains 19)
          | .stopped _ rep => (rep || !rawFlags.untraced) && !a.pending.killed
        | .delayedZombie _ k ts run _ ss _ _ ds rs =>
          !dzWillDefinitelyFinish cPid k ts run ss ds rs
        | _ => false
    let mayBlockForever :=
      !allGuaranteedAutoreap && !matching.any willDefinitelyZombieWake && matching.any canBlockOnEntry
    let flags :=
      if !rawFlags.nohang && rawFlags.isValid && !matching.isEmpty &&
          !hasConfirmedWaitable st.model.procs matching rawFlags && mayBlockForever then
        { rawFlags with nohang := true }
      else
        rawFlags
    let req := ProcessReq.waitpid pid flags
    let res ← waitpid pid flags
    let out : ProcessOutcome :=
      match res with
      | .ok wr => .waited wr
      | .error e => .err e
    match allowedStep st.model req out with
    | none =>
      return .error s!"MISMATCH waitpid cls={outcomeBucket out} pid={pid} flags={repr flags} out={repr out} procs={repr st.model.procs}"
    | some m' =>
      let mut hits' := recordHit hits "waitpid" (outcomeBucket out)
      let waitedPid? : Option UInt32 :=
        match out with
        | .waited (.exited p _) | .waited (.signaled p _ _) | .waited (.stopped p _) | .waited (.continued p) => some p
        | _ => none
      let waitedEntry? : Option ProcEntry :=
        match waitedPid? with
        | some rPid => assocGet matching rPid
        | none => none
      if flags.isValid then
        if flags.wclone && !flags.wall then
          if let some pe := waitedEntry? then
            if pe.isCloneChild then
              hits' := recordHit hits' "mode_wclone" "ok"
        if flags.wall then
          if let some pe := waitedEntry? then
            if pe.isCloneChild then
              hits' := recordHit hits' "mode_wall" "ok"
        if flags.wnothread && out == .err Errno.ECHILD && matching.isEmpty then
          if !(matchingUnreapedChildren st.model pid { flags with wnothread := false }).isEmpty then
            hits' := recordHit hits' "mode_wnothread" "ECHILD"
        if st.model.sigchld == .autoreap && out == .err Errno.ECHILD then
          let hadAutoreapChild := st.model.procs.any fun (p, pe) =>
            pe.isSigchldChild && matchesWaitSelector (effectiveSelfPgid st.model) pid p pe.pgid &&
              match pe.lifecycle with
              | .exitDead => true
              | .alive a => a.mayAutoreap
              | _ => false
          if hadAutoreapChild then
            hits' := recordHit hits' "mode_autoreap" "ECHILD"
        if st.subreaper then
          if let some rPid := waitedPid? then
            if st.children.any (fun c => c.pid == rPid && c.isSubreaperGrandchild) then
              hits' := recordHit hits' "mode_subreaper" "ok"
        if let .waited (.exited _ _) := out then
          if let some pe := waitedEntry? then
            if let .delayedZombie .. := pe.lifecycle then
              hits' := recordHit hits' "mode_delayed_zombie_exited" "ok"
      return .ok ({ st with model := m' }, hits')
  | .doKill t sig =>
    let pidOrNegPgid := resolvePid st t
    let req := ProcessReq.kill pidOrNegPgid sig
    let checkZeroPnd := sig.toLinuxNum == 0 && !st.blockedSigs.isEmpty && pidOrNegPgid == (effectiveSelfPid st.model).toInt32
    let prePnd ← if checkZeroPnd then readPendingSignals else pure []
    let res ← kill pidOrNegPgid sig
    let out : ProcessOutcome :=
      match res with
      | .ok () => .unit
      | .error e => .err e
    match allowedStep st.model req out with
    | none =>
      return .error s!"MISMATCH kill cls={outcomeBucket out} target={pidOrNegPgid} sig={repr sig} out={repr out} selfPid={st.model.selfPid} selfPgid={st.model.selfPgid} ign={repr st.model.ambientIgnoredSigs} procs={repr st.model.procs}"
    | some m' =>
      if checkZeroPnd && res.isOk then
        let postPnd ← readPendingSignals
        if postPnd.any (fun s => !prePnd.contains s && st.blockedSigs.contains s) then
          return .error s!"MISMATCH kill cls=sigzero_queued sig={repr sig} pre={repr prePnd} post={repr postPnd}"
      return .ok ({ st with model := m' }, recordHit hits "kill" (outcomeBucket out))
  | .doPidfdOpen t flags =>
    let pid := resolveU32Pid st t
    let req := ProcessReq.pidfd_open pid flags
    let hid := nextFreeHid st.model.fds st.model.nextHid
    let res ← pidfd_open pid flags
    let out : ProcessOutcome :=
      match res with
      | .ok _ => .opened hid
      | .error e => .err e
    match allowedStep st.model req out with
    | none =>
      if let .ok pfd := res then let _ ← ProcessEnv.closeFd pfd
      return .error s!"MISMATCH pidfd_open cls={outcomeBucket out} pid={pid} flags={repr flags} out={repr out} pt={st.model.pidfdThreadSupported} procs={repr st.model.procs}"
    | some m' =>
      match res with
      | .ok pfd =>
        let (fdFlags, flFlags) ←
          match ← ProcessEnv.getFdFlags pfd with
          | .ok p => pure p
          | .error e =>
            let _ ← ProcessEnv.closeFd pfd
            return .error s!"MISMATCH pidfd_open cls=fd_flags_err pid={pid} flags={repr flags} err={repr e}"
        let expNb : UInt32 := if flags.nonblock then 0x800 else 0
        if (fdFlags &&& 1) != 1 || (flFlags &&& 0x800) != expNb then
          let _ ← ProcessEnv.closeFd pfd
          return .error s!"MISMATCH pidfd_open cls=fd_flags pid={pid} flags={repr flags} fdFlags={fdFlags} flFlags={flFlags}"
        let handles' := st.handles.push { hid, raw := pfd, isPidfd := true, isClosed := false }
        return .ok ({ st with model := m', handles := handles' }, recordHit hits "pidfd_open" (outcomeBucket out))
      | .error _ =>
        return .ok ({ st with model := m' }, recordHit hits "pidfd_open" (outcomeBucket out))
  | .doPidfdSend f sig flags =>
    match resolveFd st f with
    | none => return .ok (st, hits)
    | some (hid, rawFd) =>
      let req := ProcessReq.pidfd_send_signal hid sig flags
      let targetsSelf :=
        match assocGet st.model.fds hid with
        | some (.pidfd tPid _ _) => !flags.processGroup && tPid == effectiveSelfPid st.model
        | _ => false
      let checkZeroPnd := sig.toLinuxNum == 0 && !st.blockedSigs.isEmpty && targetsSelf
      let prePnd ← if checkZeroPnd then readPendingSignals else pure []
      let res ← pidfd_send_signal rawFd sig flags
      let out : ProcessOutcome :=
        match res with
        | .ok () => .unit
        | .error e => .err e
      match allowedStep st.model req out with
      | none =>
        return .error s!"MISMATCH pidfd_send_signal cls={outcomeBucket out} hid={hid} sig={repr sig} flags={repr flags} out={repr out} fds={repr st.model.fds} procs={repr st.model.procs}"
      | some m' =>
        if checkZeroPnd && res.isOk then
          let postPnd ← readPendingSignals
          if postPnd.any (fun s => !prePnd.contains s && st.blockedSigs.contains s) then
            return .error s!"MISMATCH pidfd_send_signal cls=sigzero_queued sig={repr sig} pre={repr prePnd} post={repr postPnd}"
        return .ok ({ st with model := m' }, recordHit hits "pidfd_send_signal" (outcomeBucket out))
  | .doGetpid =>
    let res ← getpid
    let out := match res with | .ok p => ProcessOutcome.u32 p | .error e => ProcessOutcome.err e
    match allowedStep st.model .getpid out with
    | none => return .error s!"MISMATCH getpid cls={outcomeBucket out} got={repr out} model={st.model.selfPid}"
    | some m' => return .ok ({ st with model := m' }, recordHit hits "getpid" (outcomeBucket out))
  | .doGetuid =>
    let res ← getuid
    let out := match res with | .ok u => ProcessOutcome.u32 u | .error e => ProcessOutcome.err e
    match allowedStep st.model .getuid out with
    | none => return .error s!"MISMATCH getuid cls={outcomeBucket out} got={repr out} model={st.model.selfUid}"
    | some m' => return .ok ({ st with model := m' }, recordHit hits "getuid" (outcomeBucket out))

private def registerRuntimeThreads (selfPid selfPgid : UInt32) (m : ProcessSysState) :
    IO ProcessSysState := do
  let mut procs := m.procs
  try
    let entries ← System.FilePath.readDir "/proc/self/task"
    for entry in entries do
      let tidOpt ←
        try
          let txt ← IO.FS.readFile (entry.path / "status")
          pure (parseLastNspid txt)
        catch _ =>
          pure (entry.fileName.toNat?.map UInt32.ofNat)
      if let some tid := tidOpt then
        if tid != selfPid && (assocGet procs tid).isNone then
          let pe : ProcEntry :=
            { pgid := selfPgid
              canSignal := true
              sameSession := true
              role := .thread selfPid
              lifecycle := .alive { auto := .controlled } }
          procs := (tid, pe) :: procs
  catch _ =>
    pure ()
  return { m with procs := procs }

private def readAmbientIgnoredAndBlocked : IO (List UInt32) := do
  let ign ← readAmbientMaskField "SigIgn:"
  let blk ← readAmbientMaskField "SigBlk:"
  return blk.foldl (fun acc s => if acc.contains s then acc else s :: acc) ign

private def sampleHostNonLeaderTids (selfPid : UInt32) (maxCount : Nat := 16) : IO (Array UInt32) := do
  let mut out : Array UInt32 := #[]
  let mut checked : Nat := 0
  let entries ←
    try System.FilePath.readDir "/proc"
    catch _ => pure #[]
  for entry in entries do
    if out.size < maxCount && checked < 64 then
      if let some pidNat := entry.fileName.toNat? then
        let pid := UInt32.ofNat pidNat
        if pid != 0 && pid != selfPid then
          checked := checked + 1
          let tasks ←
            try System.FilePath.readDir s!"/proc/{pidNat}/task"
            catch _ => pure #[]
          for t in tasks do
            if out.size < maxCount then
              if let some tidNat := t.fileName.toNat? then
                let tid := UInt32.ofNat tidNat
                if tid != 0 && tid != pid && !out.contains tid then
                  out := out.push tid
  return out

private def probeKernelFeatures : IO (Bool × Bool) := do
  let wq ← ProcessEnv.probeKernelWatchQueue
  let pt ← ProcessEnv.probeKernelPidfdThread
  return (wq, pt)

private def runEpisode (ep : FuzzEpisode) : IO (Except (String × FuzzEpisode) HitMap) := do
  let _ ← ProcessEnv.setNofileMode 0
  let _ ← ProcessEnv.setSigchldAutoreap 0
  let _ ← ProcessEnv.setSubreaper false
  let _ ← ProcessEnv.setCoreLimit false
  ProcessEnv.clearSigMask
  for sNum in expandedSigPool do
    if sNum != 17 then
      let _ ← ProcessEnv.setSigIgn sNum false
  for sNum in ep.ambientSigIgn do
    if sNum != 17 then
      let _ ← ProcessEnv.setSigIgn sNum true
  for sNum in ep.ambientSigBlocked do
    let _ ← ProcessEnv.setSigBlock sNum true
  let ignInit ← readAmbientMaskField "SigIgn:"
  let blkInit ← readAmbientMaskField "SigBlk:"
  let ambientSigs := blkInit.foldl (fun acc s => if acc.contains s then acc else s :: acc) ignInit
  let selfPid ←
    match ← getpid with
    | .ok p => pure p
    | .error e =>
      match ep.initSelfPid? with
      | some p => pure p
      | none => return .error (s!"getpid failed unexpectedly without cached pid: {e}", ep)
  let selfPgid ← ProcessEnv.getpgrp
  let selfSid ← ProcessEnv.getsid
  let selfOrphanedPgid ← ProcessEnv.isSelfPgidOrphaned
  let selfUid ←
    match ← getuid with
    | .ok u => pure u
    | .error e =>
      match ep.initSelfUid? with
      | some u => pure u
      | none => return .error (s!"getuid failed unexpectedly without cached uid: {e}", ep)
  let hostTids ←
    if ep.closedNamespace then pure #[] else sampleHostNonLeaderTids selfPid
  let dummy? ←
    match ← pipe2 { cloexec := true } with
    | .ok (r, w) =>
      let _ ← ProcessEnv.closeFd r
      pure (some (r, w))
    | .error _ => pure none
  let mut m :=
    (((((ProcessSysState.initial selfPid selfPgid selfUid).withOpenHostPids (!ep.closedNamespace)).withAmbientIgnoredSigs ambientSigs).withAmbientSeccomp ep.ambientSeccomp).withWatchQueueSupported ep.watchQueueSupported).withPidfdThreadSupported ep.pidfdThreadSupported
  if ep.closedNamespace && ep.asPid2 then
    m := m.registerPid1Init 0 (!ep.pid1Foreign) (!ep.doSetsid)
  m ← registerRuntimeThreads selfPid selfPgid m
  let mut handles : Array TrackedFd := #[]
  if let some (r, w) := dummy? then
    let hid := nextFreeHid m.fds m.nextHid
    m := { m with fds := (hid, .closed) :: m.fds, nextHid := hid + 1 }
    handles := handles.push { hid, raw := r, isPidfd := false, isClosed := true }
    let wHid := nextFreeHid m.fds m.nextHid
    m := { m with fds := (wHid, .pipeWrite true false) :: m.fds, nextHid := wHid + 1 }
    handles := handles.push { hid := wHid, raw := w, isPidfd := false, isClosed := false }
  let initSt : LiveState :=
    { model := m
      children := #[]
      threads := #[]
      handles
      dummyPipe? := dummy?
      subreaper := false
      nofileTight := false
      blockedSigs := blkInit.toArray
      sigIgnMask := ignInit.toArray
      everBlockedSigs := ep.ambientSigBlocked
      hostThreadTids := hostTids
      initHostPgid := selfPgid
      selfSid
      selfOrphanedPgid }
  let stRef ← IO.mkRef initSt
  let mut hits : HitMap := []
  try
    for act in ep.actions do
      let curSt ← stRef.get
      match ← runOneAction curSt hits act with
      | .error msg =>
        return .error (msg, ep)
      | .ok (st', hits') =>
        stRef.set st'
        hits := hits'
    return .ok hits
  finally
    cleanupLiveState (← stRef.get)

/-- Extract stable failure-class tag so shrinking never slips into an unrelated failure mode or outcome/errno class. -/
def failureClassTag (msg : String) : String :=
  let trimmed := msg.trimAscii.toString
  if trimmed.startsWith "MISMATCH " then
    let tokens := (trimmed.drop 9).trimAscii.toString.splitOn " "
    let op := tokens.headD ""
    let cls? := tokens.findSome? fun tok =>
      if tok.startsWith "cls=" then some (tok.drop 4).toString
      else if tok.startsWith "out=" then some (tok.drop 4).toString
      else if tok.startsWith "got=" then some (tok.drop 4).toString
      else none
    match cls? with
    | some c => "MISMATCH:" ++ op ++ ":" ++ c
    | none => "MISMATCH:" ++ op
  else
    match trimmed.splitOn " " with
    | head :: _ => head
    | [] => trimmed

private def evalSubset {α : Type} (xs : Array α) (pred : Array α → IO Bool)
    (idxs : Array Nat) (seenRef : IO.Ref (Std.TreeSet (Array Nat) compare)) : IO Bool := do
  let seen ← seenRef.get
  if seen.contains idxs then
    return false
  seenRef.set (seen.insert idxs)
  pred (idxs.filterMap fun i => xs[i]?)

/-- Chunked delta-debugging (`ddmin`) shrinker with `compStart` rotation, sliding-window, and bounded pair fallback, reducing `xs` while deduplicating visited subsets. -/
def deltaShrink {α : Type} (pred : Array α → IO Bool) (xs : Array α) : IO (Array α) := do
  let mut cur := Array.range xs.size
  let seenRef ← IO.mkRef (Std.TreeSet.empty : Std.TreeSet (Array Nat) compare)
  let mut n : Nat := 2
  let mut compStart : Nat := 0
  let mut progress := true
  while progress && cur.size > 0 do
    progress := false
    while cur.size > 0 do
      if cur.size == 1 then
        if ← evalSubset xs pred #[] seenRef then
          cur := #[]
          progress := true
        break
      n := min n cur.size
      let mut shrunk := false
      for k in [:n] do
        let start := (k * cur.size) / n
        let stop := ((k + 1) * cur.size) / n
        if stop > start then
          let chunk := cur[start:stop].toArray
          if chunk.size < cur.size && (← evalSubset xs pred chunk seenRef) then
            cur := chunk
            n := 2
            compStart := 0
            shrunk := true
            progress := true
            break
      if !shrunk then
        for off in [:n] do
          let k := (compStart + off) % n
          let start := (k * cur.size) / n
          let stop := ((k + 1) * cur.size) / n
          if stop > start then
            let comp := cur[:start].toArray ++ cur[stop:].toArray
            if comp.size < cur.size && (← evalSubset xs pred comp seenRef) then
              cur := comp
              let nextN := max 2 (n - 1)
              compStart := k % nextN
              n := nextN
              shrunk := true
              progress := true
              break
      if !shrunk then
        if n >= cur.size then
          break
        n := min cur.size (n * 2)
        compStart := 0
    if cur.size ≥ 2 then
      let mut pairShrunk := false
      for w in #[2, 3, 4] do
        if w < cur.size && !pairShrunk then
          for i in [:cur.size - w + 1] do
            let cand := cur[:i].toArray ++ cur[i + w:].toArray
            if ← evalSubset xs pred cand seenRef then
              cur := cand
              n := 2
              compStart := 0
              pairShrunk := true
              progress := true
              break
      if !pairShrunk && cur.size ≤ 20 then
        for i in [:cur.size] do
          if pairShrunk then break
          for j in [i + 1 : cur.size] do
            let mut cand := Array.mkEmpty (cur.size - 2)
            for k in [:cur.size] do
              if k != i && k != j then
                cand := cand.push cur[k]!
            if ← evalSubset xs pred cand seenRef then
              cur := cand
              n := 2
              compStart := 0
              pairShrunk := true
              progress := true
              break
  return cur.filterMap fun i => xs[i]?

private def spawnSlotsForKind (nofileTight sigAuto subreaper pid1 : Bool) : SpawnKind → Bool × Bool
  | kind =>
    if nofileTight then (false, false)
    else
      match kind with
      | .controlled | .autonomous _ _ | .stopped _ | .cloneControlled | .cloneZombie _ => (true, false)
      | .zombieExit _ | .zombieSig _ _ => (!sigAuto, false)
      | .thread => (false, true)
      | .threadedChild | .delayedZombie _ _ _ | .siblingChild => (true, true)
      | .reparentedGrandchild => ((subreaper || pid1) && !sigAuto, false)

private def remapEpisodeActions (closedNs asPid2 : Bool) (origActs : Array FuzzAction) (keptIdxs : Array Nat) :
    Array FuzzAction := Id.run do
  let mut isKept := Array.replicate origActs.size false
  for k in keptIdxs do
    if k < origActs.size then
      isKept := isKept.set! k true
  let pid1 := closedNs && !asPid2
  let mut oNofile := false
  let mut oAuto := false
  let mut oSub := false
  let mut nNofile := false
  let mut nAuto := false
  let mut nSub := false
  let mut origChildMap : Array (Option Nat) := #[]
  let mut newChildCnt : Nat := 0
  let mut origThrMap : Array (Option Nat) := #[]
  let mut newThrCnt : Nat := 0
  let mut out : Array FuzzAction := Array.mkEmpty keptIdxs.size
  for i in [:origActs.size] do
    let act := origActs[i]!
    let kept := isKept[i]!
    let mapChild (idx : Nat) : Nat :=
      if origChildMap.isEmpty then 0
      else
        match origChildMap[idx % origChildMap.size]! with
        | some s => s
        | none => if newChildCnt > 0 then idx % newChildCnt else 0
    let mapThr (idx : Nat) : Nat :=
      if origThrMap.isEmpty then 0
      else
        match origThrMap[idx % origThrMap.size]! with
        | some s => s
        | none => if newThrCnt > 0 then idx % newThrCnt else 0
    let mapTarget : SymPidTarget → SymPidTarget
      | .childPid idx => .childPid (mapChild idx)
      | .negChildPgid idx => .negChildPgid (mapChild idx)
      | .threadTid idx => .threadTid (mapThr idx)
      | other => other
    let mapPgChoice (pg : Nat) : Nat :=
      let m := pg % 4
      if m == 0 then 0
      else if m == 1 || origChildMap.isEmpty then 1
      else
        match origChildMap[pg % origChildMap.size]! with
        | none => pg
        | some newSlot =>
          if newChildCnt == 0 then 1
          else
            match (List.range (4 * newChildCnt + 4)).find? (fun k => k % 4 ≥ 2 && k % newChildCnt == newSlot) with
            | some k => k
            | none => pg
    if kept then
      let mappedAct : FuzzAction :=
        match act with
        | .spawn kind pg => .spawn kind (mapPgChoice pg)
        | .movePgid ci toSelf => .movePgid (mapChild ci) toSelf
        | .doWaitpid t wf => .doWaitpid (mapTarget t) wf
        | .doKill t sig => .doKill (mapTarget t) sig
        | .doPidfdOpen t pf => .doPidfdOpen (mapTarget t) pf
        | other => other
      out := out.push mappedAct
    match act with
    | .setNofileMode mode =>
      oNofile := mode != 0
      if kept then nNofile := mode != 0
    | .setSigchld mode =>
      let isAuto := mode == 1 || mode == 2 || mode == 4
      oAuto := isAuto
      if kept then nAuto := isAuto
    | .setSubreaper en =>
      oSub := en
      if kept then nSub := en
    | .spawn kind _ =>
      let (oc, ot) := spawnSlotsForKind oNofile oAuto oSub pid1 kind
      let (nc, nt) := if kept then spawnSlotsForKind nNofile nAuto nSub pid1 kind else (false, false)
      if oc && nc then
        origChildMap := origChildMap.push (some newChildCnt)
        newChildCnt := newChildCnt + 1
      else if oc then
        origChildMap := origChildMap.push none
      else if nc then
        newChildCnt := newChildCnt + 1
      if ot && nt then
        origThrMap := origThrMap.push (some newThrCnt)
        newThrCnt := newThrCnt + 1
      else if ot then
        origThrMap := origThrMap.push none
      else if nt then
        newThrCnt := newThrCnt + 1
    | _ => pure ()
  return out

private def simplifySymPid : SymPidTarget → Option SymPidTarget
  | .childPid k => if k > 0 then some (.childPid 0) else none
  | .negChildPgid k => if k > 0 then some (.negChildPgid 0) else none
  | .threadTid k => if k > 0 then some (.threadTid 0) else none
  | .hostThreadTid k => if k > 0 then some (.hostThreadTid 0) else none
  | _ => none

private def simplifySingleAction : FuzzAction → List FuzzAction
  | .spawn kind pg =>
    let pgCands : List Nat := if pg == 0 then [] else if pg == 1 then [0] else [0, 1]
    let kindCands : List SpawnKind :=
      match kind with
      | .delayedZombie code d sc =>
        (if d > 0 && d != 8000 then [.delayedZombie code 8000 sc] else []) ++
        (if code != 0 || sc != 0 then [.delayedZombie 0 d 0] else [])
      | .autonomous d code => if code != 0 then [.autonomous d 0] else []
      | .zombieExit code => if code != 0 then [.zombieExit 0] else []
      | .cloneZombie code => if code != 0 then [.cloneZombie 0] else []
      | _ => []
    (pgCands.map (FuzzAction.spawn kind)) ++ (kindCands.map (FuzzAction.spawn · pg))
  | .doWaitpid t wf =>
    let defWf : WaitFlags := {}
    let nhWf : WaitFlags := { nohang := true }
    let unWf : WaitFlags := { nohang := wf.nohang, untraced := true }
    let tCands : List FuzzAction :=
      match simplifySymPid t with
      | some t' => [FuzzAction.doWaitpid t' wf]
      | none => []
    let base : List WaitFlags :=
      (if wf != defWf then [defWf] else []) ++
      (if wf.nohang && wf != nhWf then [nhWf] else []) ++
      (if wf.untraced && wf != unWf then [unWf] else []) ++
      (if wf.extraBits > 1 then [({ extraBits := 1 } : WaitFlags)] else [])
    tCands ++ base.map (FuzzAction.doWaitpid t)
  | .doKill t sig =>
    match simplifySymPid t with
    | some t' => [.doKill t' sig]
    | none => []
  | .doPipe2 pf =>
    let defPf : PipeFlags := {}
    ((if pf != defPf && pf.extraBits == 0 then [defPf] else []) ++
     (if pf.extraBits > 1 then [({ extraBits := 1 } : PipeFlags)] else [])).map FuzzAction.doPipe2
  | .doPidfdOpen t pf =>
    let defPof : PidfdOpenFlags := {}
    let tCands : List FuzzAction :=
      match simplifySymPid t with
      | some t' => [FuzzAction.doPidfdOpen t' pf]
      | none => []
    tCands ++
    ((if pf != defPof && pf.extraBits == 0 then [defPof] else []) ++
     (if pf.extraBits > 1 then [({ extraBits := 1 } : PidfdOpenFlags)] else [])).map (FuzzAction.doPidfdOpen t)
  | .doPidfdSend f sig pf =>
    let f' : SymFdTarget :=
      match f with
      | .openPidfd k => if k > 0 then .openPidfd 0 else f
      | .openPipe k => if k > 0 then .openPipe 0 else f
      | .closedFd k => if k > 0 then .closedFd 0 else f
      | .fallbackClosed => .fallbackClosed
    (if f' != f then [FuzzAction.doPidfdSend f' sig pf] else []) ++
    (if pf.extraBits > 1 then [FuzzAction.doPidfdSend f sig { pf with extraBits := 1 }] else [])
  | .closeHandle idx => if idx > 0 then [.closeHandle 0] else []
  | .movePgid idx toSelf => if idx > 0 then [.movePgid 0 toSelf] else []
  | _ => []

private def simplifyActions (pred : Array FuzzAction → IO Bool) (acts : Array FuzzAction) :
    IO (Array FuzzAction) := do
  let mut cur := acts
  if cur.size ≤ 16 then
    for i in [:cur.size] do
      for cand in simplifySingleAction cur[i]! do
        let next := cur.set! i cand
        if ← pred next then
          cur := next
          break
  return cur

private def shrinkActionsWithRemap (closedNs asPid2 : Bool) (pred : Array FuzzAction → IO Bool)
    (origActs : Array FuzzAction) : IO (Array FuzzAction) := do
  if origActs.isEmpty then
    return #[]
  let fullIdxs := Array.range origActs.size
  let useRemap ← pred (remapEpisodeActions closedNs asPid2 origActs fullIdxs)
  let minActs0 ←
    if useRemap then
      let minIdxs ← deltaShrink (fun idxs => pred (remapEpisodeActions closedNs asPid2 origActs idxs)) fullIdxs
      pure (remapEpisodeActions closedNs asPid2 origActs minIdxs)
    else
      deltaShrink pred origActs
  simplifyActions pred minActs0

/-- Deterministic self-test for `deltaShrink`, slot-preserving spawn shrinking, parameter canonicalization, and `failureClassTag` pinning. -/
def runShrinkSelfTest : IO Unit := do
  let noise := FuzzAction.doGetpid
  let mut trace : Array FuzzAction := #[]
  for _ in [:8] do trace := trace.push noise
  trace := trace.push (.spawn .controlled 0)
  for _ in [:8] do trace := trace.push noise
  trace := trace.push (.doKill (.childPid 0) .sigterm)
  for _ in [:8] do trace := trace.push noise
  let oracle (arr : Array FuzzAction) : IO Bool := do
    let hasSpawn := arr.any fun | .spawn .controlled _ => true | _ => false
    let hasKill := arr.any fun | .doKill (.childPid _) .sigterm => true | _ => false
    return hasSpawn && hasKill
  let shrunk ← deltaShrink oracle trace
  if shrunk.size != 2 then
    throw (IO.userError s!"shrink self-test failed: expected size 2, got {shrunk.size} ({repr shrunk})")
  let mut slipTrace : Array FuzzAction := #[]
  for _ in [:6] do slipTrace := slipTrace.push (.doGetuid)
  slipTrace := slipTrace.push .doGetpid
  slipTrace := slipTrace.push (.doPipe2 {})
  for _ in [:6] do slipTrace := slipTrace.push (.doGetuid)
  let evalSlip (arr : Array FuzzAction) : Option String :=
    let hasGetpid := arr.any fun | .doGetpid => true | _ => false
    let hasPipe := arr.any fun | .doPipe2 _ => true | _ => false
    if hasGetpid && hasPipe then some "MISMATCH waitpid cls=ok:exited pid=1"
    else if hasGetpid then some "MISMATCH kill cls=EPERM target=1"
    else none
  let origSlipMsg := (evalSlip slipTrace).getD ""
  let slipTag := failureClassTag origSlipMsg
  let slipPred (arr : Array FuzzAction) : IO Bool := do
    match evalSlip arr with
    | some m => return failureClassTag m == slipTag
    | none => return false
  let slipShrunk ← deltaShrink slipPred slipTrace
  let expectedSlip := #[FuzzAction.doGetpid, FuzzAction.doPipe2 {}]
  if slipShrunk != expectedSlip then
    throw (IO.userError s!"shrink slippage self-test failed: expected {repr expectedSlip}, got {repr slipShrunk}")
  let evalSameOp (arr : Array FuzzAction) : Option String :=
    let hasGetpid := arr.any fun | .doGetpid => true | _ => false
    let hasPipe := arr.any fun | .doPipe2 _ => true | _ => false
    if hasGetpid && hasPipe then some "MISMATCH waitpid cls=ok:exited pid=1"
    else if hasGetpid then some "MISMATCH waitpid cls=ECHILD pid=1"
    else none
  let sameOpTag := failureClassTag ((evalSameOp slipTrace).getD "")
  let sameOpShrunk ← deltaShrink (fun arr =>
    match evalSameOp arr with
    | some m => return failureClassTag m == sameOpTag
    | none => return false) slipTrace
  if sameOpShrunk != expectedSlip then
    throw (IO.userError s!"shrink same-op outcome slippage self-test failed: expected {repr expectedSlip}, got {repr sameOpShrunk}")
  let simCoupled (arr : Array FuzzAction) : IO Bool := do
    let mut hasChild := false
    let mut openHandles : Array (String × Bool) := #[("dummy_pipe", true)]
    for act in arr do
      match act with
      | .spawn .controlled _ => hasChild := true
      | .doPidfdOpen .selfPid _ => openHandles := openHandles.push ("self_pfd", true)
      | .doPidfdOpen (.childPid _) _ =>
        if hasChild then openHandles := openHandles.push ("child_pfd", true)
      | .closeHandle idx =>
        let mut openIdxs : Array Nat := #[]
        for i in [:openHandles.size] do
          if openHandles[i]!.2 then openIdxs := openIdxs.push i
        if let some realIdx := openIdxs[idx % max 1 openIdxs.size]? then
          let (tag, _) := openHandles[realIdx]!
          openHandles := openHandles.set! realIdx (tag, false)
      | .doPidfdSend (.openPidfd idx) .sigterm _ =>
        let openPidfds := openHandles.filter fun (tag, isOpen) =>
          isOpen && (tag == "self_pfd" || tag == "child_pfd")
        if !openPidfds.isEmpty then
          if openPidfds[idx % openPidfds.size]!.1 == "child_pfd" then
            return true
      | _ => pure ()
    return false
  let coupled1 : Array FuzzAction := #[
    .doPidfdOpen .selfPid {},
    .spawn .controlled 0,
    .doPidfdOpen .selfPid {},
    .doPidfdOpen (.childPid 0) {},
    .doPidfdSend (.openPidfd 2) .sigterm {}
  ]
  let cShrunk1 ← deltaShrink simCoupled coupled1
  if cShrunk1.size != 3 then
    throw (IO.userError s!"coupled pidfd shrink failed: expected size 3, got {cShrunk1.size}")
  let coupled2 : Array FuzzAction := #[
    .spawn .controlled 0,
    .doPidfdOpen .selfPid {},
    .doPidfdOpen (.childPid 0) {},
    .closeHandle 1,
    .doPidfdSend (.openPidfd 0) .sigterm {}
  ]
  let cShrunk2 ← deltaShrink simCoupled coupled2
  if cShrunk2.size != 3 then
    throw (IO.userError s!"coupled close shrink failed: expected size 3, got {cShrunk2.size}")
  let simModuloStop (arr : Array FuzzAction) : IO Bool := do
    let mut children : Array (Bool × Bool) := #[]
    for act in arr do
      match act with
      | .spawn .cloneControlled _ => children := children.push (true, false)
      | .spawn .controlled _ => children := children.push (false, false)
      | .doKill (.childPid idx) .sigstop =>
        if !children.isEmpty then
          let k := idx % children.size
          let (isTarget, _) := children[k]!
          children := children.set! k (isTarget, true)
      | .doWaitpid (.childPid idx) wf =>
        if !children.isEmpty && wf.nohang && wf.untraced then
          let (isTarget, isStopped) := children[idx % children.size]!
          if isTarget && isStopped then
            return true
      | _ => pure ()
    return false
  let modTrace : Array FuzzAction := #[
    .spawn .cloneControlled 12345,
    .doGetpid,
    .spawn .controlled 4,
    .spawn .controlled 8,
    .spawn .controlled 12,
    .spawn .controlled 16,
    .spawn .controlled 20,
    .spawn .controlled 24,
    .doGetuid,
    .doKill (.childPid 0) .sigstop,
    .doGetpid,
    .doWaitpid (.childPid 7) { nohang := true, untraced := true, continued := true },
    .doGetuid
  ]
  let modShrunk ← shrinkActionsWithRemap true false simModuloStop modTrace
  let expectedMod : Array FuzzAction := #[
    .spawn .cloneControlled 0,
    .doKill (.childPid 0) .sigstop,
    .doWaitpid (.childPid 0) { nohang := true, untraced := true }
  ]
  if modShrunk != expectedMod then
    throw (IO.userError s!"modulo-coupled shrink self-test failed: expected {repr expectedMod}, got {repr modShrunk}")
  IO.println s!"PROCESS_SHRINK_SELF_TEST: ok (reduced {trace.size} -> {shrunk.size} actions, pinned {slipTag}, coupled=3, mod=3)"

private def shrinkFailingEpisode (ep : FuzzEpisode) (origMsg : String) : IO (FuzzEpisode × String) := do
  let origTag := failureClassTag origMsg
  let lastMsg ← IO.mkRef origMsg
  let testEp (candEp : FuzzEpisode) : IO Bool := do
    match ← runEpisode candEp with
    | .error (m, _) =>
      if failureClassTag m == origTag then
        lastMsg.set m
        return true
      else
        return false
    | .ok _ => return false
  let minActs ← shrinkActionsWithRemap ep.closedNamespace ep.asPid2 (fun acts => testEp { ep with actions := acts }) ep.actions
  let mut curEp := { ep with actions := minActs }
  if !curEp.ambientSigIgn.isEmpty then
    if ← testEp { curEp with ambientSigIgn := #[] } then
      curEp := { curEp with ambientSigIgn := #[] }
    else if curEp.ambientSigIgn.size > 1 then
      for s in curEp.ambientSigIgn do
        if ← testEp { curEp with ambientSigIgn := #[s] } then
          curEp := { curEp with ambientSigIgn := #[s] }
          break
  if !curEp.ambientSigBlocked.isEmpty then
    if ← testEp { curEp with ambientSigBlocked := #[] } then
      curEp := { curEp with ambientSigBlocked := #[] }
  let msg ← lastMsg.get
  return (curEp, msg)

private def runNsFuzzSteps (seed : UInt64) (closedNs doSetsid asPid2 watchQueue pidfdThread ambientSeccomp : Bool)
    (targetSteps : Nat) (initSelfPid? : Option UInt32 := none) (initSelfUid? : Option UInt32 := none)
    (pid1Foreign : Bool := false) (secOp? : Option UInt8 := none)
    (dropCapKill : Bool := false) (secErrno : UInt32 := 0) : IO UInt32 := do
  let workerInitPg ← ProcessEnv.getpgrp
  let mut r := Rng.seed seed
  let mut totalSteps : Nat := 0
  let mut hits : HitMap := []
  while totalSteps < targetSteps do
    let epSeed := r.state
    let remaining := targetSteps - totalSteps
    let maxActs := min 80 (max 24 (remaining * 2))
    let (ep, r') := generateEpisode r closedNs doSetsid asPid2 watchQueue pidfdThread maxActs ambientSeccomp pid1Foreign initSelfPid? initSelfUid? secOp? dropCapKill secErrno
    r := r'
    match ← runEpisode ep with
    | .ok epHits =>
      hits := mergeHitMaps hits epHits
      let stepCount := (ep.actions.filter isSyscallAction).size
      totalSteps := totalSteps + max 1 stepCount
      let curPg ← ProcessEnv.getpgrp
      if curPg != workerInitPg then
        if workerInitPg != 0 then
          let _ ← ProcessEnv.setpgid 0 workerInitPg
        if (← ProcessEnv.getpgrp) != workerInitPg then
          break
    | .error (msg, badEp) =>
      let curPg ← ProcessEnv.getpgrp
      if curPg != workerInitPg || badEp.actions.contains .moveSelfPgid then
        IO.println s!"NS_FUZZ_REPLAY_NEEDED:{epSeed}:{maxActs}:{badEp.actions.size}"
        IO.eprintln msg
        return 43
      let (minEp, minMsg) ← shrinkFailingEpisode badEp msg
      IO.eprintln s!"PROCESS_FUZZ_NS_FAILURE: {msg}"
      IO.eprintln s!"MINIMAL_FAILURE: {minMsg}"
      IO.eprintln s!"MINIMAL_EPISODE: {repr minEp}"
      return 1
  if pid1Foreign then IO.println "NS_FUZZ_FOREIGN_UID=1"
  IO.println s!"NS_FUZZ_DONE steps={totalSteps}"
  IO.println s!"NS_FUZZ_HITS:{formatHitsCompact hits}"
  return 0

private def readSubIdStart (path user : String) : IO (Option String) := do
  if user.isEmpty then return none
  try
    let txt ← IO.FS.readFile path
    for line in txt.splitOn "\n" do
      match line.splitOn ":" with
      | u :: start :: _ =>
        if u == user && !start.isEmpty then return some start
      | _ => pure ()
    return none
  catch _ => return none

private def resolveCurrentUser : IO String := do
  if let some u ← IO.getEnv "USER" then
    if !u.isEmpty then return u
  if let some u ← IO.getEnv "LOGNAME" then
    if !u.isEmpty then return u
  try
    let out ← IO.Process.output { cmd := "id", args := #["-un"] }
    if out.exitCode == 0 then
      return out.stdout.trimAscii.toString
    return ""
  catch _ =>
    return ""

private def buildWorkerSubidEnv (requireNs : Bool) : IO (Except String (Array (String × Option String))) := do
  let user ← resolveCurrentUser
  let su? ← readSubIdStart "/etc/subuid" user
  let sg? ← readSubIdStart "/etc/subgid" user
  if requireNs && (su?.isNone || sg?.isNone) then
    return .error s!"REQUIRE_NS_FAILED: /etc/subuid or /etc/subgid entry missing for user '{user}' (install uidmap and allocate subuids/subgids via usermod)"
  let mut env : Array (String × Option String) := #[]
  if let some su := su? then
    env := env.push ("LEANSWE_SUBUID", some su)
  if let some sg := sg? then
    env := env.push ("LEANSWE_SUBGID", some sg)
  return .ok env

private structure ReplayConfig where
  closedNs : Bool
  doSetsid : Bool
  asPid2 : Bool
  mapUid : Bool
  dropCapKill : Bool
  ambientSeccomp : Bool
  opKind : UInt8
  errNum : UInt32
  strictSubid : Bool
  remapSlots : Bool := false
  dropIgn : Bool := false
  dropBlk : Bool := false

private def formatReplayArg (cfg : ReplayConfig) (epSeed : UInt64) (maxActs : Nat) (idxs : Array Nat) (printEp : Bool) : String :=
  let b (v : Bool) := if v then "1" else "0"
  let csv := if idxs.isEmpty then "empty" else String.intercalate "," (idxs.toList.map toString)
  let prefixTag := if printEp then "P" else "R"
  s!"{b cfg.closedNs}:{epSeed}:{maxActs}:{b cfg.doSetsid}:{b cfg.asPid2}:{b cfg.mapUid}:{b cfg.dropCapKill}:{b cfg.ambientSeccomp}:{cfg.opKind}:{cfg.errNum}:{b cfg.strictSubid}:{b cfg.remapSlots}:{b cfg.dropIgn}:{b cfg.dropBlk}:{prefixTag}:{csv}"

private def resolveSelfExe : IO String := do
  try
    return (← IO.FS.realPath "/proc/self/exe").toString
  catch _ =>
    try
      return (← IO.appPath).toString
    catch _ =>
      return "/proc/self/exe"

private def runReplayProbe (subidEnv : Array (String × Option String)) (cfg : ReplayConfig)
    (epSeed : UInt64) (maxActs : Nat) (idxs : Array Nat) (printEp : Bool := false) :
    IO (UInt32 × String × String) := do
  let exe ← resolveSelfExe
  let mode := if cfg.closedNs then "fuzz-replay-spawn" else "fuzz-replay-host"
  let arg := formatReplayArg cfg epSeed maxActs idxs printEp
  let workerEnv := (subidEnv.filter (·.1 != "LEAN_NUM_THREADS")).push ("LEAN_NUM_THREADS", some "1")
  let out ← IO.Process.output {
    cmd := exe
    args := #["--suite", "process", "--ns-worker", mode, arg]
    env := workerEnv
  }
  return (out.exitCode, out.stdout, out.stderr)

private def shrinkViaReplay (subidEnv : Array (String × Option String)) (cfg : ReplayConfig)
    (epSeed : UInt64) (maxActs numActs : Nat) (initMsg : String) : IO String := do
  let origTag := failureClassTag initMsg
  let lastMsg ← IO.mkRef initMsg
  let checkProbe (probeCfg : ReplayConfig) (idxs : Array Nat) : IO Bool := do
    let (rc, _, errOut) ← runReplayProbe subidEnv probeCfg epSeed maxActs idxs false
    let trimmedErr := errOut.trimAscii.toString
    if rc == 42 && failureClassTag trimmedErr == origTag then
      lastMsg.set trimmedErr
      return true
    else
      return false
  let fullIdxs := Array.range numActs
  let canRemap ← if numActs > 0 then checkProbe { cfg with remapSlots := true } fullIdxs else pure false
  let mut activeCfg := { cfg with remapSlots := canRemap }
  let minIdxs ← deltaShrink (checkProbe activeCfg) fullIdxs
  if ← checkProbe { activeCfg with dropIgn := true } minIdxs then
    activeCfg := { activeCfg with dropIgn := true }
  if ← checkProbe { activeCfg with dropBlk := true } minIdxs then
    activeCfg := { activeCfg with dropBlk := true }
  let (finalRc, _, finalErr) ← runReplayProbe subidEnv activeCfg epSeed maxActs minIdxs true
  let minMsg ← lastMsg.get
  let trimmedFinal := finalErr.trimAscii.toString
  let replayMode := if activeCfg.closedNs then "fuzz-replay-spawn" else "fuzz-replay-host"
  let replayArg := formatReplayArg activeCfg epSeed maxActs minIdxs false
  let epTail :=
    if finalRc == 42 && !trimmedFinal.isEmpty then trimmedFinal
    else s!"MINIMAL_EPISODE: seed={epSeed} maxActs={maxActs} idxs={repr minIdxs}"
  return s!"PROCESS_FUZZ_NS_FAILURE: {initMsg}\nMINIMAL_FAILURE: {minMsg}\nREPLAY_CMD: --suite process --ns-worker {replayMode} {replayArg}\n{epTail}"

private def parseReplayNeeded? (stdout : String) : Option (UInt64 × Nat × Nat) :=
  (stdout.splitOn "\n").findSome? fun ln =>
    if ln.startsWith "NS_FUZZ_REPLAY_NEEDED:" then
      match (ln.drop 22).trimAscii.toString.splitOn ":" with
      | [sStr, mStr, nStr] =>
        match sStr.toNat?, mStr.toNat?, nStr.toNat? with
        | some s, some m, some n => some (s.toUInt64, m, n)
        | _, _, _ => none
      | _ => none
    else
      none

private def runWorkerWithCapture (subidEnv : Array (String × Option String)) (mode arg : String)
    (_fallbackSteps : Nat) (replayCfg? : Option ReplayConfig := none) : IO (Except String (Nat × HitMap × Bool)) := do
  let exe ← resolveSelfExe
  let workerEnv := (subidEnv.filter (·.1 != "LEAN_NUM_THREADS")).push ("LEAN_NUM_THREADS", some "1")
  let out ← IO.Process.output {
    cmd := exe
    args := #["--suite", "process", "--ns-worker", mode, arg]
    env := workerEnv
  }
  if out.exitCode == 43 then
    if let (some cfg, some (epSeed, maxActs, numActs)) := (replayCfg?, parseReplayNeeded? out.stdout) then
      let shrunkMsg ← shrinkViaReplay subidEnv cfg epSeed maxActs numActs out.stderr.trimAscii.toString
      return .error shrunkMsg
  if out.exitCode != 0 then
    return .error s!"worker failure ({mode} {arg}, rc={out.exitCode}): {out.stderr}"
  let lines := out.stdout.splitOn "\n"
  let mut parsedSteps? : Option Nat := none
  let mut parsedHits : HitMap := []
  let mut foreignUid := false
  for ln in lines do
    if ln.trimAscii.toString == "NS_FUZZ_FOREIGN_UID=1" then
      foreignUid := true
    else if ln.startsWith "NS_FUZZ_DONE steps=" then
      if let some n := (ln.drop 19).trimAscii.toString.toNat? then
        parsedSteps? := some n
    else if ln.startsWith "NS_FUZZ_HITS:" then
      parsedHits := mergeHitMaps parsedHits (parseHitsCompact (ln.drop 13).trimAscii.toString)
  match parsedSteps? with
  | some n => return .ok (n, parsedHits, foreignUid)
  | none => return .error s!"worker failure ({mode} {arg}): exited 0 without NS_FUZZ_DONE"

private def runNsFuzzWithCapture (subidEnv : Array (String × Option String))
    (doSetsid asPid2 mapUid dropCapKill strictSubid : Bool) (seed : UInt64)
    (steps : Nat) : IO (Except String (Nat × HitMap × Bool)) := do
  let sBit := if doSetsid then 1 else 0
  let pBit := if asPid2 then 1 else 0
  let mBit := if mapUid then 1 else 0
  let dBit := if dropCapKill then 1 else 0
  let xBit := if strictSubid then 1 else 0
  let cfg : ReplayConfig :=
    { closedNs := true, doSetsid, asPid2, mapUid, dropCapKill, ambientSeccomp := false, opKind := 0, errNum := 1, strictSubid }
  let mut curR := Rng.seed seed
  let mut accSteps : Nat := 0
  let mut accHits : HitMap := []
  let mut accForeign := false
  let mut subTries : Nat := 0
  while accSteps < steps && subTries < 24 do
    subTries := subTries + 1
    let rem := max 1 (steps - accSteps)
    let curSeed := if subTries == 1 then seed else curR.state
    let (_, rNext) := curR.nextU64
    curR := rNext
    match ← runWorkerWithCapture subidEnv "fuzz-ns-spawn" s!"{curSeed}:{sBit}:{pBit}:{mBit}:{dBit}:{rem}:{xBit}" rem (some cfg) with
    | .ok (n, h, f) =>
      accSteps := accSteps + max 1 n
      accHits := mergeHitMaps accHits h
      if f then accForeign := true
    | .error errMsg =>
      return .error errMsg
  return .ok (accSteps, accHits, accForeign)

private def pickSeccompErrno (r : Rng) : UInt32 × Rng :=
  let (useBoundary, r1) := r.chance 1 2
  let (errNum, r2) :=
    if useBoundary then
      r1.pickArray #[1, 3, 10, 12, 13, 22, 24, 38, 95, 4095] 1
    else
      let (u, r') := r1.nextU32
      (UInt32.ofNat ((u.toNat % 4095) + 1), r')
  (if errNum == 14 then 15 else errNum, r2)

private def runSeccompFuzzWithCapture (subidEnv : Array (String × Option String))
    (useNs doSetsid asPid2 mapUid dropCapKill strictSubid : Bool) (seed : UInt64) (opKind : UInt8)
    (errNum : UInt32) (steps : Nat) : IO (Except String (Nat × HitMap × Bool)) :=
  let mode := if useNs then "fuzz-seccomp-ns" else "fuzz-seccomp-host"
  let closedFlag := if useNs then 1 else 0
  let sidFlag := if doSetsid then 1 else 0
  let pid2Flag := if asPid2 then 1 else 0
  let mapFlag := if mapUid then 1 else 0
  let capFlag := if dropCapKill then 1 else 0
  let xFlag := if strictSubid then 1 else 0
  let cfg : ReplayConfig :=
    { closedNs := useNs, doSetsid, asPid2, mapUid, dropCapKill, ambientSeccomp := true, opKind, errNum, strictSubid }
  runWorkerWithCapture subidEnv mode s!"{closedFlag}:{seed}:{opKind}:{errNum}:{steps}:{sidFlag}:{pid2Flag}:{mapFlag}:{capFlag}:{xFlag}" steps (some cfg)

private def runHostFuzzWithCapture (subidEnv : Array (String × Option String))
    (seed : UInt64) (steps : Nat) : IO (Except String (Nat × HitMap × Bool)) :=
  let cfg : ReplayConfig :=
    { closedNs := false, doSetsid := false, asPid2 := false, mapUid := false, dropCapKill := false, ambientSeccomp := false, opKind := 0, errNum := 1, strictSubid := false }
  runWorkerWithCapture subidEnv "fuzz-host-spawn" s!"{seed}:{steps}" steps (some cfg)

private def setupWorkerEnv (closedNs asPid2 mapUid dropCap strictSubid : Bool) : IO (Except UInt32 Bool) := do
  if closedNs then
    match ← getpid with
    | .ok 1 =>
      let _ ← ProcessEnv.setSigIgn 7 false
      let _ ← ProcessEnv.setSigIgn 11 false
    | _ => pure ()
  let mut pid1Foreign := false
  if closedNs && asPid2 && mapUid then
    match ← getuid with
    | .ok 0 =>
      match ← ProcessEnv.dropToNobody with
      | .ok () => pid1Foreign := true
      | .error e =>
        if strictSubid then
          IO.eprintln s!"REQUIRE_NS_FAILED: dropToNobody failed for pid1Foreign: {e}"
          return .error 1
    | .ok u =>
      if strictSubid then
        IO.eprintln s!"REQUIRE_NS_FAILED: expected uid 0 inside mapped namespace before dropToNobody, got {u}"
        return .error 1
      if dropCap then
        let _ ← ProcessEnv.dropCapKill
    | .error e =>
      if strictSubid then
        IO.eprintln s!"REQUIRE_NS_FAILED: getuid failed before dropToNobody: {e}"
        return .error 1
  else if dropCap then
    let _ ← ProcessEnv.dropCapKill
  return .ok pid1Foreign

private def parseReplayIndices (csv : String) : Array Nat :=
  if csv == "empty" || csv.isEmpty then #[]
  else
    (csv.splitOn ",").foldl (fun acc tok =>
      match tok.toNat? with
      | some idx => acc.push idx
      | none => acc) #[]

/-- Entrypoint for isolated namespace worker probes and fuzzing (`--suite process --ns-worker <mode> <arg>`). -/
def nsWorkerMain (mode arg : String) (_rest : List String) : IO UInt32 := do
  match mode with
  | "kill-eperm" =>
    match ← getuid with
    | .ok 0 =>
      let _ ← ProcessEnv.dropToNobody
    | _ => pure ()
    let selfP := (← getpid).toOption.getD 0
    let mut targets : Array Int32 := #[]
    if let some parsed := arg.toNat? then
      if parsed > 0 && UInt32.ofNat parsed != selfP then
        targets := targets.push (Int32.ofNat parsed)
    if selfP != 1 then
      targets := targets.push 1
    for target in targets do
      if let .error e := (← kill target .sigzero) then
        if e == Errno.EPERM || e == Errno.EACCES then return 0
    return 1
  | "pidfd-eperm" =>
    match ← getuid with
    | .ok 0 =>
      let _ ← ProcessEnv.dropToNobody
    | _ => pure ()
    let selfP := (← getpid).toOption.getD 0
    let mut targets : Array UInt32 := #[]
    if let some parsed := arg.toNat? then
      if parsed > 0 && UInt32.ofNat parsed != selfP then
        targets := targets.push (UInt32.ofNat parsed)
    if selfP != 1 then
      targets := targets.push 1
    for target in targets do
      if let .ok pfd := (← pidfd_open target {}) then
        let r ← pidfd_send_signal pfd .sigzero {}
        let _ ← ProcessEnv.closeFd pfd
        if let .error e := r then
          if e == Errno.EPERM || e == Errno.EACCES then return 0
    return 1
  | "kill-neg1-foreign-spawn" =>
    match ← buildWorkerSubidEnv false with
    | .error _ => return 0
    | .ok subidEnv =>
      if subidEnv.size < 2 then return 0
      let exe ← resolveSelfExe
      let workerEnv := (subidEnv.filter (·.1 != "LEAN_NUM_THREADS")).push ("LEAN_NUM_THREADS", some "1")
      let out ← IO.Process.output {
        cmd := exe
        args := #["--suite", "process", "--ns-worker", "kill-neg1-foreign-ns", "0"]
        env := workerEnv
      }
      if out.exitCode == 125 && arg != "strict" then
        return 0
      if out.exitCode != 0 then
        IO.eprintln s!"kill-neg1-foreign-ns failed (rc={out.exitCode}): {out.stderr}"
        return 1
      return 0
  | "kill-neg1-foreign-ns" =>
    match ← ProcessEnv.runNsWorker true 14 "kill-neg1-foreign" "0" with
    | .ok rc => return rc
    | .error e =>
      IO.eprintln s!"runNsWorker kill-neg1-foreign failed: {e}"
      return 1
  | "kill-neg1-foreign" =>
    let selfP ← match ← getpid with | .ok p => pure p | .error _ => return 1
    let selfPg ← ProcessEnv.getpgrp
    match ← ProcessEnv.spawnControlled 0 false with
    | .error e =>
      IO.eprintln s!"kill-neg1-foreign: spawnControlled failed {e}"
      return 2
    | .ok (cPid, cPg) =>
      match ← ProcessEnv.dropToNobody with
      | .error e =>
        ProcessEnv.cleanupChild cPid
        IO.eprintln s!"kill-neg1-foreign: dropToNobody failed {e}"
        return 3
      | .ok () =>
        let rUid ← getuid
        if (match rUid with | .ok 65534 => false | _ => true) then
          IO.eprintln "kill-neg1-foreign: expected uid 65534 after dropToNobody"
          return 4
        let rK1 ← kill cPid.toInt32 .sigzero
        if (match rK1 with | .error e => e != Errno.EPERM | .ok () => true) then
          IO.eprintln "kill-neg1-foreign: expected EPERM on kill(cPid, 0)"
          return 5
        let rKg ← kill (-(cPg.toInt32)) .sigzero
        if (match rKg with | .error e => e != Errno.EPERM | .ok () => true) then
          IO.eprintln "kill-neg1-foreign: expected EPERM on kill(-cPg, 0)"
          return 6
        let rBad ← kill (-1) (.raw 999)
        if (match rBad with | .error e => e != Errno.EINVAL | .ok () => true) then
          IO.eprintln "kill-neg1-foreign: expected EINVAL on kill(-1, 999)"
          return 7
        if !(← kill (-1) .sigzero).isOk then
          IO.eprintln "kill-neg1-foreign: expected ok on kill(-1, 0) with unowned pid > 1"
          return 8
        if !(← kill (-1) .sigterm).isOk then
          IO.eprintln "kill-neg1-foreign: expected ok on kill(-1, SIGTERM) with unowned pid > 1"
          return 9
        let rWait ← waitpid cPid.toInt32 { nohang := true }
        let badWait : Bool := match rWait with | .ok w => w != .stillRunning | .error _ => true
        if badWait then
          IO.eprintln "kill-neg1-foreign: unowned child unexpectedly signaled by kill(-1, SIGTERM)"
          return 10
        let s := ((ProcessSysState.initial selfP selfPg 65534).registerForeignProc 1 1 false false).registerForeignProc cPid cPg false false
        let (mkRes, mkSt) := (modelOps.kill (-1) .sigterm).run s
        if !mkRes.isOk || mkSt != s then
          IO.eprintln "kill-neg1-foreign: modelOps.kill (-1) mismatch"
          return 11
        if (allowedStep s (.kill (-1) .sigterm) .unit) != some s then
          IO.eprintln "kill-neg1-foreign: allowedStep rejected .unit on kill(-1)"
          return 12
        if (allowedStep s (.kill (-1) .sigterm) (.err Errno.EPERM)).isSome then
          IO.eprintln "kill-neg1-foreign: allowedStep falsely accepted EPERM on kill(-1)"
          return 13
        return 0
  | "zero-pgid" =>
    let pg ← ProcessEnv.getpgrp
    if pg != 0 then
      IO.eprintln s!"zero-pgid: expected getpgrp=0, got {pg}"
      return 1
    match ← kill 0 .sigzero with
    | .ok () => pure ()
    | .error e =>
      IO.eprintln s!"zero-pgid: expected kill(0, 0)=ok, got {e}"
      return 2
    match ← ProcessEnv.spawnControlled 0 false with
    | .error e =>
      IO.eprintln s!"zero-pgid: spawnControlled failed {e}"
      return 3
    | .ok (cpid, cpg) =>
      try
        if cpg != cpid then
          IO.eprintln s!"zero-pgid: expected child pgid={cpid}, got {cpg}"
          return 4
        match ← waitpid 0 { nohang := true } with
        | .error e =>
          if e != Errno.ECHILD then
            IO.eprintln s!"zero-pgid: expected waitpid(0, WNOHANG)=ECHILD, got {e}"
            return 5
        | .ok wr =>
          IO.eprintln s!"zero-pgid: expected waitpid(0, WNOHANG)=ECHILD, got {repr wr}"
          return 5
        match ← waitpid (-1) { nohang := true } with
        | .ok .stillRunning => pure ()
        | other =>
          IO.eprintln s!"zero-pgid: expected waitpid(-1, WNOHANG)=stillRunning, got {repr other}"
          return 6
        return 0
      finally
        ProcessEnv.cleanupChild cpid
  | "pid1-unkillable" =>
    let p ←
      match ← getpid with
      | .ok v => pure v
      | .error e =>
        IO.eprintln s!"pid1-unkillable: getpid failed {e}"
        return 1
    if p != 1 && p != 2 then
      IO.eprintln s!"pid1-unkillable: expected getpid in (1 or 2), got {p}"
      return 1
    for sig in #[Signal.sigzero, .sigterm, .sigkill, .sigstop] do
      match ← kill 1 sig with
      | .ok () => pure ()
      | .error e =>
        IO.eprintln s!"pid1-unkillable: kill 1 {repr sig} failed with {e}"
        return 2
    match ← pidfd_open 1 {} with
    | .error e =>
      IO.eprintln s!"pid1-unkillable: pidfd_open 1 failed {e}"
      return 3
    | .ok pfd =>
      let r ← pidfd_send_signal pfd .sigkill {}
      let _ ← ProcessEnv.closeFd pfd
      match r with
      | .ok () => pure ()
      | .error e =>
        IO.eprintln s!"pidfd_send_signal failed {e}"
        return 4
    return 0
  | "check-uid0" =>
    match ← getuid with
    | .ok 0 => return 0
    | other =>
      IO.eprintln s!"check-uid0: expected ok 0, got {repr other}"
      return 1
  | "orphan-tty-cont" =>
    let selfPid ← match ← getpid with | .ok p => pure p | .error _ => return 1
    let selfPgid ← ProcessEnv.getpgrp
    let selfUid ← match ← getuid with | .ok u => pure u | .error _ => return 1
    let selfOrph ← ProcessEnv.isSelfPgidOrphaned
    if !selfOrph then
      IO.eprintln s!"orphan-tty-cont: expected orphaned selfPgid={selfPgid}"
      return 1
    let wf : WaitFlags := { nohang := true, continued := true }
    for _ in [:8] do
      if let .ok (cPid, cPg) := (← ProcessEnv.spawnStopped (-1) 19) then
        let mut s := (ProcessSysState.initial selfPid selfPgid selfUid).spawnStoppedChild cPid 19 false cPg true [19]
        let o1 : ProcessOutcome := match ← kill cPid.toInt32 .sigcont with | .ok () => .unit | .error e => .err e
        let some s1 := allowedStep s (.kill cPid.toInt32 .sigcont) o1 | do ProcessEnv.cleanupChild cPid; return 2
        let o2 : ProcessOutcome := match ← kill cPid.toInt32 (.raw 20) with | .ok () => .unit | .error e => .err e
        let some s2 := allowedStep s1 (.kill cPid.toInt32 (.raw 20)) o2 | do ProcessEnv.cleanupChild cPid; return 3
        if (← ProcessEnv.setpgid cPid cPid).isOk then
          s := { s2 with procs := s2.procs.map fun (p, e) => if p == cPid then (p, e.setPgid cPid false) else (p, e) }
          IO.sleep 3
          let ow : ProcessOutcome := match ← waitpid cPid.toInt32 wf with | .ok w => .waited w | .error e => .err e
          let okStep := (allowedStep s (.waitpid cPid.toInt32 wf) ow).isSome
          ProcessEnv.cleanupChild cPid
          if !okStep then
            IO.eprintln s!"orphan-tty-cont 1a mismatch: out={repr ow}"
            return 4
        else
          ProcessEnv.cleanupChild cPid
      if let .ok (cPid, cPg) := (← ProcessEnv.spawnControlled (-1) false) then
        let mut s := (ProcessSysState.initial selfPid selfPgid selfUid).spawnRunningChild cPid cPg none false false true
        let o1 : ProcessOutcome := match ← kill cPid.toInt32 (.raw 20) with | .ok () => .unit | .error e => .err e
        let some s1 := allowedStep s (.kill cPid.toInt32 (.raw 20)) o1 | do ProcessEnv.cleanupChild cPid; return 5
        if (← ProcessEnv.setpgid cPid cPid).isOk then
          let sMoved := { s1 with procs := s1.procs.map fun (p, e) => if p == cPid then (p, e.setPgid cPid false) else (p, e) }
          IO.sleep 3
          let o2 : ProcessOutcome := match ← kill cPid.toInt32 .sigcont with | .ok () => .unit | .error e => .err e
          let some s2 := allowedStep sMoved (.kill cPid.toInt32 .sigcont) o2 | do ProcessEnv.cleanupChild cPid; return 6
          let ow : ProcessOutcome := match ← waitpid cPid.toInt32 wf with | .ok w => .waited w | .error e => .err e
          let okStep := (allowedStep s2 (.waitpid cPid.toInt32 wf) ow).isSome
          ProcessEnv.cleanupChild cPid
          if !okStep then
            IO.eprintln s!"orphan-tty-cont 1b mismatch: out={repr ow}"
            return 7
        else
          ProcessEnv.cleanupChild cPid
    match ← ProcessEnv.spawnDelayedZombie (-1) 42 with
    | .error e =>
      IO.eprintln s!"orphan-tty-cont: spawnDelayedZombie failed in NS: {e}"
      return 8
    | .ok (dzPid, (dzPg, dzTid)) =>
      let dzEntry : ProcEntry :=
        { pgid := dzPg, canSignal := true, sameSession := true, orphanedPgid := true,
          role := .child .sigchld false,
          lifecycle := .delayedZombie (.exited 42) false [] .running .none [] .zombieOnly false }
      let sDz0 := ((ProcessSysState.initial selfPid selfPgid selfUid).upsertProc dzPid dzEntry).registerNonLeaderThread dzTid dzPid dzPg
      let oTstp : ProcessOutcome := match ← kill dzPid.toInt32 (.raw 20) with | .ok () => .unit | .error e => .err e
      let some sDz1 := allowedStep sDz0 (.kill dzPid.toInt32 (.raw 20)) oTstp | do ProcessEnv.cleanupChild dzPid; return 9
      let wfU : WaitFlags := { nohang := true, untraced := true }
      let oWait0 : ProcessOutcome := match ← waitpid dzPid.toInt32 wfU with | .ok w => .waited w | .error e => .err e
      let okDz := (oWait0 == .waited .stillRunning) && (allowedStep sDz1 (.waitpid dzPid.toInt32 wfU) oWait0).isSome
      ProcessEnv.cleanupChild dzPid
      if !okDz then
        IO.eprintln s!"orphan-tty-cont delayedZombie mismatch: out={repr oWait0}"
        return 10
    return 0
  | "fuzz-host-spawn" =>
    match ← ProcessEnv.runHostWorker "fuzz-host-inner" arg with
    | .ok rc => return rc
    | .error e =>
      IO.eprintln s!"runHostWorker fuzz-host-inner failed: {e}"
      return 1
  | "fuzz-host-inner" =>
    let parts := arg.splitOn ":"
    match parts with
    | [sStr, stStr] =>
      let seed := (sStr.toNat?.getD 1).toUInt64
      let steps := stStr.toNat?.getD 1000
      let (wq, pt) ← probeKernelFeatures
      runNsFuzzSteps seed false false false wq pt false steps none none false
    | _ =>
      IO.eprintln s!"invalid fuzz-host-inner arg: {arg}"
      return 2
  | "fuzz-ns-spawn" =>
    let parts := arg.splitOn ":"
    let (seed, doSetsid, asPid2, mapUid, dropCapKill, steps, strictSubid) ←
      match parts with
      | [sStr, sidStr, stStr] =>
        pure ((sStr.toNat?.getD 1).toUInt64, sidStr == "1", false, false, false, stStr.toNat?.getD 1000, false)
      | [sStr, sidStr, pid2Str, mapStr, capStr, stStr] =>
        pure ((sStr.toNat?.getD 1).toUInt64, sidStr == "1", pid2Str == "1", mapStr == "1", capStr == "1", stStr.toNat?.getD 1000, false)
      | [sStr, sidStr, pid2Str, mapStr, capStr, stStr, strictStr] =>
        pure ((sStr.toNat?.getD 1).toUInt64, sidStr == "1", pid2Str == "1", mapStr == "1", capStr == "1", stStr.toNat?.getD 1000, strictStr == "1")
      | _ =>
        IO.eprintln s!"invalid fuzz-ns-spawn arg: {arg}"
        return 2
    let nsFlags : UInt32 :=
      (if asPid2 then 2 else 0) |||
      (if mapUid then 4 else 0) |||
      (if strictSubid then 8 else 0)
    let innerArg :=
      s!"{seed}:{if doSetsid then 1 else 0}:{if asPid2 then 1 else 0}:{if mapUid then 1 else 0}:{if dropCapKill then 1 else 0}:{steps}:{if strictSubid then 1 else 0}"
    match ← ProcessEnv.runNsWorker doSetsid nsFlags "fuzz-ns-inner" innerArg with
    | .ok rc => return rc
    | .error e =>
      IO.eprintln s!"runNsWorker failed: {e}"
      return 1
  | "fuzz-ns-inner" =>
    let parts := arg.splitOn ":"
    let (seed, doSetsid, asPid2, mapUid, dropCap, steps, strictSubid) ←
      match parts with
      | [sStr, sidStr, stStr] =>
        pure ((sStr.toNat?.getD 1).toUInt64, sidStr == "1", false, false, false, stStr.toNat?.getD 1000, false)
      | [sStr, sidStr, pid2Str, capStr, stStr] =>
        pure ((sStr.toNat?.getD 1).toUInt64, sidStr == "1", pid2Str == "1", false, capStr == "1", stStr.toNat?.getD 1000, false)
      | [sStr, sidStr, pid2Str, mapStr, capStr, stStr] =>
        pure ((sStr.toNat?.getD 1).toUInt64, sidStr == "1", pid2Str == "1", mapStr == "1", capStr == "1", stStr.toNat?.getD 1000, false)
      | [sStr, sidStr, pid2Str, mapStr, capStr, stStr, strictStr] =>
        pure ((sStr.toNat?.getD 1).toUInt64, sidStr == "1", pid2Str == "1", mapStr == "1", capStr == "1", stStr.toNat?.getD 1000, strictStr == "1")
      | _ =>
        IO.eprintln s!"invalid fuzz-ns-inner arg: {arg}"
        return 2
    match ← setupWorkerEnv true asPid2 mapUid dropCap strictSubid with
    | .error rc => return rc
    | .ok pid1Foreign =>
      let (wq, pt) ← probeKernelFeatures
      runNsFuzzSteps seed true doSetsid asPid2 wq pt false steps none none pid1Foreign none dropCap 0
  | "fuzz-seccomp-host" =>
    match ← ProcessEnv.runHostWorker "fuzz-seccomp-inner" arg with
    | .ok rc => return rc
    | .error e =>
      IO.eprintln s!"runHostWorker fuzz-seccomp-inner failed: {e}"
      return 1
  | "fuzz-seccomp-ns" =>
    let parts := arg.splitOn ":"
    match parts with
    | [_closedStr, sStr, opStr, errStr, stStr] =>
      let innerArg := s!"1:{sStr}:{opStr}:{errStr}:{stStr}:1:0:1:0:0"
      match ← ProcessEnv.runNsWorker true 4 "fuzz-seccomp-inner" innerArg with
      | .ok rc => return rc
      | .error e =>
        IO.eprintln s!"runNsWorker seccomp failed: {e}"
        return 1
    | [_closedStr, sStr, opStr, errStr, stStr, sidStr, pid2Str, mapStr, capStr] =>
      let doSetsid := sidStr == "1"
      let asPid2 := pid2Str == "1"
      let mapUid := mapStr == "1"
      let nsFlags : UInt32 := (if asPid2 then 2 else 0) ||| (if mapUid then 4 else 0)
      let innerArg := s!"1:{sStr}:{opStr}:{errStr}:{stStr}:{sidStr}:{pid2Str}:{mapStr}:{capStr}:0"
      match ← ProcessEnv.runNsWorker doSetsid nsFlags "fuzz-seccomp-inner" innerArg with
      | .ok rc => return rc
      | .error e =>
        IO.eprintln s!"runNsWorker seccomp failed: {e}"
        return 1
    | [_closedStr, sStr, opStr, errStr, stStr, sidStr, pid2Str, mapStr, capStr, strictStr] =>
      let doSetsid := sidStr == "1"
      let asPid2 := pid2Str == "1"
      let mapUid := mapStr == "1"
      let strictSubid := strictStr == "1"
      let nsFlags : UInt32 := (if asPid2 then 2 else 0) ||| (if mapUid then 4 else 0) ||| (if strictSubid then 8 else 0)
      let innerArg := s!"1:{sStr}:{opStr}:{errStr}:{stStr}:{sidStr}:{pid2Str}:{mapStr}:{capStr}:{strictStr}"
      match ← ProcessEnv.runNsWorker doSetsid nsFlags "fuzz-seccomp-inner" innerArg with
      | .ok rc => return rc
      | .error e =>
        IO.eprintln s!"runNsWorker seccomp failed: {e}"
        return 1
    | _ =>
      IO.eprintln s!"invalid fuzz-seccomp-ns arg: {arg}"
      return 2
  | "fuzz-seccomp-inner" =>
    let parts := arg.splitOn ":"
    let (closedNs, seed, opKind, errNum, steps, doSetsid, asPid2, mapUid, dropCap, strictSubid) ←
      match parts with
      | [closedStr, sStr, opStr, errStr, stStr] =>
        pure (closedStr == "1", (sStr.toNat?.getD 1).toUInt64, UInt8.ofNat (opStr.toNat?.getD 3),
              UInt32.ofNat (errStr.toNat?.getD 1), stStr.toNat?.getD 60, true, false, true, false, false)
      | [closedStr, sStr, opStr, errStr, stStr, sidStr, pid2Str, mapStr, capStr] =>
        pure (closedStr == "1", (sStr.toNat?.getD 1).toUInt64, UInt8.ofNat (opStr.toNat?.getD 3),
              UInt32.ofNat (errStr.toNat?.getD 1), stStr.toNat?.getD 60, sidStr == "1", pid2Str == "1", mapStr == "1", capStr == "1", false)
      | [closedStr, sStr, opStr, errStr, stStr, sidStr, pid2Str, mapStr, capStr, strictStr] =>
        pure (closedStr == "1", (sStr.toNat?.getD 1).toUInt64, UInt8.ofNat (opStr.toNat?.getD 3),
              UInt32.ofNat (errStr.toNat?.getD 1), stStr.toNat?.getD 60, sidStr == "1", pid2Str == "1", mapStr == "1", capStr == "1", strictStr == "1")
      | _ =>
        IO.eprintln s!"invalid fuzz-seccomp-inner arg: {arg}"
        return 2
    match ← setupWorkerEnv closedNs asPid2 mapUid dropCap strictSubid with
    | .error rc => return rc
    | .ok pid1Foreign =>
      let initSelfPid ←
        match ← getpid with
        | .ok p => pure p
        | .error e =>
          IO.eprintln s!"fuzz-seccomp-inner: initial getpid failed {e}"
          return 1
      let initSelfUid ←
        match ← getuid with
        | .ok u => pure u
        | .error e =>
          IO.eprintln s!"fuzz-seccomp-inner: initial getuid failed {e}"
          return 1
      let (wq, pt) ← probeKernelFeatures
      match ← ProcessEnv.installSeccompErrno opKind errNum with
      | .error e =>
        IO.eprintln s!"installSeccompErrno failed: {e}"
        return 1
      | .ok () =>
        runNsFuzzSteps seed closedNs doSetsid asPid2 wq pt true steps (some initSelfPid) (some initSelfUid) pid1Foreign (some opKind) dropCap errNum
  | "fuzz-replay-host" =>
    match ← ProcessEnv.runHostWorker "fuzz-replay-inner" arg with
    | .ok rc => return rc
    | .error e =>
      IO.eprintln s!"runHostWorker fuzz-replay-inner failed: {e}"
      return 1
  | "fuzz-replay-spawn" =>
    match arg.splitOn ":" with
    | _closedStr :: _sStr :: _mStr :: sidStr :: pid2Str :: mapStr :: _capStr :: _secStr :: _opStr :: _errStr :: strictStr :: _ =>
      let doSetsid := sidStr == "1"
      let asPid2 := pid2Str == "1"
      let mapUid := mapStr == "1"
      let strictSubid := strictStr == "1"
      let nsFlags : UInt32 := (if asPid2 then 2 else 0) ||| (if mapUid then 4 else 0) ||| (if strictSubid then 8 else 0)
      match ← ProcessEnv.runNsWorker doSetsid nsFlags "fuzz-replay-inner" arg with
      | .ok rc => return rc
      | .error e =>
        IO.eprintln s!"runNsWorker replay failed: {e}"
        return 1
    | _ =>
      IO.eprintln s!"invalid fuzz-replay-spawn arg: {arg}"
      return 2
  | "fuzz-replay-inner" =>
    let parsed? : Option (Bool × UInt64 × Nat × Bool × Bool × Bool × Bool × Bool × UInt8 × UInt32 × Bool × Bool × Bool × Bool × Bool × String) :=
      match arg.splitOn ":" with
      | [closedStr, sStr, maxStr, sidStr, pid2Str, mapStr, capStr, secStr, opStr, errStr, strictStr, printTag, csv] =>
        some (closedStr == "1", (sStr.toNat?.getD 1).toUInt64, maxStr.toNat?.getD 60,
              sidStr == "1", pid2Str == "1", mapStr == "1", capStr == "1", secStr == "1",
              UInt8.ofNat (opStr.toNat?.getD 0), UInt32.ofNat (errStr.toNat?.getD 1),
              strictStr == "1", false, false, false, printTag == "P", csv)
      | [closedStr, sStr, maxStr, sidStr, pid2Str, mapStr, capStr, secStr, opStr, errStr, strictStr, remapStr, ignStr, blkStr, printTag, csv] =>
        some (closedStr == "1", (sStr.toNat?.getD 1).toUInt64, maxStr.toNat?.getD 60,
              sidStr == "1", pid2Str == "1", mapStr == "1", capStr == "1", secStr == "1",
              UInt8.ofNat (opStr.toNat?.getD 0), UInt32.ofNat (errStr.toNat?.getD 1),
              strictStr == "1", remapStr == "1", ignStr == "1", blkStr == "1", printTag == "P", csv)
      | _ => none
    match parsed? with
    | some (closedNs, epSeed, maxActs, doSetsid, asPid2, mapUid, dropCap, useSec, opKind, errNum, strictSubid, remapSlots, dropIgn, dropBlk, printEp, csv) =>
      match ← setupWorkerEnv closedNs asPid2 mapUid dropCap strictSubid with
      | .error rc => return rc
      | .ok pid1Foreign =>
        let initSelfPid? ←
          if useSec then
            match ← getpid with | .ok p => pure (some p) | .error _ => pure none
          else pure none
        let initSelfUid? ←
          if useSec then
            match ← getuid with | .ok u => pure (some u) | .error _ => pure none
          else pure none
        let (wq, pt) ← probeKernelFeatures
        if useSec then
          match ← ProcessEnv.installSeccompErrno opKind errNum with
          | .error e =>
            IO.eprintln s!"fuzz-replay-inner installSeccompErrno failed: {e}"
            return 1
          | .ok () => pure ()
        let (ep, _) := generateEpisode (Rng.seed epSeed) closedNs doSetsid asPid2 wq pt maxActs useSec pid1Foreign initSelfPid? initSelfUid? (if useSec then some opKind else none) dropCap errNum
        let rawIdxs := parseReplayIndices csv
        let kept :=
          if remapSlots then remapEpisodeActions closedNs asPid2 ep.actions rawIdxs
          else rawIdxs.filterMap fun idx => ep.actions[idx]?
        let subEp :=
          { ep with
            ambientSigIgn := if dropIgn then #[] else ep.ambientSigIgn
            ambientSigBlocked := if dropBlk then #[] else ep.ambientSigBlocked
            actions := kept }
        match ← runEpisode subEp with
        | .ok _ => return 0
        | .error (msg, _) =>
          if printEp then
            IO.eprintln s!"MINIMAL_EPISODE: {repr subEp}"
          else
            IO.eprintln msg
          return 42
    | none =>
      IO.eprintln s!"invalid fuzz-replay-inner arg: {arg}"
      return 2
  | _ =>
    IO.eprintln s!"unknown --ns-worker mode: {mode}"
    return 2

private def hitCount (hits : HitMap) (sys bkt : String) : Nat :=
  match hits.find? fun ((s, b), _) => s == sys && b == bkt with
  | some (_, c) => c
  | none => 0

private def sumErrorHits (hits : HitMap) (sys : String) : Nat :=
  hits.foldl (fun acc ((s, b), c) => if s == sys && !b.startsWith "ok" then acc + c else acc) 0

private def verifyCoverageFloor (nonSecHits secHits : HitMap) (totalSteps : Nat) (pid1ForeignRan requireNs : Bool) : Except String Unit := do
  if totalSteps < 10000 then
    return ()
  let reqExact : Array (String × String) := #[
    ("pipe2", "ok"), ("pipe2", "EINVAL"), ("pipe2", "EMFILE"),
    ("waitpid", "ok:stillRunning"), ("waitpid", "ok:exited"), ("waitpid", "ok:signaled"),
    ("waitpid", "ok:stopped"), ("waitpid", "ok:continued"), ("waitpid", "EINVAL"), ("waitpid", "ECHILD"),
    ("kill", "ok"), ("kill", "EINVAL"), ("kill", "ESRCH"),
    ("pidfd_open", "ok"), ("pidfd_open", "EINVAL"), ("pidfd_open", "ENOENT"), ("pidfd_open", "ESRCH"),
    ("pidfd_send_signal", "ok"), ("pidfd_send_signal", "EINVAL"),
    ("pidfd_send_signal", "EBADF"), ("pidfd_send_signal", "ESRCH"),
    ("getpid", "ok"), ("getuid", "ok"),
    ("mode_wclone", "ok"), ("mode_wall", "ok"),
    ("mode_wnothread", "ECHILD"), ("mode_autoreap", "ECHILD"), ("mode_subreaper", "ok"),
    ("mode_delayed_zombie_exited", "ok")
  ]
  for (sys, bkt) in reqExact do
    if hitCount nonSecHits sys bkt == 0 then
      throw s!"COVERAGE_FLOOR_FAILED: missing required non-seccomp bucket ({sys}, {bkt}) across {totalSteps} steps"
  for sys in #["pipe2", "waitpid", "kill", "pidfd_open", "pidfd_send_signal", "getpid", "getuid"] do
    if sumErrorHits secHits sys == 0 then
      throw s!"COVERAGE_FLOOR_FAILED: missing seccomp error hits on {sys} across {totalSteps} steps"
  if pid1ForeignRan || requireNs then
    if hitCount nonSecHits "kill" "EPERM" == 0 then
      throw s!"COVERAGE_FLOOR_FAILED: missing non-seccomp (kill, EPERM) with pid1Foreign/requireNs across {totalSteps} steps"
    if hitCount nonSecHits "pidfd_send_signal" "EPERM" == 0 then
      throw s!"COVERAGE_FLOOR_FAILED: missing non-seccomp (pidfd_send_signal, EPERM) with pid1Foreign/requireNs across {totalSteps} steps"
  pure ()

private def printHitSummary (hits : HitMap) (totalSyscalls : Nat) : IO Unit := do
  IO.println s!"PROCESS_FUZZ_SUMMARY: total_syscalls={totalSyscalls} unique_buckets={hits.length}"
  let sorted := hits.toArray.qsort fun a b =>
    if a.1.1 != b.1.1 then a.1.1 < b.1.1 else a.1.2 < b.1.2
  for ((sys, bkt), cnt) in sorted do
    IO.println s!"  HIT {sys} {bkt}: {cnt}"

private def runShimEdgeSmoke : IO (Except String Unit) := do
  let _ ← ProcessEnv.setSigchldAutoreap 0
  for secErr in #[(1 : UInt32), 4, 5, 7, 9, 12, 28, 104, 116, 122, 4095] do
    match ← ProcessEnv.checkFdCloseSeccomp secErr with
    | .ok true => pure ()
    | other => return .error s!"MISMATCH close_fd cls=seccomp_detach err={secErr} got={repr other}"
  for badPipeBits in #[(1 : UInt32), 0x80000000] do
    match ← pipe2 { extraBits := badPipeBits } with
    | .error e => if e != Errno.EINVAL then return .error s!"MISMATCH pipe2 cls=extra_bits got={e}"
    | .ok (r, w) => let _ ← ProcessEnv.closeFd r; let _ ← ProcessEnv.closeFd w; return .error "MISMATCH pipe2 cls=extra_bits got=ok"
  if !(← ProcessEnv.probeKernelWatchQueue) then
    match ← pipe2 { notificationPipe := true } with
    | .error e => if e != errnoENOPKG then return .error s!"MISMATCH pipe2 cls=notif_enopkg got={e}"
    | .ok (r, w) => let _ ← ProcessEnv.closeFd r; let _ ← ProcessEnv.closeFd w; return .error "MISMATCH pipe2 cls=notif_enopkg got=ok"
  for badWaitBits in #[(1 : UInt32), 0x04000000, 0x80000000] do
    match ← waitpid (-1) { extraBits := badWaitBits } with
    | .error e => if e != Errno.EINVAL then return .error s!"MISMATCH waitpid cls=extra_bits_high got={e}"
    | .ok wr => return .error s!"MISMATCH waitpid cls=extra_bits_high got={repr wr}"
  let selfP := (← getpid).toOption.getD 1
  for badOpen in #[((0x80000000 : UInt32), ({} : PidfdOpenFlags)), (selfP, { extraBits := 1 }), (selfP, { extraBits := 0x80000000 })] do
    match ← pidfd_open badOpen.1 badOpen.2 with
    | .error e => if e != Errno.EINVAL then return .error s!"MISMATCH pidfd_open cls=invalid_high got={e}"
    | .ok fd => let _ ← ProcessEnv.closeFd fd; return .error "MISMATCH pidfd_open cls=invalid_high got=ok"
  if ← ProcessEnv.probeUnshare then
    let exe ← resolveSelfExe
    let outNeg1 ← IO.Process.output {
      cmd := exe
      args := #["--suite", "process", "--ns-worker", "kill-neg1-foreign-spawn", "0"]
    }
    if outNeg1.exitCode != 0 then
      return .error s!"MISMATCH kill cls=neg1_foreign rc={outNeg1.exitCode} err={outNeg1.stderr.trimAscii}"
  match ← ProcessEnv.spawnSigPendingProbe with
  | .error _ => pure ()
  | .ok (cZero, probeSock) =>
    let pndMask ←
      try
        let _ ← kill cZero.toInt32 .sigzero
        if let .ok czPfd := (← pidfd_open cZero {}) then
          let sendOk ← pidfd_send_signal czPfd .sigzero {}
          for badSigBits in #[(1 : UInt32), 0x80000000] do
            match ← pidfd_send_signal czPfd .sigzero { extraBits := badSigBits } with
            | .error e =>
              if e != Errno.EINVAL then
                let _ ← ProcessEnv.closeFd czPfd
                let _ ← ProcessEnv.finishSigPendingProbe cZero probeSock
                return .error s!"MISMATCH pidfd_send_signal cls=extra_bits_high got={e}"
            | .ok () =>
              let _ ← ProcessEnv.closeFd czPfd
              let _ ← ProcessEnv.finishSigPendingProbe cZero probeSock
              return .error "MISMATCH pidfd_send_signal cls=extra_bits_high got=ok"
          let closeRes ← ProcessEnv.closeFd czPfd
          if sendOk.isOk && !closeRes.isOk then
            let _ ← ProcessEnv.finishSigPendingProbe cZero probeSock
            return .error s!"MISMATCH closeFd cls=EBUSY after pidfd_send_signal got={repr closeRes}"
        ProcessEnv.finishSigPendingProbe cZero probeSock
      finally
        let _ ← ProcessEnv.closeFd probeSock
        ProcessEnv.cleanupChild cZero
    if pndMask != 0 then
      return .error s!"MISMATCH kill cls=sigzero_queued mask={pndMask}"
  let selfPid := (← getpid).toOption.getD 1000
  let selfPgid ← ProcessEnv.getpgrp
  let selfUid := (← getuid).toOption.getD 1000
  if let .ok (cDzEx, (dzExPg, dzExTid)) := (← ProcessEnv.spawnDelayedZombie (-1) 23 8000 37) then
    let dzExErr ←
      try
        let dzExEntry : ProcEntry :=
          { pgid := dzExPg, canSignal := true, sameSession := true, role := .child .sigchld false,
            lifecycle := .delayedZombie (.exited 23) false [] .running .none [] .zombieOnly false }
        let wExEntry : ProcEntry :=
          { pgid := dzExPg, canSignal := true, sameSession := true, role := .thread cDzEx,
            lifecycle := .alive { auto := .planned (.exited 37) } }
        let sEx0 := ((ProcessSysState.initial selfPid selfPgid selfUid).upsertProc cDzEx dzExEntry).upsertProc dzExTid wExEntry
        match ← waitpid cDzEx.toInt32 {} with
        | .error e => pure (some s!"MISMATCH waitpid cls={Errno.name e} autonomous delayedZombie waitpid failed")
        | .ok wEx =>
          if wEx != WaitResult.exited cDzEx 37 then
            pure (some s!"MISMATCH waitpid cls=ok:exited autonomous delayedZombie got {repr wEx}")
          else if (allowedStep sEx0 (.waitpid cDzEx.toInt32 {}) (.waited wEx)).isNone then
            pure (some "MISMATCH waitpid cls=ok:exited model rejected autonomous delayedZombie exited")
          else
            pure none
      finally
        ProcessEnv.cleanupChild cDzEx
    if let some msg := dzExErr then return .error msg
  if ← ProcessEnv.probeKernelPidfdThread then
    if let .ok (cDz, (dzPg, dzTid)) := (← ProcessEnv.spawnDelayedZombie (-1) 9) then
      let dzErr ←
        try
          let dzEntry : ProcEntry :=
            { pgid := dzPg, canSignal := true, sameSession := true, role := .child .sigchld false,
              lifecycle := .delayedZombie (.exited 9) false [] .running .none [] .zombieOnly false }
          let s0 := (((ProcessSysState.initial selfPid selfPgid selfUid).withPidfdThreadSupported true).upsertProc cDz dzEntry).registerNonLeaderThread dzTid cDz dzPg
          match ← pidfd_open cDz { thread := true } with
          | .error e => pure (some s!"MISMATCH pidfd_open cls={Errno.name e} delayedZombie PIDFD_THREAD failed")
          | .ok dzPfd =>
            try
              let some s1 := allowedStep s0 (.pidfd_open cDz { thread := true }) (.opened 0)
                | pure (some "MISMATCH pidfd_open cls=ok model rejected delayedZombie PIDFD_THREAD")
              match ← pidfd_send_signal dzPfd .sigterm {} with
              | .error e => pure (some s!"MISMATCH pidfd_send_signal cls={Errno.name e} default PIDFD_THREAD sigterm failed")
              | .ok () =>
                let some s2 := allowedStep s1 (.pidfd_send_signal 0 .sigterm {}) .unit
                  | pure (some "MISMATCH pidfd_send_signal cls=ok model rejected default PIDFD_THREAD")
                IO.sleep 5
                match ← waitpid cDz.toInt32 { nohang := true } with
                | .error e => pure (some s!"MISMATCH waitpid cls={Errno.name e} expected stillRunning after thread sigterm")
                | .ok w1 =>
                  if w1 != WaitResult.stillRunning then
                    pure (some s!"MISMATCH waitpid cls=stillRunning expected stillRunning after thread sigterm, got {repr w1}")
                  else
                    match ← pidfd_send_signal dzPfd .sigterm { threadGroup := true } with
                    | .error e => pure (some s!"MISMATCH pidfd_send_signal cls={Errno.name e} THREAD_GROUP override failed")
                    | .ok () =>
                      let some s3 := allowedStep s2 (.pidfd_send_signal 0 .sigterm { threadGroup := true }) .unit
                        | pure (some "MISMATCH pidfd_send_signal cls=ok model rejected THREAD_GROUP override")
                      let mut ready := false
                      for _ in [:100] do
                        let (zst, _) ← ProcessEnv.probeZombie cDz
                        if zst != 0 then ready := true; break
                        IO.sleep 2
                      if !ready then
                        pure (some "MISMATCH pidfd_send_signal cls=thread_group_dropped delayedZombie remained alive after PIDFD_SIGNAL_THREAD_GROUP")
                      else
                        match ← waitpid cDz.toInt32 {} with
                        | .error e => pure (some s!"MISMATCH waitpid cls={Errno.name e} blocking waitpid on delayedZombie failed")
                        | .ok w2 =>
                          if w2 != WaitResult.signaled cDz 15 false then
                            pure (some s!"MISMATCH waitpid cls=ok:signaled unexpected {repr w2}")
                          else if (allowedStep s3 (.waitpid cDz.toInt32 {}) (.waited w2)).isNone then
                            pure (some s!"MISMATCH waitpid cls=ok:signaled model rejected blocking waitpid on delayedZombie")
                          else
                            pure none
            finally
              let _ ← ProcessEnv.closeFd dzPfd
        finally
          ProcessEnv.cleanupChild cDz
      if let some msg := dzErr then return .error msg
  return .ok ()

/-- Run `totalSteps` real Linux process syscalls against the `ProcessSysState` relational oracle across isolated `CLONE_NEWPID` namespaces (`doSetsid = true/false`, `asPid2 = true/false`, `mapUid`, `dropCapKill`), multi-errno `seccomp` (`0..7`), and open-host episodes. Passing `requireNs := true` (`--require-ns`) requires unprivileged user/PID namespaces, the `uidmap` helpers (`/usr/bin/newuidmap`, `/usr/bin/newgidmap`), and `/etc/subuid` + `/etc/subgid` ranges for the running user. -/
def runFuzz (totalSteps : Nat) (seed : UInt64) (selfTestShrink : Bool) (requireNs : Bool := false) : IO UInt32 := do
  if selfTestShrink then
    runShrinkSelfTest
  if let .error smokeMsg := (← runShimEdgeSmoke) then
    IO.eprintln smokeMsg
    return 1
  let canNs ← ProcessEnv.probeUnshare
  if requireNs && !canNs then
    IO.eprintln "REQUIRE_NS_FAILED: unprivileged CLONE_NEWUSER | CLONE_NEWPID is unavailable"
    return 1
  if requireNs then
    let exeStrict ← resolveSelfExe
    let outStrict ← IO.Process.output {
      cmd := exeStrict
      args := #["--suite", "process", "--ns-worker", "kill-neg1-foreign-spawn", "strict"]
    }
    if outStrict.exitCode != 0 then
      IO.eprintln s!"REQUIRE_NS_FAILED: kill-neg1-foreign strict check failed (rc={outStrict.exitCode}): {outStrict.stderr.trimAscii}"
      return 1
  let subidEnv ←
    match ← buildWorkerSubidEnv requireNs with
    | .ok e => pure e
    | .error msg =>
      IO.eprintln msg
      return 1
  let mut r := Rng.seed seed
  let mut doneSteps : Nat := 0
  let mut nonSecHits : HitMap := []
  let mut secHits : HitMap := []
  let mut pid1ForeignRan := false
  let seccompTarget := min 24000 (max 640 (totalSteps / 16))
  let secOps : Array UInt8 := #[0, 1, 2, 3, 4, 5, 6, 7]
  let sweepCount := max secOps.size (min 40 (seccompTarget / 150))
  let perSweep := max 80 (seccompTarget / sweepCount)
  for i in [:sweepCount] do
    if doneSteps < totalSteps then
      let opKind := secOps.getD (i % secOps.size) 3
      let mut sweepDone : Nat := 0
      let mut tries : Nat := 0
      while sweepDone < perSweep && doneSteps < totalSteps && tries < 24 do
        tries := tries + 1
        let (wSeed, r1) := r.nextU64
        let (errNum, r2) := pickSeccompErrno r1
        let (doSetsid, r3) := r2.chance 1 2
        let (asPid2, r4) := r3.chance 1 2
        let (mapUid, r5) := r4.chance 1 2
        let (dropCapKill, r6) := r5.chance 1 2
        r := r6
        let useNs := canNs && ((i + tries) % 4 != 3)
        let remSweep := min (perSweep - sweepDone) (totalSteps - doneSteps)
        let batch := max 1 remSweep
        match ← runSeccompFuzzWithCapture subidEnv useNs doSetsid asPid2 mapUid dropCapKill requireNs wSeed opKind errNum batch with
        | .ok (actualSteps, sHits, foreignUid) =>
          if foreignUid then pid1ForeignRan := true
          doneSteps := doneSteps + actualSteps
          sweepDone := sweepDone + actualSteps
          secHits := mergeHitMaps secHits sHits
        | .error errMsg =>
          IO.eprintln errMsg
          return 1
  if canNs then
    let nsTarget := (totalSteps * 88) / 100
    let batchSize := max 500 (min 20000 (nsTarget / 24))
    let mut cfgIdx : Nat := 0
    while doneSteps < nsTarget do
      let batch := min batchSize (nsTarget - doneSteps)
      let (wSeed, r') := r.nextU64
      r := r'
      let doSetsid := cfgIdx % 2 == 0
      let asPid2 := (cfgIdx / 2) % 2 == 1
      let mapUid := (cfgIdx / 4) % 2 == 1
      let dropCapKill := (cfgIdx / 8) % 2 == 1
      cfgIdx := cfgIdx + 1
      match ← runNsFuzzWithCapture subidEnv doSetsid asPid2 mapUid dropCapKill requireNs wSeed batch with
      | .ok (actualSteps, nsHits, foreignUid) =>
        if foreignUid then pid1ForeignRan := true
        doneSteps := doneSteps + actualSteps
        nonSecHits := mergeHitMaps nonSecHits nsHits
      | .error errMsg =>
        IO.eprintln errMsg
        return 1
  while doneSteps < totalSteps do
    let remHost := min 20000 (totalSteps - doneSteps)
    let (hSeed, r') := r.nextU64
    r := r'
    match ← runHostFuzzWithCapture subidEnv hSeed remHost with
    | .ok (actualSteps, hostHits, _) =>
      doneSteps := doneSteps + actualSteps
      nonSecHits := mergeHitMaps nonSecHits hostHits
    | .error errMsg =>
      IO.eprintln errMsg
      return 1
  let allHits := mergeHitMaps nonSecHits secHits
  printHitSummary allHits doneSteps
  match verifyCoverageFloor nonSecHits secHits doneSteps pid1ForeignRan requireNs with
  | .ok () => return 0
  | .error covMsg =>
    IO.eprintln covMsg
    return 1

end Fuzz.LinuxSyscall.ProcessFuzz
