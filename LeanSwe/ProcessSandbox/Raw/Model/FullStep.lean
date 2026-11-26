import LeanSwe.ProcessSandbox.Raw.Model.FullWorld

namespace LeanSwe.ProcessSandbox.Raw.Model

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw

/-- Process syscall request over `RawFd` covering all 7 `LinuxSyscall.Process` operations. -/
inductive RawFdProcReq where
  /-- `proc.pipe2`. -/
  | pipe2 (flags : LinuxSyscall.Process.PipeFlags)
  /-- `proc.waitpid`. -/
  | waitpid (pid : Int32) (flags : LinuxSyscall.Process.WaitFlags)
  /-- `proc.kill`. -/
  | kill (target : Int32) (sig : LinuxSyscall.Process.Signal)
  /-- `proc.pidfd_open`. -/
  | pidfdOpen (pid : UInt32) (flags : LinuxSyscall.Process.PidfdOpenFlags)
  /-- `proc.pidfd_send_signal`. -/
  | pidfdSendSignal (pidfd : RawFd) (sig : LinuxSyscall.Process.Signal) (flags : LinuxSyscall.Process.PidfdSignalFlags)
  /-- `proc.getpid`. -/
  | getpid
  /-- `proc.getuid`. -/
  | getuid

/-- Map a `RawFdProcReq` into `LinuxSyscall.Process.ProcessReq` under `toHid : RawFd → Nat`. -/
def mapRawFdProcReq (toHid : RawFd → Nat) : RawFdProcReq → LinuxSyscall.Process.ProcessReq
  | .pipe2 fl => .pipe2 fl
  | .waitpid pid fl => .waitpid pid fl
  | .kill tgt sig => .kill tgt sig
  | .pidfdOpen pid fl => .pidfd_open pid fl
  | .pidfdSendSignal fd sig fl => .pidfd_send_signal (toHid fd) sig fl
  | .getpid => .getpid
  | .getuid => .getuid

/-- Process syscall outcome over `RawFd` paired with `RawFdProcReq`. -/
inductive RawFdProcOut where
  /-- `pipe2` succeeded. -/
  | piped (rFd wFd : RawFd)
  /-- `pidfd_open` succeeded. -/
  | opened (fd : RawFd)
  /-- `waitpid` succeeded. -/
  | waited (res : LinuxSyscall.Process.WaitResult)
  /-- `kill` or `pidfd_send_signal` succeeded. -/
  | unit
  /-- `getpid` or `getuid` succeeded. -/
  | u32 (val : UInt32)
  /-- Process syscall failed with Linux `Errno`. -/
  | err (code : Errno)

/-- Relate a `RawFdProcOut` to a model `LinuxSyscall.Process.ProcessOutcome`. -/
def RawFdProcOut.MatchesModel : RawFdProcOut → LinuxSyscall.Process.ProcessOutcome → Prop
  | .piped _ _, .piped _ _ => True
  | .opened _, .opened _ => True
  | .waited wr, .waited wr' => wr = wr'
  | .unit, .unit => True
  | .u32 v, .u32 v' => v = v'
  | .err e, .err e' => e = e'
  | _, _ => False

/-- Execute one `RawFdProcReq` against `proc : LinuxSyscall.Process.ProcessOpsM (StateM W) RawFd`. -/
def execRawFdProcReq {W : Type} (proc : LinuxSyscall.Process.ProcessOpsM (StateM W) RawFd) :
    RawFdProcReq → StateM W RawFdProcOut
  | .pipe2 fl => (fun | .ok (r, w) => .piped r w | .error e => .err e) <$> proc.pipe2 fl
  | .waitpid pid fl => (fun | .ok wr => .waited wr | .error e => .err e) <$> proc.waitpid pid fl
  | .kill tgt sig => (fun | .ok () => .unit | .error e => .err e) <$> proc.kill tgt sig
  | .pidfdOpen pid fl => (fun | .ok d => .opened d | .error e => .err e) <$> proc.pidfd_open pid fl
  | .pidfdSendSignal d sig fl => (fun | .ok () => .unit | .error e => .err e) <$> proc.pidfd_send_signal d sig fl
  | .getpid => (fun | .ok v => .u32 v | .error e => .err e) <$> proc.getpid
  | .getuid => (fun | .ok v => .u32 v | .error e => .err e) <$> proc.getuid

/-- Sandbox syscall request over `RawFd` covering the 3 `LinuxSyscall.Sandbox` operations consumed by `ProcessSandbox.Raw`. -/
inductive RawFdSandboxReq where
  /-- `sandbox.landlockCreateRuleset`. -/
  | landlockCreateRuleset (attr? : Option Sandbox.LandlockRulesetAttr) (flags : UInt32)
  /-- `sandbox.seccomp`. -/
  | seccomp (op : Sandbox.SeccompOp) (flags : Sandbox.SeccompFlags) (filterBytes : ByteArray)
  /-- `sandbox.memfdCreate`. -/
  | memfdCreate (name : ByteArray) (flags : Sandbox.MemfdFlags)

/-- Map a `RawFdSandboxReq` into `Sandbox.SandboxReq`. -/
def mapRawFdSandboxReq : RawFdSandboxReq → Sandbox.SandboxReq
  | .landlockCreateRuleset a fl => .landlockCreateRuleset a fl
  | .seccomp op fl bs => .seccomp op fl bs
  | .memfdCreate nm fl => .memfdCreate nm fl

/-- Sandbox syscall outcome over `RawFd` paired with `RawFdSandboxReq`. -/
inductive RawFdSandboxOut where
  /-- `landlockCreateRuleset(none, flags)` returned ABI version `val`. -/
  | landlockVersion (val : UInt32)
  /-- `landlockCreateRuleset(some attr, 0)` or `memfdCreate` allocated `fd`. -/
  | opened (fd : RawFd)
  /-- `seccomp` succeeded returning `val`. -/
  | u32 (val : UInt32)
  /-- Sandbox syscall failed with Linux `Errno`. -/
  | err (code : Errno)

/-- Relate a `RawFdSandboxOut` to a model `LinuxSyscall.Sandbox.SandboxOutcome`. -/
def RawFdSandboxOut.MatchesModel : RawFdSandboxOut → LinuxSyscall.Sandbox.SandboxOutcome → Prop
  | .landlockVersion v, .landlockVersion v' => v = v'
  | .opened _, .opened _ => True
  | .u32 v, .u32 v' => v = v'
  | .err e, .err e' => e = e'
  | _, _ => False

/-- Execute one `RawFdSandboxReq` against `sb : Sandbox.SandboxOpsM (StateM W) RawFd`. -/
def execRawFdSandboxReq {W : Type} (sb : Sandbox.SandboxOpsM (StateM W) RawFd) :
    RawFdSandboxReq → StateM W RawFdSandboxOut
  | .landlockCreateRuleset a fl =>
    (fun
      | .ok (.version v) => .landlockVersion v
      | .ok (.ruleset d) => .opened d
      | .error e => .err e) <$> sb.landlockCreateRuleset a fl
  | .seccomp op fl bs => (fun | .ok v => .u32 v | .error e => .err e) <$> sb.seccomp op fl bs
  | .memfdCreate nm fl => (fun | .ok d => .opened d | .error e => .err e) <$> sb.memfdCreate nm fl

/-- Map `toHid : RawFd → Nat` across a `PostFork.FdRef RawFd`. -/
def mapPostForkFdRef (toHid : RawFd → Nat) : PostFork.FdRef RawFd → PostFork.FdRef Nat
  | .handle h => .handle (toHid h)
  | .raw n => .raw n

/-- Map `toHid : RawFd → Nat` across a `PostFork.ArgToken RawFd`. -/
def mapPostForkArgToken (toHid : RawFd → Nat) : PostFork.ArgToken RawFd → PostFork.ArgToken Nat
  | .lit s => .lit s
  | .fdDecimal r => .fdDecimal (mapPostForkFdRef toHid r)
  | .prefixedFd pre r suf => .prefixedFd pre (mapPostForkFdRef toHid r) suf

/-- Map `toHid : RawFd → Nat` across a `PostFork.StdioPlan RawFd`. -/
def mapPostForkStdio (toHid : RawFd → Nat) : PostFork.StdioPlan RawFd → PostFork.StdioPlan Nat
  | .inherit => .inherit
  | .redirect i o e cl =>
    .redirect (mapPostForkFdRef toHid i) (mapPostForkFdRef toHid o) (mapPostForkFdRef toHid e) cl

/-- Map `toHid : RawFd → Nat` across a `PostFork.FdPolicy RawFd`. -/
def mapPostForkPolicy (toHid : RawFd → Nat) : PostFork.FdPolicy RawFd → PostFork.FdPolicy Nat
  | .inheritNonCloexec ks => .inheritNonCloexec (ks.map (mapPostForkFdRef toHid))
  | .closeAllAbove2Except ks => .closeAllAbove2Except (ks.map (mapPostForkFdRef toHid))

/-- Map `toHid : RawFd → Nat` across a `PostFork.ChildSpecM RawFd`. -/
def mapPostForkChildSpec (toHid : RawFd → Nat) (s : PostFork.ChildSpecM RawFd) :
    PostFork.ChildSpecM Nat :=
  { path := s.path
    argv := s.argv.map (mapPostForkArgToken toHid)
    cwd := s.cwd
    env := s.env
    rawEnv := s.rawEnv
    stdio := mapPostForkStdio toHid s.stdio
    fdPolicy := mapPostForkPolicy toHid s.fdPolicy
    closeFds := s.closeFds.map (mapPostForkFdRef toHid)
    processGroup := s.processGroup
    sigpipe := s.sigpipe
    forkMode := s.forkMode }

/-- Map `toHid : RawFd → Nat` across a `PostFork.PendingChildM RawFd`. -/
def mapPostForkPending (toHid : RawFd → Nat) (p : PostFork.PendingChildM RawFd) :
    PostFork.PendingChildM Nat :=
  { pid := p.pid, pgid := p.pgid, syncWrite := toHid p.syncWrite, errRead := toHid p.errRead }

/-- `PostFork` request over `RawFd` covering all 4 `PostForkOpsM` operations. -/
inductive RawFdPostForkReq where
  /-- `postFork.spawn`. -/
  | spawn (spec : PostFork.ChildSpecM RawFd)
  /-- `postFork.spawnWithBarrier`. -/
  | spawnWithBarrier (spec : PostFork.ChildSpecM RawFd)
  /-- `postFork.releaseBarrier`. -/
  | releaseBarrier (pending : PostFork.PendingChildM RawFd)
  /-- `postFork.abortBarrier`. -/
  | abortBarrier (pending : PostFork.PendingChildM RawFd)

/-- Map a `RawFdPostForkReq` into `PostFork.Model.PkgStepReq` under `toHid : RawFd → Nat`. -/
def mapRawFdPostForkReq (toHid : RawFd → Nat) : RawFdPostForkReq → PostFork.Model.PkgStepReq
  | .spawn sp => .spawn (mapPostForkChildSpec toHid sp)
  | .spawnWithBarrier sp => .spawnWithBarrier (mapPostForkChildSpec toHid sp)
  | .releaseBarrier p => .releaseBarrier (mapPostForkPending toHid p)
  | .abortBarrier p => .abortBarrier (mapPostForkPending toHid p)

/-- `PostFork` outcome over `RawFd` paired with `RawFdPostForkReq`. -/
inductive RawFdPostForkOut where
  /-- `spawn` or `releaseBarrier` outcome. -/
  | spawned (res : Except PostFork.PostForkError PostFork.SpawnedChild)
  /-- `spawnWithBarrier` outcome. -/
  | pending (res : Except PostFork.PostForkError (PostFork.PendingChildM RawFd))
  /-- `abortBarrier` outcome. -/
  | aborted (res : Except PostFork.PostForkError PostFork.AbortOutcome)

/-- Relate a `RawFdPostForkOut` to a model `PostFork.Model.PkgStepOut`. -/
def RawFdPostForkOut.MatchesModel : RawFdPostForkOut → PostFork.Model.PkgStepOut → Prop
  | .spawned r, .spawned r' => r = r'
  | .pending (.ok p), .pending (.ok p') => p.pid = p'.pid ∧ p.pgid = p'.pgid
  | .pending (.error e), .pending (.error e') => e = e'
  | .aborted r, .aborted r' => r = r'
  | _, _ => False

/-- Execute one `RawFdPostForkReq` against `pf : PostFork.PostForkOpsM (StateM W) RawFd`. -/
def execRawFdPostForkReq {W : Type} (pf : PostFork.PostForkOpsM (StateM W) RawFd) :
    RawFdPostForkReq → StateM W RawFdPostForkOut
  | .spawn sp => RawFdPostForkOut.spawned <$> pf.spawn sp
  | .spawnWithBarrier sp => RawFdPostForkOut.pending <$> pf.spawnWithBarrier sp
  | .releaseBarrier p => RawFdPostForkOut.spawned <$> pf.releaseBarrier p
  | .abortBarrier p => RawFdPostForkOut.aborted <$> pf.abortBarrier p

/-- Unified raw capability request dispatched across all 9 `manifest.deps` capabilities of `FullSysOpsM`. -/
inductive FullRawReq where
  /-- Execute a `LinuxSyscall.TimeRand` request. -/
  | timeRand (req : TimeRand.TimeRandReq)
  /-- Execute a `LinuxSyscall.Passwd` request. -/
  | passwd (req : Passwd.PasswdReq)
  /-- Execute an `EnvVars.Raw.getEnv` lookup. -/
  | envGet (key : String)
  /-- Execute a `LinuxSyscall.Files` request over `RawFd`. -/
  | files (req : RawFdFilesReq)
  /-- Execute a `LinuxSyscall.Net` request over `RawFd`. -/
  | net (req : RawFdNetReq)
  /-- Execute a `LinuxSyscall.Poll.ppoll` readiness request over `RawFd`. -/
  | pollPpoll (fds : Array (RawFd × Poll.PollEvents)) (timeout : Option Poll.Timespec)
  /-- Execute a `LinuxSyscall.Process` request over `RawFd`. -/
  | proc (req : RawFdProcReq)
  /-- Execute a `LinuxSyscall.Sandbox` request over `RawFd`. -/
  | sandbox (req : RawFdSandboxReq)
  /-- Execute a `PostFork` request over `RawFd`. -/
  | postFork (req : RawFdPostForkReq)

instance : Inhabited FullRawReq :=
  ⟨.timeRand (.clock_gettime .monotonic)⟩

/-- Unified raw capability outcome paired with `FullRawReq`. -/
inductive FullRawOut where
  /-- Outcome of `timeRand`. -/
  | timeRand (out : TimeRand.TimeRandOutcome)
  /-- Outcome of `passwd`. -/
  | passwd (out : Passwd.PasswdOutcome)
  /-- Outcome of `envGet`. -/
  | envGet (res : Except EnvVars.Raw.EnvVarsRawError (Option String))
  /-- Outcome of `files`. -/
  | files (out : RawFdFilesOut)
  /-- Outcome of `net`. -/
  | net (out : RawFdNetOut)
  /-- Outcome of `pollPpoll`. -/
  | poll (out : Poll.PollOutcome)
  /-- Outcome of `proc`. -/
  | proc (out : RawFdProcOut)
  /-- Outcome of `sandbox`. -/
  | sandbox (out : RawFdSandboxOut)
  /-- Outcome of `postFork`. -/
  | postFork (out : RawFdPostForkOut)

instance : Inhabited FullRawOut :=
  ⟨.timeRand .unit⟩

/-- Execute one `FullRawReq` against `sys : FullSysOpsM (StateM W)`. -/
def execFullRawStep {W : Type} (sys : FullSysOpsM (StateM W)) : FullRawReq → StateM W FullRawOut
  | .timeRand r => FullRawOut.timeRand <$> TimeRand.execTimeRandReq sys.timeRand r
  | .passwd r => FullRawOut.passwd <$> Passwd.execPasswdReq sys.passwd r
  | .envGet k => FullRawOut.envGet <$> sys.envVars.getEnv k
  | .files r => FullRawOut.files <$> execRawFdFilesReq sys.files r
  | .net r => FullRawOut.net <$> execRawFdNetReq sys.net r
  | .pollPpoll fds to? =>
    (fun | .ok revs => FullRawOut.poll (.polled revs) | .error e => FullRawOut.poll (.err e)) <$>
      sys.poll.ppoll fds to?
  | .proc r => FullRawOut.proc <$> execRawFdProcReq sys.proc r
  | .sandbox r => FullRawOut.sandbox <$> execRawFdSandboxReq sys.sandbox r
  | .postFork r => FullRawOut.postFork <$> execRawFdPostForkReq sys.postFork r

/-- Relational step contract tying every `FullRawReq` directly to its canonical `manifest.deps` `healthyStep` / `allowedPkgStep` model while preserving `HealthyRawSysWorld.wf`. -/
def allowedFullRawStep (w : HealthyRawSysWorld) (req : FullRawReq)
    (out : FullRawOut) (w' : HealthyRawSysWorld) : Prop :=
  w'.wf = true ∧
  match req, out with
  | .timeRand treq, .timeRand tout =>
    TimeRand.healthyStep w.timeEnv treq tout = some w'.timeEnv
  | .passwd preq, .passwd pout =>
    Passwd.healthyStep w.passwdEnv preq pout = some w'.passwdEnv
  | .envGet key, .envGet res =>
    EnvVars.Raw.Model.allowedPkgStep w.envVarsSt (.getEnv key) (.valOpt res) w'.envVarsSt
  | .files freq, .files fout =>
    ∃ (toHid : RawFd → Nat) (mo : Files.FilesOutcome),
      RawFdFilesOut.MatchesModel fout mo ∧
      Files.healthyStep w.filesEnv (mapRawFdFilesReq toHid freq) mo = some w'.filesEnv
  | .net nreq, .net nout =>
    ∃ (toHid : RawFd → Nat) (mo : Net.NetOutcome),
      RawFdNetOut.MatchesModel nout mo ∧
      Net.healthyStep w.netEnv (mapRawFdNetReq toHid nreq) mo = some w'.netEnv
  | .pollPpoll fds to?, .poll pout =>
    ∃ toHid : RawFd → Nat,
      Poll.healthyStep w.pollEnv (.ppoll (fds.map fun p => (toHid p.1, p.2)) to?) pout = some w'.pollEnv
  | .proc preq, .proc pout =>
    ∃ (toHid : RawFd → Nat) (mo : LinuxSyscall.Process.ProcessOutcome),
      RawFdProcOut.MatchesModel pout mo ∧
      LinuxSyscall.Process.healthyStep w.procEnv (mapRawFdProcReq toHid preq) mo = some w'.procEnv
  | .sandbox sreq, .sandbox sout =>
    ∃ mo : LinuxSyscall.Sandbox.SandboxOutcome,
      RawFdSandboxOut.MatchesModel sout mo ∧
      Sandbox.healthyStep w.sandboxEnv (mapRawFdSandboxReq sreq) mo = some w'.sandboxEnv
  | .postFork pfreq, .postFork pfout =>
    ∃ (toHid : RawFd → Nat) (mo : PostFork.Model.PkgStepOut),
      RawFdPostForkOut.MatchesModel pfout mo ∧
      PostFork.Model.allowedPkgStep w.postForkSt (mapRawFdPostForkReq toHid pfreq) mo w'.postForkSt
  | _, _ => False

/-- Canonical single-step package executor alias for `OBEYS_SYNTH` verification. -/
abbrev execPkgStep {W : Type} := @execRawOpsStep W

/-- Canonical single-step package postcondition alias for `OBEYS_SYNTH` verification. -/
abbrev allowedPkgStep := allowedRawOpsStep

end LeanSwe.ProcessSandbox.Raw.Model
