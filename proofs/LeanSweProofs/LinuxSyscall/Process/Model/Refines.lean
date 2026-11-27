import LeanSweProofs.LinuxSyscall.Process.Model

/-!
# Capability-Parametric Refinement Model for `LeanSwe.LinuxSyscall.Process`

Defines the pure `killTargetOfPgid` behavior model, portable C-ABI wire
decoders, the raw `PosixProcessOpsM` single-step contract (`RawProcessOpsM`,
`RawProcessReq`, `RawProcessOut`, `execRawStep`, `allowedRawStep`,
`rawHealthyModelOps`), and package-level `HandleId` single-step entry points
(`HandleProcessOpsM`, `healthyModelOps`, `execPkgStep`, `allowedPkgStep`) over
`HealthyEnv`.
-/

namespace LeanSwe.LinuxSyscall.Process.Model

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Process

/-- Pure behavior model of `LeanSwe.LinuxSyscall.Process.killTargetOfPgid`. -/
def killTargetOfPgid (pgid : UInt32) : Int32 :=
  if pgid == 1 then 1 else -(pgid.toInt32)

/-- Monad-parameterized raw C-ABI `Process` capability family specialized to `HandleId`. -/
abbrev RawProcessOpsM (m : Type → Type) : Type :=
  PosixProcessOpsM m HandleId

/-- Monad-parameterized public `Process` capability family specialized to `HandleId`. -/
abbrev HandleProcessOpsM (m : Type → Type) : Type :=
  ProcessOpsM m HandleId

/-- Decode portable 36-bit `PipeFlags` wire mask (`bits >> 36 == 0`). -/
def decodeRawPipeFlags? (bits : UInt64) : Option PipeFlags :=
  if (bits >>> 36) == 0 then
    some { cloexec := (bits &&& 1) != 0
           nonblock := (bits &&& 2) != 0
           direct := (bits &&& 4) != 0
           notificationPipe := (bits &&& 8) != 0
           extraBits := (bits >>> 4).toUInt32 }
  else
    none

/-- Decode portable 38-bit `WaitFlags` wire mask (`bits >> 38 == 0`). -/
def decodeRawWaitFlags? (bits : UInt64) : Option WaitFlags :=
  if (bits >>> 38) == 0 then
    some { nohang := (bits &&& 1) != 0
           untraced := (bits &&& 2) != 0
           continued := (bits &&& 4) != 0
           wall := (bits &&& 8) != 0
           wclone := (bits &&& 16) != 0
           wnothread := (bits &&& 32) != 0
           extraBits := (bits >>> 6).toUInt32 }
  else
    none

/-- Decode portable `(sigTag, sigArg)` pair into `Signal`. -/
def decodeRawSignal? (tag : UInt8) (arg : Int32) : Option Signal :=
  match tag with
  | 0 => if arg == 0 then some .sigzero else none
  | 1 => if arg == 0 then some .sighup else none
  | 2 => if arg == 0 then some .sigint else none
  | 3 => if arg == 0 then some .sigkill else none
  | 4 => if arg == 0 then some .sigusr1 else none
  | 5 => if arg == 0 then some .sigusr2 else none
  | 6 => if arg == 0 then some .sigterm else none
  | 7 => if arg == 0 then some .sigcont else none
  | 8 => if arg == 0 then some .sigstop else none
  | 9 => some (.raw arg)
  | _ => none

/-- Decode portable 34-bit `PidfdOpenFlags` wire mask (`bits >> 34 == 0`). -/
def decodeRawPidfdOpenFlags? (bits : UInt64) : Option PidfdOpenFlags :=
  if (bits >>> 34) == 0 then
    some { nonblock := (bits &&& 1) != 0
           thread := (bits &&& 2) != 0
           extraBits := (bits >>> 2).toUInt32 }
  else
    none

/-- Decode portable 35-bit `PidfdSignalFlags` wire mask (`bits >> 35 == 0`). -/
def decodeRawPidfdSignalFlags? (bits : UInt64) : Option PidfdSignalFlags :=
  if (bits >>> 35) == 0 then
    some { thread := (bits &&& 1) != 0
           threadGroup := (bits &&& 2) != 0
           processGroup := (bits &&& 4) != 0
           extraBits := (bits >>> 3).toUInt32 }
  else
    none

/-- Encode a `WaitResult` into a Linux `<bits/waitstatus.h>` `RawWaitTuple`. -/
def encodeRawWait4 : WaitResult → RawWaitTuple
  | .stillRunning => (0, 0)
  | .exited pid code => (pid.toInt32, code.toUInt32 <<< 8)
  | .signaled pid sig core =>
    (pid.toInt32, (sig &&& 0x7f) ||| (if core then 0x80 else 0))
  | .stopped pid sig => (pid.toInt32, ((sig &&& 0xff) <<< 8) ||| 0x7f)
  | .continued pid => (pid.toInt32, 0xffff)

/-- Single-step request sum for `PosixProcessOpsM` C-ABI syscall hooks. -/
inductive RawProcessReq where
  /-- Raw `pipe2(flagsBits)`. -/
  | pipe2 (flagsBits : UInt64)
  /-- Raw `waitpid(pid, flagsBits)`. -/
  | waitpid (pid : Int32) (flagsBits : UInt64)
  /-- Raw `kill(pidOrNegPgid, sigTag, sigArg)`. -/
  | kill (pidOrNegPgid : Int32) (sigTag : UInt8) (sigArg : Int32)
  /-- Raw `pidfd_open(pid, flagsBits)`. -/
  | pidfd_open (pid : UInt32) (flagsBits : UInt64)
  /-- Raw `pidfd_send_signal(hid, sigTag, sigArg, flagsBits)`. -/
  | pidfd_send_signal (hid : HandleId) (sigTag : UInt8) (sigArg : Int32) (flagsBits : UInt64)
  /-- Raw `getpid()`. -/
  | getpid
  /-- Raw `getuid()`. -/
  | getuid
  deriving Repr, DecidableEq, Inhabited

/-- Single-step output sum for `PosixProcessOpsM` C-ABI syscall hooks. -/
inductive RawProcessOut where
  /-- `pipe2` succeeded returning `(readHid, writeHid)`. -/
  | piped (readHid : HandleId) (writeHid : HandleId)
  /-- `pidfd_open` succeeded returning `hid`. -/
  | opened (hid : HandleId)
  /-- `waitpid` succeeded returning `(rcPid, rawStatus)`. -/
  | rawWaited (t : RawWaitTuple)
  /-- Unit-returning syscall succeeded. -/
  | unit
  /-- `getpid` or `getuid` succeeded returning `val`. -/
  | u32 (val : UInt32)
  /-- Syscall failed with Linux `Errno`. -/
  | err (code : Errno)
  deriving Repr, DecidableEq, Inhabited

/-- Wrap `Except Errno (HandleId × HandleId)` into `RawProcessOut`. -/
def outcomeOfRawPiped : Except Errno (HandleId × HandleId) → RawProcessOut
  | .ok (rHid, wHid) => .piped rHid wHid
  | .error e => .err e

/-- Wrap `Except Errno HandleId` into `RawProcessOut`. -/
def outcomeOfRawOpened : Except Errno HandleId → RawProcessOut
  | .ok hid => .opened hid
  | .error e => .err e

/-- Wrap `Except Errno RawWaitTuple` into `RawProcessOut`. -/
def outcomeOfRawWaited : Except Errno RawWaitTuple → RawProcessOut
  | .ok t => .rawWaited t
  | .error e => .err e

/-- Wrap `Except Errno Unit` into `RawProcessOut`. -/
def outcomeOfRawUnit : Except Errno Unit → RawProcessOut
  | .ok () => .unit
  | .error e => .err e

/-- Wrap `Except Errno UInt32` into `RawProcessOut`. -/
def outcomeOfRawU32 : Except Errno UInt32 → RawProcessOut
  | .ok v => .u32 v
  | .error e => .err e

/-- Convert a `RawProcessOut` into its domain `ProcessOutcome`. -/
def toModelOutcome : RawProcessOut → ProcessOutcome
  | .piped r w => .piped r w
  | .opened h => .opened h
  | .rawWaited t => .waited (WaitResult.ofRawWait4 t)
  | .unit => .unit
  | .u32 v => .u32 v
  | .err e => .err e

/-- Decode a `RawProcessReq` into its domain `ProcessReq` if all wire flags/signals are portable. -/
def decodeRawProcessReq? : RawProcessReq → Option ProcessReq
  | .pipe2 flBits => (decodeRawPipeFlags? flBits).map ProcessReq.pipe2
  | .waitpid pid flBits => (decodeRawWaitFlags? flBits).map (ProcessReq.waitpid pid ·)
  | .kill pid tag arg => (decodeRawSignal? tag arg).map (ProcessReq.kill pid ·)
  | .pidfd_open pid flBits =>
    (decodeRawPidfdOpenFlags? flBits).map (ProcessReq.pidfd_open pid ·)
  | .pidfd_send_signal hid tag arg flBits =>
    match decodeRawSignal? tag arg, decodeRawPidfdSignalFlags? flBits with
    | some sig, some fl => some (.pidfd_send_signal hid sig fl)
    | _, _ => none
  | .getpid => some .getpid
  | .getuid => some .getuid

/-- Execute one `RawProcessReq` against a `RawProcessOpsM (StateM W)` bundle. -/
def execRawStep {W : Type} (raw : RawProcessOpsM (StateM W)) :
    RawProcessReq → StateM W RawProcessOut
  | .pipe2 flBits => outcomeOfRawPiped <$> raw.pipe2 flBits
  | .waitpid pid flBits => outcomeOfRawWaited <$> raw.waitpid pid flBits
  | .kill pid tg ag => outcomeOfRawUnit <$> raw.kill pid tg ag
  | .pidfd_open pid flBits => outcomeOfRawOpened <$> raw.pidfd_open pid flBits
  | .pidfd_send_signal h tg ag flBits => outcomeOfRawUnit <$> raw.pidfd_send_signal h tg ag flBits
  | .getpid => outcomeOfRawU32 <$> raw.getpid
  | .getuid => outcomeOfRawU32 <$> raw.getuid

/-- Allowed single-step relation for `PosixProcessOpsM` over `HealthyEnv`. -/
def allowedRawStep (env : HealthyEnv) (req : RawProcessReq) (out : RawProcessOut)
    (env' : HealthyEnv) : Prop :=
  match decodeRawProcessReq? req with
  | some preq => healthyStep env preq (toModelOutcome out) = some env'
  | none => out = .err Errno.EINVAL ∧ env' = env

/-- Check that a `WaitResult` outcome round-trips losslessly through `encodeRawWait4`. -/
def waitResFitsRaw : Except Errno WaitResult → Bool
  | .ok wr => WaitResult.ofRawWait4 (encodeRawWait4 wr) == wr
  | .error _ => true

/-- Run `modelOps` over `HealthyEnv`, falling back to `Errno.ENOSPC` on `waitpid` if `healthyStep` or `waitResFitsRaw` rejects the candidate outcome. -/
def runHealthyWaitpid (pid : Int32) (flags : WaitFlags) :
    StateM HealthyEnv (Except Errno WaitResult) := fun env =>
  let (candRes, _) := (modelOps.waitpid pid flags).run env.state
  if waitResFitsRaw candRes then
    match healthyStep env (.waitpid pid flags) (outcomeOfWaited candRes) with
    | some env' => if env'.wf then (candRes, env') else (.error Errno.ENOSPC, env)
    | none => (.error Errno.ENOSPC, env)
  else
    (.error Errno.ENOSPC, env)

/-- Lift a non-`EINTR`, non-critical `modelOps` step onto `HealthyEnv`. -/
def liftHealthyProcessOp {α : Type} (act : StateM ProcessSysState α) :
    StateM HealthyEnv α := fun env =>
  let (res, s') := act.run env.state
  (res, { env with state := s' })

/-- Reference `HandleProcessOpsM (StateM HealthyEnv)` satisfying `healthyStep` from every well-formed `HealthyEnv`. -/
def healthyModelOps : HandleProcessOpsM (StateM HealthyEnv) :=
  { pipe2 := fun flags => liftHealthyProcessOp (modelOps.pipe2 flags)
    waitpid := runHealthyWaitpid
    kill := fun pid sig => liftHealthyProcessOp (modelOps.kill pid sig)
    pidfd_open := fun pid flags => liftHealthyProcessOp (modelOps.pidfd_open pid flags)
    pidfd_send_signal := fun hid sig flags =>
      liftHealthyProcessOp (modelOps.pidfd_send_signal hid sig flags)
    getpid := liftHealthyProcessOp modelOps.getpid
    getuid := liftHealthyProcessOp modelOps.getuid }

/-- Reference `RawProcessOpsM (StateM HealthyEnv)` witness satisfying `allowedRawStep`. -/
def rawHealthyModelOps : RawProcessOpsM (StateM HealthyEnv) :=
  { pipe2 := fun flBits =>
      match decodeRawPipeFlags? flBits with
      | some fl => healthyModelOps.pipe2 fl
      | none => pure (.error Errno.EINVAL)
    waitpid := fun pid flBits =>
      match decodeRawWaitFlags? flBits with
      | some fl => do
        match ← healthyModelOps.waitpid pid fl with
        | .ok wr => return .ok (encodeRawWait4 wr)
        | .error e => return .error e
      | none => pure (.error Errno.EINVAL)
    kill := fun pid tg ag =>
      match decodeRawSignal? tg ag with
      | some sig => healthyModelOps.kill pid sig
      | none => pure (.error Errno.EINVAL)
    pidfd_open := fun pid flBits =>
      match decodeRawPidfdOpenFlags? flBits with
      | some fl => healthyModelOps.pidfd_open pid fl
      | none => pure (.error Errno.EINVAL)
    pidfd_send_signal := fun h tg ag flBits =>
      match decodeRawSignal? tg ag, decodeRawPidfdSignalFlags? flBits with
      | some sig, some fl => healthyModelOps.pidfd_send_signal h sig fl
      | _, _ => pure (.error Errno.EINVAL)
    getpid := healthyModelOps.getpid
    getuid := healthyModelOps.getuid }

/-- Execute one single-syscall `ProcessReq` against a `HandleProcessOpsM (StateM W)` capability bundle. -/
def execSingleStep {W : Type} (ops : HandleProcessOpsM (StateM W)) (req : ProcessReq) :
    StateM W ProcessOutcome :=
  execProcessReq ops req

/-- Allowed single-syscall transition relation for `ProcessOpsM` over `HealthyEnv`. -/
def allowedSingleStep (env : HealthyEnv) (req : ProcessReq) (out : ProcessOutcome)
    (env' : HealthyEnv) : Prop :=
  healthyStep env req out = some env'

/-- Capability-parametric function family `Int32 → Nat → m (Except (Option Errno) Unit)` of `Process.waitpidReapLoop`. -/
abbrev WaitpidReapLoopFn (m : Type → Type) : Type :=
  Int32 → Nat → m (Except (Option Errno) Unit)

/-- Execute `Process.waitpidReapLoop` on `(pid, fuel)` inside `StateM W`. -/
def execWaitpidReapLoop {W : Type} (fn : WaitpidReapLoopFn (StateM W)) (req : Int32 × Nat) :
    StateM W (Except (Option Errno) Unit) :=
  fn req.1 req.2

/-- Relational fuel-bounded step postcondition for `Process.waitpidReapLoop` over `HealthyEnv`. -/
def allowedWaitpidReapLoopAux (pid : Int32) :
    Nat → HealthyEnv → Except (Option Errno) Unit → HealthyEnv → Prop
  | 0, env, out, env' => env.wf = true ∧ out = .error none ∧ env' = env
  | fuel + 1, env, out, env' =>
    (∃ wr : WaitResult, out = .ok () ∧
      healthyStep env (.waitpid pid {}) (.waited wr) = some env') ∨
    (out = .ok () ∧
      healthyStep env (.waitpid pid {}) (.err Errno.ECHILD) = some env') ∨
    (∃ e : Errno, e ≠ Errno.EINTR ∧ e ≠ Errno.ECHILD ∧ out = .error (some e) ∧
      healthyStep env (.waitpid pid {}) (.err e) = some env') ∨
    (∃ envMid : HealthyEnv,
      healthyStep env (.waitpid pid {}) (.err Errno.EINTR) = some envMid ∧
      allowedWaitpidReapLoopAux pid fuel envMid out env')

/-- Relational postcondition for `Process.waitpidReapLoop` over `HealthyEnv`. -/
def allowedWaitpidReapLoop (env : HealthyEnv) (req : Int32 × Nat)
    (out : Except (Option Errno) Unit) (env' : HealthyEnv) : Prop :=
  allowedWaitpidReapLoopAux req.1 req.2 env out env'

/-- Package-level request covering both individual `ProcessReq` syscalls and `waitpidReapLoop`. -/
inductive PkgProcessReq where
  /-- Single `ProcessReq` syscall operation. -/
  | syscall (req : ProcessReq)
  /-- Fuel-bounded `waitpidReapLoop` operation on `(pid, fuel)`. -/
  | reapLoop (pid : Int32) (fuel : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Package-level outcome corresponding to `PkgProcessReq`. -/
inductive PkgProcessOut where
  /-- Outcome of a single `ProcessReq` syscall operation. -/
  | syscall (out : ProcessOutcome)
  /-- Outcome of `waitpidReapLoop`. -/
  | reaped (res : Except (Option Errno) Unit)
  deriving Repr, Inhabited

/-- Fuel-bounded `waitpid` reap loop over any `[Monad m]` `ProcessOpsM` capability bundle. -/
def execReapLoop {m : Type → Type} [Monad m] {fd : Type}
    (proc : ProcessOpsM m fd) (pid : Int32) :
    Nat → m (Except (Option Errno) Unit)
  | 0 => pure (.error none)
  | fuel + 1 => do
    match ← proc.waitpid pid {} with
    | .ok _ => return .ok ()
    | .error e =>
      if e == Errno.EINTR then execReapLoop proc pid fuel
      else if e == Errno.ECHILD then return .ok ()
      else return .error (some e)

/-- Execute one `PkgProcessReq` against a `HandleProcessOpsM (StateM W)` capability bundle. -/
def execPkgStep {W : Type} (ops : HandleProcessOpsM (StateM W)) :
    PkgProcessReq → StateM W PkgProcessOut
  | .syscall req => do
    let out ← execProcessReq ops req
    return .syscall out
  | .reapLoop pid fuel => do
    let res ← execReapLoop ops pid fuel
    return .reaped res

/-- Allowed package-level transition relation for `ProcessOpsM` over `HealthyEnv`. -/
def allowedPkgStep (env : HealthyEnv) :
    PkgProcessReq → PkgProcessOut → HealthyEnv → Prop
  | .syscall req, .syscall out, env' => healthyStep env req out = some env'
  | .reapLoop pid fuel, .reaped res, env' => allowedWaitpidReapLoopAux pid fuel env res env'
  | _, _, _ => False

end LeanSwe.LinuxSyscall.Process.Model
