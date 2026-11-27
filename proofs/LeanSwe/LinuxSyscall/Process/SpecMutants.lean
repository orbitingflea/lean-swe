import LeanSwe.LinuxSyscall.Process.SpecTests
import LeanSwe.LinuxSyscall.Process.SpecMutants.Extra

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

example : ¬ Core.AllPass (test_process_errno_classificationAndTransient
    (fun e => e == Errno.EFAULT || Errno.isTransientOsErrno e)
    ProcessErrorKind.ofErrno) := by
  intro h
  have h0 := h Errno.EFAULT
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_process_errno_classificationAndTransient
    Errno.isTransientOsErrno
    (fun e => if e == Errno.ECHILD then .noSuchProcess else ProcessErrorKind.ofErrno e)) := by
  intro h
  have h0 := h Errno.ECHILD
  exact absurd h0.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_errno_classificationAndTransient
    Errno.isTransientOsErrno
    (fun e => if e == Errno.ENOENT then .invalidArg else ProcessErrorKind.ofErrno e)) := by
  intro h
  have h0 := h Errno.ENOENT
  exact absurd h0.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_errno_classificationAndTransient
    Errno.isTransientOsErrno
    (fun e => if e == Errno.EFAULT || e == (999 : Errno) then .invalidArg else ProcessErrorKind.ofErrno e)) := by
  intro h
  have h0 := h (999 : Errno)
  exact absurd h0.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_flagsAndSignals_encodersInjectiveAndValid
    (encPipe := fun f => { f with nonblock := false }.toBits)) := by
  intro h
  have h0 := h { nonblock := false } { nonblock := true }
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_process_flagsAndSignals_encodersInjectiveAndValid
    (encPipe := fun f =>
      (if f.nonblock then (1 : UInt64) else 0) |||
      (if f.cloexec then (2 : UInt64) else 0) |||
      (f.extraBits.toUInt64 <<< 2))) := by
  intro h
  have h0 := h { cloexec := true, nonblock := false } { cloexec := true, nonblock := false }
  exact absurd h0.2.1 (by decide)

example : ¬ Core.AllPass (test_process_flagsAndSignals_encodersInjectiveAndValid
    (pipeValid := fun _ => true)) := by
  intro h
  have h0 := h { extraBits := 1 } { extraBits := 1 }
  exact absurd h0.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_flagsAndSignals_encodersInjectiveAndValid
    (encWait := fun f =>
      (if f.nohang then (1 : UInt64) else 0) |||
      (if f.untraced then (2 : UInt64) else 0) |||
      (if f.continued then (4 : UInt64) else 0) |||
      (f.extraBits.toUInt64 <<< 2))) := by
  intro h
  have h0 := (h {} {}).2.2.2 { continued := true, extraBits := 0 } { continued := false, extraBits := 1 }
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_process_flagsAndSignals_encodersInjectiveAndValid
    (waitValid := fun _ => true)) := by
  intro h
  have h0 := (h {} {}).2.2.2 { extraBits := 1 } { extraBits := 1 }
  exact absurd h0.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_flagsAndSignals_encodersInjectiveAndValid
    (encSig := fun s => (0, Int32.ofInt s.toLinuxNum))) := by
  intro h
  have h0 := ((h {} {}).2.2.2 {} {}).2.2.2 .sigterm (.raw 15)
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_process_flagsAndSignals_encodersInjectiveAndValid
    (sigValid := fun s => decide (0 ≤ s.toLinuxNum ∧ s.toLinuxNum ≤ 65))) := by
  intro h
  have h0 := ((h {} {}).2.2.2 {} {}).2.2.2 (.raw 65) (.raw 65)
  exact absurd h0.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_flagsAndSignals_encodersInjectiveAndValid
    (encPidfdOpen := fun f => if f.nonblock then 1 else 0)) := by
  intro h
  have h0 := (((h {} {}).2.2.2 {} {}).2.2.2 .sigzero .sigzero).2.2.2.2 { extraBits := 0 } { extraBits := 1 }
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_process_flagsAndSignals_encodersInjectiveAndValid
    (pidfdOpenValid := fun _ => true)) := by
  intro h
  have h0 := (((h {} {}).2.2.2 {} {}).2.2.2 .sigzero .sigzero).2.2.2.2 { extraBits := 1 } { extraBits := 1 }
  exact absurd h0.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_flagsAndSignals_encodersInjectiveAndValid
    (encPidfdSig := fun f =>
      (if f.processGroup then (1 : UInt64) else 0) |||
      (if f.threadGroup then (2 : UInt64) else 0) |||
      (if f.thread then (4 : UInt64) else 0) |||
      (f.extraBits.toUInt64 <<< 3))) := by
  intro h
  have h0 := ((((h {} {}).2.2.2 {} {}).2.2.2 .sigzero .sigzero).2.2.2.2 {} {}).2.2.2
    { thread := true } { thread := true }
  exact absurd h0.2.1 (by decide)

example : ¬ Core.AllPass (test_process_flagsAndSignals_encodersInjectiveAndValid
    (pidfdSigValid := fun f => f.extraBits == 0)) := by
  intro h
  have h0 := ((((h {} {}).2.2.2 {} {}).2.2.2 .sigzero .sigzero).2.2.2.2 {} {}).2.2.2
    { thread := true, threadGroup := true } { thread := true, threadGroup := true }
  exact absurd h0.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_waitResult_ofRawWait4_decodesAllStatuses
    (fun (rc, raw) =>
      if rc < 0 then .stillRunning
      else WaitResult.ofRawWait4 (1, raw))) := by
  intro h
  have h0 := h 0 (by decide) 1234 (by decide) 0 0 9 (by decide) false 19 0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_process_waitResult_ofRawWait4_decodesAllStatuses
    (fun (rc, raw) =>
      if rc <= 0 then .stillRunning
      else WaitResult.ofRawWait4 (1234, raw))) := by
  intro h
  have h0 := h 0 (by decide) 7777 (by decide) 0 42 9 (by decide) false 19 0
  exact absurd h0.2.1 (by decide)

example : ¬ Core.AllPass (test_process_waitResult_ofRawWait4_decodesAllStatuses
    (fun (rc, raw) =>
      if rc <= 0 then .stillRunning
      else if (raw &&& 0x7f) != 0 && (raw &&& 0x7f) != 0x7f then
        .signaled rc.toUInt32 (raw &&& 0xff) ((raw &&& 0x80) != 0)
      else WaitResult.ofRawWait4 (rc, raw))) := by
  intro h
  have h0 := h 0 (by decide) 1234 (by decide) 0 0 15 (by decide) true 19 0
  exact absurd h0.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_waitResult_ofRawWait4_decodesAllStatuses
    (fun (rc, raw) =>
      if rc <= 0 then .stillRunning
      else if (raw &&& 0x7f) == 0x7f && (raw &&& 0xff) == 0x7f then
        .stopped rc.toUInt32 (raw >>> 8)
      else WaitResult.ofRawWait4 (rc, raw))) := by
  intro h
  have h0 := h 0 (by decide) 1234 (by decide) 0 0 9 (by decide) false 19 1
  exact absurd h0.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_waitResult_ofRawWait4_decodesAllStatuses
    (fun (rc, raw) =>
      if rc <= 0 then .stillRunning
      else if (raw &&& 0x7f) == 0x7f then .stopped rc.toUInt32 ((raw >>> 8) &&& 0xff)
      else WaitResult.ofRawWait4 (rc, raw))) := by
  intro h
  have h0 := h 0 (by decide) 1234 (by decide) 0 0 9 (by decide) false 19 0
  exact absurd h0.2.2.2.2.1 (by decide)

private def baseMkOps (raw : PosixProcessOpsM (StateM Nat) Nat) : ProcessOpsM (StateM Nat) Nat :=
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

example : ¬ Core.AllPass (test_process_impl_mkProcessOps_wiresEncodersAndDecodesWait4 fun raw =>
    { baseMkOps raw with
      kill := fun pid sig =>
        let (tag, arg) := sig.toRaw
        raw.kill pid tag arg }) := by
  intro h
  have h0 := (h {} 2000 {} (2000, 0) 2000 (.raw 32) 2000 {} 4 .sigzero {} 1000 500 Errno.EIO 0).2.2.1
  dsimp only [baseMkOps, Bind.bind, StateT.bind, assert, StateT.run, pure, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h0
  have h1 : (Except.ok () : Except Errno Unit) = Except.error Errno.EINVAL :=
    congrArg Prod.fst h0
  cases h1

example : ¬ Core.AllPass (test_process_impl_mkProcessOps_wiresEncodersAndDecodesWait4 fun raw =>
    { baseMkOps raw with
      pidfd_send_signal := fun pfd sig flags =>
        let (tag, arg) := sig.toRaw
        raw.pidfd_send_signal pfd tag arg flags.toBits }) := by
  intro h
  have h0 := (h {} 2000 {} (2000, 0) 2000 .sigzero 2000 {} 4 (.raw 33) {} 1000 500 Errno.EIO 0).2.2.2.2.1
  dsimp only [baseMkOps, Bind.bind, StateT.bind, assert, StateT.run, pure, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h0
  have h1 : (Except.ok () : Except Errno Unit) = Except.error Errno.EINVAL :=
    congrArg Prod.fst h0
  cases h1

example : ¬ Core.AllPass (test_process_impl_mkProcessOps_wiresEncodersAndDecodesWait4 fun raw =>
    { baseMkOps raw with
      pipe2 := fun _ => raw.pipe2 0 }) := by
  intro h
  have h0 := (h { cloexec := true } 2000 {} (2000, 0) 2000 .sigzero 2000 {} 4 .sigzero {} 1000 500 Errno.EIO 0).1
  dsimp only [baseMkOps, Bind.bind, StateT.bind, assert, StateT.run, pure, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h0
  have h1 : (Except.error Errno.EINVAL : Except Errno (Nat × Nat)) = Except.ok (5, 6) :=
    congrArg Prod.fst h0
  cases h1

example : ¬ Core.AllPass (test_process_impl_mkProcessOps_wiresEncodersAndDecodesWait4 fun raw =>
    { baseMkOps raw with
      waitpid := fun pid flags => do
        match ← raw.waitpid pid flags.toBits with
        | .ok _ => return .ok .stillRunning
        | .error e => return .error e }) := by
  intro h
  have h0 := (h {} 2000 {} (2000, 0) 2000 .sigzero 2000 {} 4 .sigzero {} 1000 500 Errno.EIO 0).2.1
  dsimp only [baseMkOps, Bind.bind, StateT.bind, assert, StateT.run, pure, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h0
  have h1 : (Except.ok WaitResult.stillRunning : Except Errno WaitResult) =
      Except.ok (WaitResult.ofRawWait4 (2000, 0)) :=
    congrArg Prod.fst h0
  exact absurd h1 (by decide)

example : ¬ Core.AllPass (test_process_impl_mkProcessOps_wiresEncodersAndDecodesWait4 fun raw =>
    { baseMkOps raw with
      getpid := raw.getuid
      getuid := raw.getpid }) := by
  intro h
  have h0 := (h {} 2000 {} (2000, 0) 2000 .sigzero 2000 {} 4 .sigzero {} 1000 500 Errno.EIO 0).2.2.2.2.2.1
  dsimp only [baseMkOps, Bind.bind, StateT.bind, assert, StateT.run, pure, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h0
  have h1 : (Except.ok (500 : UInt32) : Except Errno UInt32) = .ok 1000 := congrArg Prod.fst h0
  exact absurd h1 (by decide)

example : ¬ Core.AllPass (test_process_impl_mkProcessOps_wiresEncodersAndDecodesWait4 fun raw =>
    { baseMkOps raw with
      pidfd_send_signal := fun pfd sig _ =>
        let (tag, arg) := sig.toRaw
        raw.pidfd_send_signal pfd tag arg 0 }) := by
  intro h
  have h0 := (h {} 2000 {} (2000, 0) 2000 .sigzero 2000 {} 4 .sigterm { processGroup := true } 1000 500 Errno.EIO 0).2.2.2.2.1
  dsimp only [baseMkOps, Bind.bind, StateT.bind, assert, StateT.run, pure, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h0
  have h1 : (Except.error Errno.EINVAL : Except Errno Unit) = Except.ok () :=
    congrArg Prod.fst h0
  cases h1

example : ¬ Core.AllPass (test_process_impl_mkProcessOps_wiresEncodersAndDecodesWait4 fun raw =>
    { baseMkOps raw with
      kill := fun pid sig => do
        let (tag, arg) := sig.toRaw
        match ← raw.kill pid tag arg with
        | .ok () => return .ok ()
        | .error _ => return .error Errno.EINVAL }) := by
  intro h
  have h0 := (h {} 2000 {} (2000, 0) 2000 .sigzero 2000 {} 4 .sigzero {} 1000 500 Errno.ESRCH 0).2.2.2.2.2.2.2.2.2.1
  dsimp only [baseMkOps, Bind.bind, StateT.bind, assert, StateT.run, pure, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h0
  have h1 : (Except.error Errno.EINVAL : Except Errno Unit) = Except.error Errno.ESRCH :=
    congrArg Prod.fst h0
  exact absurd h1 (by decide)

example : ¬ Core.AllPass (test_process_ops_pipe2_flagsAndDistinctHandles
    { modelOps with
      pipe2 := fun flags => do
        let s ← get
        let rHid := nextFreeHid s.fds s.nextHid
        let wHid := rHid + 1
        set (commitPipeFds s rHid wHid flags)
        return .ok (rHid, wHid) }) := by
  intro h
  have h0 := h ProcessSysState.initial { extraBits := 1 } (by decide)
  dsimp only [Bind.bind, assert, StateT.run, StateT.get, StateT.set, get, set, getThe,
    MonadState.get, MonadStateOf.get, MonadStateOf.set, pure, StateT.pure] at h0
  cases h0.1

example : ¬ Core.AllPass (test_process_ops_pipe2_flagsAndDistinctHandles
    { modelOps with
      pipe2 := fun flags => do
        let s ← get
        if !flags.isValid then return .error Errno.EINVAL
        else
          let rHid := nextFreeHid s.fds s.nextHid
          set (commitPipeFds s rHid rHid flags)
          return .ok (rHid, rHid) }) := by
  intro h
  have h0 := h ProcessSysState.initial { extraBits := 1 } (by decide)
  dsimp only [Bind.bind, assert, StateT.run, StateT.get, StateT.set, get, set, getThe,
    MonadState.get, MonadStateOf.get, MonadStateOf.set, pure, StateT.pure] at h0
  exact absurd h0.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_getpidAndGetuid_consistentAndPositive
    { modelOps with getpid := pure (.ok 0) }) := by
  intro h
  have h0 := h ProcessSysState.initial
  dsimp only [Bind.bind, assert, StateT.run, pure, StateT.pure] at h0
  exact absurd h0.1.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_getpidAndGetuid_consistentAndPositive
    { modelOps with
      getpid := do
        let s ← get
        let p := effectiveSelfPid s
        set { s with nextHid := s.nextHid + 1 }
        return .ok p }) := by
  intro h
  have h0 := h (ProcessSysState.initial 1000 1000 500)
  dsimp only [modelOps, Bind.bind, assert, StateT.run, StateT.get, StateT.set, get, set, getThe,
    MonadState.get, MonadStateOf.get, MonadStateOf.set, pure, StateT.pure] at h0
  exact absurd h0.1.2.2.2 (by decide)

example : ¬ Core.AllPass (test_process_ops_getpidAndGetuid_consistentAndPositive
    { modelOps with
      getuid := do
        let s ← get
        set { s with selfUid := s.selfUid + 1 }
        return .ok s.selfUid }) := by
  intro h
  have h0 := h (ProcessSysState.initial 1000 1000 500)
  dsimp only [modelOps, Bind.bind, assert, StateT.run, StateT.get, StateT.set, get, set, getThe,
    MonadState.get, MonadStateOf.get, MonadStateOf.set, pure, StateT.pure] at h0
  exact absurd h0.2.1.2 (by decide)

example : ¬ Core.AllPass (test_process_ops_waitpid_optionsWnohangAndExitedReap
    { modelOps with
      waitpid := fun pid flags =>
        match pid == Int32.minValue with
        | true => pure (.error Errno.ESRCH)
        | false => modelOps.waitpid pid flags }) := by
  intro h
  exact absurd h.1.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_waitpid_optionsWnohangAndExitedReap
    { modelOps with
      waitpid := fun pid flags =>
        match !flags.isValid with
        | true => pure (.error Errno.EINVAL)
        | false =>
          match pid == Int32.minValue with
          | true => pure (.error Errno.ECHILD)
          | false => modelOps.waitpid pid flags }) := by
  intro h
  exact absurd h.2.1.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_waitpid_optionsWnohangAndExitedReap
    { modelOps with
      waitpid := fun pid flags =>
        match !flags.nohang && pid == 2001 with
        | true => pure (.ok (.exited 2001 0))
        | false => modelOps.waitpid pid flags }) := by
  intro h
  exact absurd h.2.2.2.2.1.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_waitpid_optionsWnohangAndExitedReap
    { modelOps with
      waitpid := fun pid flags => do
        let s ← get
        let (res, _) := evalModelWaitpid s pid flags
        return res }) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_waitpid_stopContinueAndSignaledReap
    { modelOps with
      kill := fun pid sig =>
        match sig == .raw 20 with
        | true => modelOps.kill pid .sigkill
        | false => modelOps.kill pid sig }) := by
  intro h
  exact absurd h.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_waitpid_stopContinueAndSignaledReap
    { modelOps with
      waitpid := fun pid flags => do
        let s ← get
        match evalModelWaitpid s pid flags with
        | (.ok (.stopped cPid sig), _) =>
          set (reapThreadGroup s cPid)
          return .ok (.stopped cPid sig)
        | (res, s') => set s'; return res }) := by
  intro h
  exact absurd h.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_waitpid_queuedFatalAcrossSigcont
    { modelOps with
      kill := fun pid sig =>
        match sig == .sigterm with
        | true => pure (.ok ())
        | false => modelOps.kill pid sig }) := by
  intro h
  exact absurd h.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_waitpid_queuedFatalAcrossSigcont
    { modelOps with
      kill := fun pid sig =>
        match sig == .sigterm with
        | true => modelOps.kill pid .sigkill
        | false => modelOps.kill pid sig }) := by
  intro h
  exact absurd h.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_kill_precedencePermissionsAndIgnoredSignals
    { modelOps with
      kill := fun pidOrNegPgid sig =>
        match !sig.isValid with
        | true => pure (.error Errno.EINVAL)
        | false => modelOps.kill pidOrNegPgid sig }) := by
  intro h
  exact absurd h.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_kill_precedencePermissionsAndIgnoredSignals
    { modelOps with
      kill := fun pidOrNegPgid sig =>
        match pidOrNegPgid == 1 with
        | true => pure (.error Errno.EPERM)
        | false => modelOps.kill pidOrNegPgid sig }) := by
  intro h
  exact absurd h.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_kill_precedencePermissionsAndIgnoredSignals
    { modelOps with
      kill := fun pidOrNegPgid sig =>
        match sig == .raw 17 with
        | true => modelOps.kill pidOrNegPgid .sigkill
        | false => modelOps.kill pidOrNegPgid sig }) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_kill_precedencePermissionsAndIgnoredSignals
    { modelOps with
      kill := fun pidOrNegPgid sig =>
        match pidOrNegPgid == -1 && sig == .sigterm with
        | true => pure (.error Errno.EPERM)
        | false => modelOps.kill pidOrNegPgid sig }) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.1.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_kill_precedencePermissionsAndIgnoredSignals
    { modelOps with
      kill := fun pidOrNegPgid sig =>
        match pidOrNegPgid == -2 && sig == .sigzero with
        | true => pure (.ok ())
        | false => modelOps.kill pidOrNegPgid sig }) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.1.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_kill_sigzeroZombieAndProcessGroup
    { modelOps with
      kill := fun pidOrNegPgid sig =>
        match sig == .sigzero with
        | true => modelOps.kill pidOrNegPgid .sigkill
        | false => modelOps.kill pidOrNegPgid sig }) := by
  intro h
  exact absurd h.1.2 (by decide)

example : ¬ Core.AllPass (test_process_ops_kill_nonLeaderThreadRoutesToTgidAndReaps
    { modelOps with
      kill := fun pidOrNegPgid sig =>
        match pidOrNegPgid == 2021 with
        | true => pure (.ok ())
        | false => modelOps.kill pidOrNegPgid sig }) := by
  intro h
  exact absurd h.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_kill_nonLeaderThreadRoutesToTgidAndReaps
    { modelOps with
      pidfd_open := fun pid flags =>
        match pid == 2021 with
        | true => pure (.error Errno.ENOENT)
        | false => modelOps.pidfd_open pid flags }) := by
  intro h
  exact absurd h.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_pidfdOpen_validationThreadAndZombie
    { modelOps with
      pidfd_open := fun pid flags =>
        match !flags.isValid with
        | true => pure (.error Errno.EINVAL)
        | false =>
          match pid == 0 with
          | true => pure (.error Errno.ESRCH)
          | false => modelOps.pidfd_open pid flags }) := by
  intro h
  exact absurd h.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_pidfdOpen_validationThreadAndZombie
    { modelOps with
      pidfd_open := fun pid flags => do
        let s ← get
        match assocGet s.procs pid with
        | some e =>
          match e.lifecycle with
          | .zombie _ => return .error Errno.ESRCH
          | _ => modelOps.pidfd_open pid flags
        | none => modelOps.pidfd_open pid flags }) := by
  intro h
  exact absurd h.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_pidfdOpen_validationThreadAndZombie
    { modelOps with
      pidfd_open := fun pid flags =>
        match pid == 1001 with
        | true => pure (.ok 77)
        | false => modelOps.pidfd_open pid flags }) := by
  intro h
  exact absurd h.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_pidfdSendSignal_fdKindsAndFlags
    { modelOps with
      pidfd_send_signal := fun hid sig flags => do
        let s ← get
        match assocGet s.fds hid with
        | some (.pipeRead _ _) => return .error Errno.EINVAL
        | _ => modelOps.pidfd_send_signal hid sig flags }) := by
  intro h
  exact absurd h.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_pidfdSendSignal_permissionsAndPostReap
    { modelOps with
      pidfd_send_signal := fun hid sig flags => do
        let s ← get
        match assocGet s.fds hid with
        | some (.pidfd targetPid _ _) =>
          match assocGet s.procs targetPid with
          | none =>
            match flags.isValid with
            | true => return .ok ()
            | false => modelOps.pidfd_send_signal hid sig flags
          | some _ => modelOps.pidfd_send_signal hid sig flags
        | _ => modelOps.pidfd_send_signal hid sig flags }) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_process_ops_pidfdSendSignal_processGroupAfterLeaderReapOrMove
    { modelOps with
      pidfd_send_signal := fun hid sig flags => do
        let s ← get
        match assocGet s.fds hid with
        | some (.pidfd targetPid _ _) =>
          match assocGet s.procs targetPid with
          | none => return .error Errno.ESRCH
          | some _ => modelOps.pidfd_send_signal hid sig flags
        | _ => modelOps.pidfd_send_signal hid sig flags }) := by
  intro h
  exact absurd h.2.2.1 (by decide)

end LeanSwe.LinuxSyscall.Process
