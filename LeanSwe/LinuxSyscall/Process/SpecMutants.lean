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
      { Internal.mkProcessOps raw with
        kill := fun pid sig =>
          if sig.isNptlReserved then pure (.error Errno.EPERM)
          else (Internal.mkProcessOps raw).kill pid sig })) := by
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
    { defaultOps with kill := fun _ _ => pure (.error Errno.EPERM) }) := by
  intro h
  rcases h with ⟨⟨raw, hmk⟩, _⟩
  have hk := congrArg (fun o => o.kill 0 (.raw 32)) hmk
  exact (inferInstance : Nonempty (Void IO.RealWorld)).elim fun w => by
    have hw := congrFun hk w
    cases hw

example : ¬ Core.AllPass (test_process_interface_defaultOpsWiring
    { defaultOps with
      pidfd_send_signal := fun _ _ flags =>
        if flags == {} then pure (.error Errno.EPERM) else pure (.error Errno.EINVAL) }) := by
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
