import LeanSwe.ProcessSandbox.Raw.Proofs.FullObeysWitnessBase

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.Model

private def witnessSandbox : Sandbox.SandboxOpsM (StateM WitnessWorld) RawFd where
  landlockCreateRuleset attr? flags :=
    pure (.error (match attr? with
      | none => if flags == 0 then Errno.EINVAL else Errno.ENOSYS
      | some _ => if flags != 0 then Errno.EINVAL else Errno.ENOSYS))
  landlockAddRule _ _ := pure (.error Errno.ENOSYS)
  landlockRestrictSelf _ := pure (.error Errno.ENOSYS)
  seccomp op flags filterBytes :=
    pure (.error (match op with
      | .getActionAvail _ => if flags.toBits != 0 then Errno.EINVAL else Errno.ENOSYS
      | .setModeFilter =>
        if !Sandbox.isValidSeccompFilterByteLen filterBytes.data.size ||
           !Sandbox.hasSafeSeccompRetBytes filterBytes then Errno.EINVAL
        else Errno.ENOSYS))
  prctl _ := pure (.error Errno.EINVAL)
  setrlimit _ _ _ := pure (.error Errno.EINVAL)
  memfdCreate name _ :=
    pure (.error (if hasEmbeddedNul name || name.data.size > Sandbox.MFD_NAME_MAX then
      Errno.EINVAL else Errno.ENOSYS))

private theorem sandbox_healthy_of_core (req : Sandbox.SandboxReq) (e : Errno)
    (hCrit : Errno.isCriticalOsErrno e = false) (hEintr : (e == Errno.EINTR) = false)
    (hCore : Sandbox.allowedStepCore (Sandbox.HealthyEnv.initial 0).state req (.err e) =
      some (Sandbox.HealthyEnv.initial 0).state) :
    Sandbox.healthyStep (Sandbox.HealthyEnv.initial 0) req (.err e) =
      some (Sandbox.HealthyEnv.initial 0) := by
  have hWf : (!(Sandbox.HealthyEnv.initial 0).wf) = false := by decide
  have hSec : (Sandbox.HealthyEnv.initial 0).state.seccompMayIntercept = false := rfl
  unfold Sandbox.healthyStep Sandbox.allowedStep Sandbox.isCriticalFault Sandbox.isEintrOutcome
  simp only [hWf, hCrit, hSec, hCore, hEintr, Bool.and_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte]

private theorem witnessSandbox_healthy (w : WitnessWorld) (sreq : RawFdSandboxReq) :
    let (out, w') := (execRawFdSandboxReq witnessSandbox sreq).run w
    w' = w ∧
    ∃ mo, RawFdSandboxOut.MatchesModel out mo ∧
      Sandbox.healthyStep (Sandbox.HealthyEnv.initial 0)
        (mapRawFdSandboxReq sreq) mo = some (Sandbox.HealthyEnv.initial 0) := by
  have hLlEv : (!Sandbox.hasLandlockEvidence (Sandbox.HealthyEnv.initial 0).state) = true := by decide
  have hScEv : (!Sandbox.hasSeccompEvidence (Sandbox.HealthyEnv.initial 0).state) = true := by decide
  have hMfEv : (!Sandbox.hasMemfdEvidence (Sandbox.HealthyEnv.initial 0).state) = true := by decide
  have hNeF1 : (Errno.EINVAL == Errno.EFAULT) = false := by decide
  have hNeF2 : (Errno.ENOSYS == Errno.EFAULT) = false := by decide
  have hNeAcc : (Errno.ENOSYS == Errno.EACCES) = false := by decide
  cases sreq with
  | landlockCreateRuleset attr? flags =>
    cases attr? with
    | none =>
      cases hF : (flags == 0) <;>
        (dsimp only [execRawFdSandboxReq, witnessSandbox, mapRawFdSandboxReq];
         rw [stateM_map_run, stateM_pure_run];
         simp only [hF, Bool.false_eq_true, ↓reduceIte];
         refine ⟨trivial, .err _, rfl, sandbox_healthy_of_core _ _ (by decide) (by decide) ?_⟩;
         unfold Sandbox.allowedStepCore; dsimp only;
         try simp only [hNeF1, hF, Bool.false_eq_true, ↓reduceIte];
         try simp only [hNeF2, hLlEv, Bool.false_eq_true, ↓reduceIte];
         repeat (first | rfl | split))
    | some attr =>
      cases hF : (flags != 0) <;>
        (dsimp only [execRawFdSandboxReq, witnessSandbox, mapRawFdSandboxReq];
         rw [stateM_map_run, stateM_pure_run];
         simp only [hF, Bool.false_eq_true, ↓reduceIte];
         refine ⟨trivial, .err _, rfl, sandbox_healthy_of_core _ _ (by decide) (by decide) ?_⟩;
         unfold Sandbox.allowedStepCore; dsimp only;
         try simp only [hNeF1, hF, Bool.false_eq_true, ↓reduceIte];
         try simp only [hNeF2, hLlEv, Bool.false_eq_true, ↓reduceIte];
         rfl)
  | seccomp op flags bs =>
    cases op with
    | getActionAvail act =>
      cases hF : (flags.toBits != 0) <;>
        (dsimp only [execRawFdSandboxReq, witnessSandbox, mapRawFdSandboxReq];
         rw [stateM_map_run, stateM_pure_run];
         simp only [hF, Bool.false_eq_true, ↓reduceIte];
         refine ⟨trivial, .err _, rfl, sandbox_healthy_of_core _ _ (by decide) (by decide) ?_⟩;
         unfold Sandbox.allowedStepCore; dsimp only;
         try simp only [hNeF1, hF, Bool.false_eq_true, ↓reduceIte];
         try simp only [hNeF2, hScEv, Bool.false_eq_true, ↓reduceIte];
         repeat (first | rfl | split))
    | setModeFilter =>
      cases hB : (!Sandbox.isValidSeccompFilterByteLen bs.data.size || !Sandbox.hasSafeSeccompRetBytes bs) <;>
        (dsimp only [execRawFdSandboxReq, witnessSandbox, mapRawFdSandboxReq];
         rw [stateM_map_run, stateM_pure_run];
         simp only [hB, Bool.false_eq_true, ↓reduceIte];
         refine ⟨trivial, .err _, rfl, sandbox_healthy_of_core _ _ (by decide) (by decide) ?_⟩;
         unfold Sandbox.allowedStepCore; dsimp only;
         try simp only [hNeF1, hB, Bool.false_eq_true, ↓reduceIte];
         try simp only [hNeF2, hScEv, Bool.false_eq_true, ↓reduceIte];
         repeat (first | rfl | split))
  | memfdCreate nm fl =>
    cases hN : (hasEmbeddedNul nm || decide (nm.data.size > Sandbox.MFD_NAME_MAX))
    · dsimp only [execRawFdSandboxReq, witnessSandbox, mapRawFdSandboxReq]
      rw [stateM_map_run, stateM_pure_run]
      simp only [hN, Bool.false_eq_true, ↓reduceIte]
      refine ⟨trivial, .err _, rfl, sandbox_healthy_of_core _ _ (by decide) (by decide) ?_⟩
      unfold Sandbox.allowedStepCore; dsimp only
      simp only [hNeF2, hN, hMfEv, hNeAcc, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      cases (fl.noexecSeal && fl.exec) <;> rfl
    · dsimp only [execRawFdSandboxReq, witnessSandbox, mapRawFdSandboxReq]
      rw [stateM_map_run, stateM_pure_run]
      simp only [hN, ↓reduceIte]
      refine ⟨trivial, .err _, rfl, sandbox_healthy_of_core _ _ (by decide) (by decide) ?_⟩
      unfold Sandbox.allowedStepCore; dsimp only
      simp only [hNeF1, hN, Bool.false_eq_true, ↓reduceIte]
      rfl

private def witnessTimeRand : TimeRand.TimeRandOpsM (StateM WitnessWorld) where
  clock_gettime
    | .realtime => fun w => (.ok { sec := 0, nsec := 0 }, w)
    | .monotonic => fun w =>
      let m := min w.monoNs TimeRand.MAX_TIMESPEC_NANOS
      (.ok { sec := Int64.ofInt (Int.ofNat (m / TimeRand.NSEC_PER_SEC)),
             nsec := UInt32.ofNat (m % TimeRand.NSEC_PER_SEC) }, w)
  clock_nanosleep clk abstime reqTs w :=
    if !reqTs.isValid then
      (.error Errno.EINVAL, w)
    else
      match clk with
      | .realtime => (.ok (), w)
      | .monotonic =>
        let m := min w.monoNs TimeRand.MAX_TIMESPEC_NANOS
        let reqNs := reqTs.toNanosNat
        let nextMono :=
          if abstime then max m reqNs
          else max m (min TimeRand.MAX_TIMESPEC_NANOS (m + reqNs))
        (.ok (), { w with monoNs := nextMono })
  getrandom len flags w :=
    if flags.isInvalid then
      (.error Errno.EINVAL, w)
    else
      let cap := min len.toNat MAX_READ_BYTES.toNat
      (.ok (ByteArray.mk (List.replicate cap 0).toArray),
       { w with entropyDraws := w.entropyDraws + 1 })

private theorem int64_toInt_ofNat_le {q : Nat} (hq : q ≤ 9223372036854775807) :
    (Int64.ofInt (Int.ofNat q)).toInt = Int.ofNat q := by
  rw [Int64.toInt_ofInt]
  change (if Int.ofNat q % 18446744073709551616 < 9223372036854775808 then
      Int.ofNat q % 18446744073709551616
    else Int.ofNat q % 18446744073709551616 - 18446744073709551616) = Int.ofNat q
  simp only [Int.ofNat_eq_natCast]; omega

private theorem mono_ts_roundtrip (m : Nat) (hm : m ≤ TimeRand.MAX_TIMESPEC_NANOS) :
    let ts : TimeRand.Timespec :=
      { sec := Int64.ofInt (Int.ofNat (m / TimeRand.NSEC_PER_SEC))
        nsec := UInt32.ofNat (m % TimeRand.NSEC_PER_SEC) }
    ts.isValid = true ∧ ts.toNanosNat = m := by
  have hbound : m ≤ 9223372036854775807999999999 := hm
  have hsec := int64_toInt_ofNat_le (q := m / 1000000000) (by omega)
  have hnsec : (UInt32.ofNat (m % 1000000000)).toNat = m % 1000000000 := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_⟩
  · unfold TimeRand.Timespec.isValid TimeRand.NSEC_PER_SEC; dsimp only
    rw [hsec, hnsec]; simp only [Bool.and_eq_true, decide_eq_true_eq, Int.ofNat_eq_natCast]; omega
  · unfold TimeRand.Timespec.toNanosNat TimeRand.NSEC_PER_SEC; dsimp only
    rw [hsec, hnsec]; exact Nat.div_add_mod' m 1000000000

private theorem valid_timespec_le_max (ts : TimeRand.Timespec) (hV : ts.isValid = true) :
    ts.toNanosNat ≤ TimeRand.MAX_TIMESPEC_NANOS := by
  unfold TimeRand.Timespec.isValid TimeRand.NSEC_PER_SEC at hV
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hV
  have hSecLe : ts.sec.toInt ≤ 9223372036854775807 := by
    have := ts.sec.toBitVec.isLt
    change (if 2 * ts.sec.toBitVec.toNat < 18446744073709551616 then (ts.sec.toBitVec.toNat : Int)
      else (ts.sec.toBitVec.toNat : Int) - 18446744073709551616) ≤ 9223372036854775807
    split <;> omega
  unfold TimeRand.Timespec.toNanosNat TimeRand.MAX_TIMESPEC_NANOS TimeRand.MAX_TIMESPEC_SEC TimeRand.NSEC_PER_SEC
  omega

private theorem witnessTimeRand_healthy (w : WitnessWorld) (treq : TimeRand.TimeRandReq) :
    let (out, w') := (TimeRand.execTimeRandReq witnessTimeRand treq).run w
    w'.cell = w.cell ∧
    TimeRand.healthyStep (witnessProjRaw w).timeEnv treq out = some (witnessProjRaw w').timeEnv := by
  cases treq with
  | clock_gettime clk =>
    cases clk with
    | realtime =>
      exact ⟨rfl, rfl⟩
    | monotonic =>
      dsimp only [TimeRand.execTimeRandReq, witnessTimeRand, TimeRand.outcomeOfTimespec,
        Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Id.run]
      refine ⟨rfl, ?_⟩
      have hm : min w.monoNs TimeRand.MAX_TIMESPEC_NANOS ≤ TimeRand.MAX_TIMESPEC_NANOS :=
        Nat.min_le_right _ _
      have ⟨hVal, hTo⟩ := mono_ts_roundtrip (min w.monoNs TimeRand.MAX_TIMESPEC_NANOS) hm
      unfold TimeRand.healthyStep TimeRand.isCriticalFault TimeRand.isEintrOutcome TimeRand.allowedStep TimeRand.allowedStepCore witnessProjRaw witnessTimeEnv TimeRand.HealthyEnv.wf
      dsimp only
      rw [hVal, hTo]
      have hMinIdem : min (min w.monoNs TimeRand.MAX_TIMESPEC_NANOS) TimeRand.MAX_TIMESPEC_NANOS =
          min w.monoNs TimeRand.MAX_TIMESPEC_NANOS := Nat.min_eq_left hm
      have hMaxIdem : max (min w.monoNs TimeRand.MAX_TIMESPEC_NANOS)
          (min w.monoNs TimeRand.MAX_TIMESPEC_NANOS) =
          min w.monoNs TimeRand.MAX_TIMESPEC_NANOS := Nat.max_self _
      rw [hMinIdem, hMaxIdem]
      simp
  | clock_nanosleep clk abstime reqTs =>
    dsimp only [TimeRand.execTimeRandReq, witnessTimeRand,
      Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Id.run]
    cases hVal : reqTs.isValid
    · simp only [Bool.not_false, ↓reduceIte, TimeRand.outcomeOfUnit]
      refine ⟨trivial, ?_⟩
      unfold TimeRand.healthyStep TimeRand.isCriticalFault TimeRand.isEintrOutcome TimeRand.allowedStep TimeRand.allowedStepCore witnessProjRaw witnessTimeEnv TimeRand.HealthyEnv.wf
      simp only [hVal, Bool.not_false, ↓reduceIte]; rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases clk with
      | realtime =>
        dsimp only [TimeRand.outcomeOfUnit]
        refine ⟨rfl, ?_⟩
        unfold TimeRand.healthyStep TimeRand.isCriticalFault TimeRand.isEintrOutcome TimeRand.allowedStep TimeRand.allowedStepCore witnessProjRaw witnessTimeEnv TimeRand.HealthyEnv.wf
        simp [hVal]
      | monotonic =>
        dsimp only [TimeRand.outcomeOfUnit]
        refine ⟨rfl, ?_⟩
        have hm : min w.monoNs TimeRand.MAX_TIMESPEC_NANOS ≤ TimeRand.MAX_TIMESPEC_NANOS :=
          Nat.min_le_right _ _
        have hReqLe := valid_timespec_le_max reqTs hVal
        have hNextLe : (if abstime then max (min w.monoNs TimeRand.MAX_TIMESPEC_NANOS) reqTs.toNanosNat
            else max (min w.monoNs TimeRand.MAX_TIMESPEC_NANOS)
              (min TimeRand.MAX_TIMESPEC_NANOS (min w.monoNs TimeRand.MAX_TIMESPEC_NANOS + reqTs.toNanosNat))) ≤
            TimeRand.MAX_TIMESPEC_NANOS := by
          cases abstime <;> simp [Nat.max_le, hm, hReqLe, Nat.min_le_left]
        unfold TimeRand.healthyStep TimeRand.isCriticalFault TimeRand.isEintrOutcome TimeRand.allowedStep TimeRand.allowedStepCore witnessProjRaw witnessTimeEnv TimeRand.HealthyEnv.wf
        simp [hVal, Nat.min_eq_left hNextLe]
  | getrandom len flags =>
    dsimp only [TimeRand.execTimeRandReq, witnessTimeRand,
      Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Id.run]
    cases hInv : flags.isInvalid
    · simp only [Bool.false_eq_true, ↓reduceIte, TimeRand.outcomeOfBytes]
      refine ⟨trivial, ?_⟩
      have hVLen : TimeRand.validGetrandomResultLen len (min len.toNat MAX_READ_BYTES.toNat) = true := by
        unfold TimeRand.validGetrandomResultLen TimeRand.GETRANDOM_EXACT_MAX
        dsimp only
        split
        · simp_all
        · split
          · simp
          · rw [Bool.and_eq_true]; exact ⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩
      unfold TimeRand.healthyStep TimeRand.isCriticalFault TimeRand.isEintrOutcome TimeRand.allowedStep TimeRand.allowedStepCore witnessProjRaw witnessTimeEnv TimeRand.HealthyEnv.wf
      dsimp only
      simp [hInv, hVLen]
    · simp only [↓reduceIte, TimeRand.outcomeOfBytes]
      refine ⟨trivial, ?_⟩
      unfold TimeRand.healthyStep TimeRand.isCriticalFault TimeRand.isEintrOutcome TimeRand.allowedStep TimeRand.allowedStepCore witnessProjRaw witnessTimeEnv TimeRand.HealthyEnv.wf
      simp only [hInv, ↓reduceIte]; rfl

private def witnessPasswd : Passwd.PasswdOpsM (StateM WitnessWorld) where
  getpwuid _ := pure (.error Errno.EMFILE)
  getpwnam name :=
    pure (.error (if !Passwd.validPasswdName name then Errno.EINVAL
      else if name.size > Passwd.MAX_PASSWD_NAME_BYTES then Errno.ENAMETOOLONG
      else Errno.EMFILE))

private theorem witnessPasswd_healthy (w : WitnessWorld) (preq : Passwd.PasswdReq) :
    let (out, w') := (Passwd.execPasswdReq witnessPasswd preq).run w
    w' = w ∧
    Passwd.healthyStep (Passwd.HealthyEnv.initial 0 true) preq out =
      some (Passwd.HealthyEnv.initial 0 true) := by
  have hWf : (!(Passwd.HealthyEnv.initial 0 true).wf) = false := by decide
  cases preq with
  | getpwuid uid =>
    dsimp only [Passwd.execPasswdReq, witnessPasswd]
    rw [stateM_bind_run, stateM_pure_run, stateM_pure_run]
    refine ⟨rfl, ?_⟩
    unfold Passwd.outcomeOfEntryOpt Passwd.healthyStep Passwd.isCriticalFault Passwd.isEintrOutcome
      Passwd.allowedStep Passwd.allowedStepCore Passwd.lookupPasswdByUid
    dsimp only; rw [hWf]; rfl
  | getpwnam name =>
    dsimp only [Passwd.execPasswdReq, witnessPasswd]
    rw [stateM_bind_run, stateM_pure_run, stateM_pure_run]
    refine ⟨rfl, ?_⟩
    cases hV : (!Passwd.validPasswdName name)
    · by_cases hL : name.size > Passwd.MAX_PASSWD_NAME_BYTES
      · unfold Passwd.outcomeOfEntryOpt Passwd.healthyStep Passwd.isCriticalFault
          Passwd.isEintrOutcome Passwd.allowedStep Passwd.allowedStepCore
        dsimp only; rw [hWf]; simp only [hV, hL, Bool.false_eq_true, ↓reduceIte]; rfl
      · unfold Passwd.outcomeOfEntryOpt Passwd.healthyStep Passwd.isCriticalFault
          Passwd.isEintrOutcome Passwd.allowedStep Passwd.allowedStepCore Passwd.lookupPasswdByName
        dsimp only; rw [hWf]; simp only [hV, hL, Bool.false_eq_true, ↓reduceIte]; rfl
    · unfold Passwd.outcomeOfEntryOpt Passwd.healthyStep Passwd.isCriticalFault
        Passwd.isEintrOutcome Passwd.allowedStep Passwd.allowedStepCore
      dsimp only; rw [hWf]; simp only [hV, ↓reduceIte]; rfl

private def pfInvalidErr : PostFork.PostForkError :=
  { kind := .invalidInput, errno := none, childFailure := none, message := "invalid" }

private def pfSysErr : PostFork.PostForkError :=
  { kind := .sysError, errno := some Errno.EAGAIN, childFailure := none, message := "again" }

private def witnessPostFork : PostFork.PostForkOpsM (StateM WitnessWorld) RawFd where
  spawn sp :=
    pure (.error (if PostFork.Model.validateSpec (mapPostForkChildSpec dummyHid sp) then pfSysErr else pfInvalidErr))
  spawnWithBarrier sp :=
    pure (.error (if PostFork.Model.validateSpec (mapPostForkChildSpec dummyHid sp) then pfSysErr else pfInvalidErr))
  releaseBarrier p := pure (.ok { pid := p.pid, pgid := p.pgid })
  abortBarrier _ := pure (.error pfSysErr)

private theorem witnessPostFork_allowed (w : WitnessWorld) (pfreq : RawFdPostForkReq) :
    let (out, w') := (execRawFdPostForkReq witnessPostFork pfreq).run w
    w' = w ∧
    ∃ mo, RawFdPostForkOut.MatchesModel out mo ∧
      PostFork.Model.allowedPkgStep {} (mapRawFdPostForkReq dummyHid pfreq) mo {} := by
  have hWf0 : PostFork.Model.rawStepWf {} = true := by decide
  have hSysOk : PostFork.Model.validSysErrProp pfSysErr :=
    ⟨rfl, rfl, by decide, Errno.EAGAIN, rfl, ⟨by decide, by decide⟩⟩
  have hInvOk : PostFork.Model.validInvalidErrProp pfInvalidErr :=
    ⟨rfl, rfl, rfl, by decide⟩
  cases pfreq with
  | spawn sp =>
    dsimp only [execRawFdPostForkReq, witnessPostFork, mapRawFdPostForkReq]
    rw [stateM_map_run, stateM_pure_run]
    cases hV : PostFork.Model.validateSpec (mapPostForkChildSpec dummyHid sp)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨trivial, .spawned (.error pfInvalidErr), rfl, hWf0, hWf0, Nat.le_refl _, ?_⟩
      dsimp only; rw [hV]; exact ⟨rfl, hInvOk⟩
    · simp only [↓reduceIte]
      refine ⟨trivial, .spawned (.error pfSysErr), rfl, hWf0, hWf0, Nat.le_refl _, ?_⟩
      dsimp only; rw [hV]; exact Or.inl hSysOk
  | spawnWithBarrier sp =>
    dsimp only [execRawFdPostForkReq, witnessPostFork, mapRawFdPostForkReq]
    rw [stateM_map_run, stateM_pure_run]
    cases hV : PostFork.Model.validateSpec (mapPostForkChildSpec dummyHid sp)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨trivial, .pending (.error pfInvalidErr), rfl, hWf0, hWf0, Nat.le_refl _, ?_⟩
      dsimp only; rw [hV]; exact ⟨rfl, hInvOk⟩
    · simp only [↓reduceIte]
      refine ⟨trivial, .pending (.error pfSysErr), rfl, hWf0, hWf0, Nat.le_refl _, ?_⟩
      dsimp only; rw [hV]; exact hSysOk
  | releaseBarrier p =>
    dsimp only [execRawFdPostForkReq, witnessPostFork, mapRawFdPostForkReq]
    rw [stateM_map_run, stateM_pure_run]
    exact ⟨rfl, .spawned (.ok { pid := p.pid, pgid := p.pgid }), rfl,
      hWf0, hWf0, Nat.le_refl _, ⟨rfl, rfl⟩⟩
  | abortBarrier _ =>
    dsimp only [execRawFdPostForkReq, witnessPostFork, mapRawFdPostForkReq]
    rw [stateM_map_run, stateM_pure_run]
    exact ⟨rfl, .aborted (.error pfSysErr), rfl, hWf0, hWf0, Nat.le_refl _, hSysOk⟩

private def witnessEnvVars : EnvVars.Raw.RawEnvVarsOpsM (StateM WitnessWorld) where
  mapRawError := fun _ => { kind := .ioError, message := "err" }
  getEnv key := pure (EnvVars.Raw.Model.rawGetEnvModel {} key)
  listEnv := pure (EnvVars.Raw.Model.rawListEnvModel {})

private theorem witnessProc_healthy (w : WitnessWorld) (preq : RawFdProcReq) :
    let (out, w') := (execRawFdProcReq witnessProc preq).run w
    w' = w ∧
    ∃ mo, RawFdProcOut.MatchesModel out mo ∧
      LinuxSyscall.Process.healthyStep LinuxSyscall.Process.HealthyEnv.initial
        (mapRawFdProcReq dummyHid preq) mo = some LinuxSyscall.Process.HealthyEnv.initial := by
  have hSpcCrit : Errno.isCriticalOsErrno Errno.ENOSPC = false := by decide
  have hSpcEintr : (Errno.ENOSPC == Errno.EINTR) = false := by decide
  have hSpcFd : LinuxSyscall.Process.isKernelFdAllocTransient Errno.ENOSPC = true := by decide
  have hSpcNonFd : LinuxSyscall.Process.isKernelNonFdTransient Errno.ENOSPC = true := by decide
  have hWf : (!LinuxSyscall.Process.HealthyEnv.initial.wf) = false := by decide
  cases preq with
  | getpid =>
    exact ⟨rfl, .u32 (LinuxSyscall.Process.effectiveSelfPid LinuxSyscall.Process.ProcessSysState.initial), rfl, rfl⟩
  | getuid =>
    exact ⟨rfl, .u32 LinuxSyscall.Process.ProcessSysState.initial.selfUid, rfl, rfl⟩
  | pidfdSendSignal fd sig fl =>
    cases hR : sig.isNptlReserved
    · dsimp only [execRawFdProcReq, witnessProc, mapRawFdProcReq, dummyHid]
      rw [stateM_map_run, stateM_pure_run]
      refine ⟨rfl, .err Errno.EBADF, ?_, ?_⟩
      · simp [RawFdProcOut.MatchesModel, hR]
      · unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.allowedStep
          LinuxSyscall.Process.validateReqBeforeKernel
        dsimp only; simp only [hR, Bool.false_eq_true, ↓reduceIte]; rfl
    · dsimp only [execRawFdProcReq, witnessProc, mapRawFdProcReq, dummyHid]
      rw [stateM_map_run, stateM_pure_run]
      refine ⟨rfl, .err Errno.EINVAL, ?_, ?_⟩
      · simp [RawFdProcOut.MatchesModel, hR]
      · unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.allowedStep
          LinuxSyscall.Process.validateReqBeforeKernel
        dsimp only; simp only [hR, ↓reduceIte]; rfl
  | pipe2 fl =>
    refine ⟨rfl, .err Errno.ENOSPC, rfl, ?_⟩
    unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.isCriticalFault
      LinuxSyscall.Process.isEintrOutcome LinuxSyscall.Process.allowedStep
      LinuxSyscall.Process.validateReqBeforeKernel mapRawFdProcReq
    dsimp only; simp only [hWf, hSpcCrit, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    cases (!fl.isValid)
    · cases (fl.notificationPipe && !LinuxSyscall.Process.HealthyEnv.initial.state.watchQueueSupported) <;>
        simp [hSpcFd, hSpcEintr]
    · simp [hSpcNonFd, hSpcEintr]
  | waitpid pid fl =>
    refine ⟨rfl, .err Errno.ENOSPC, rfl, ?_⟩
    unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.isCriticalFault
      LinuxSyscall.Process.isEintrOutcome LinuxSyscall.Process.allowedStep
      LinuxSyscall.Process.validateReqBeforeKernel LinuxSyscall.Process.allowedStepWaitpid mapRawFdProcReq
    dsimp only; simp only [hWf, hSpcCrit, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    have hEmp : (LinuxSyscall.Process.matchingUnreapedChildren
        LinuxSyscall.Process.HealthyEnv.initial.state pid fl).isEmpty = true := rfl
    cases (!fl.isValid)
    · cases (pid == Int32.minValue)
      · rw [hEmp]; simp [hSpcNonFd, hSpcEintr]
      · simp [hSpcNonFd, hSpcEintr]
    · simp [hSpcNonFd, hSpcEintr]
  | pidfdOpen pid fl =>
    refine ⟨rfl, .err Errno.ENOSPC, rfl, ?_⟩
    unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.isCriticalFault
      LinuxSyscall.Process.isEintrOutcome LinuxSyscall.Process.allowedStep
      LinuxSyscall.Process.validateReqBeforeKernel LinuxSyscall.Process.allowedStepPidfdOpen mapRawFdProcReq
    dsimp only; simp only [hWf, hSpcCrit, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    have hSec : LinuxSyscall.Process.HealthyEnv.initial.state.ambientSeccomp = false := rfl
    cases hChk : LinuxSyscall.Process.checkPidfdOpenTarget LinuxSyscall.Process.HealthyEnv.initial.state pid fl with
    | ok _ => dsimp only; rw [hSec]; simp [hSpcFd, hSpcEintr]
    | error expErr =>
      have hNe := checkPidfdOpen_err_ne_enospc _ _ _ _ hChk
      have hNe1 : (Errno.ENOSPC == Errno.EINVAL) = false := by decide
      have hNe2 : (Errno.ENOSPC == Errno.ESRCH) = false := by decide
      have hNe3 : (Errno.ENOSPC == Errno.ENOENT) = false := by decide
      dsimp only
      simp only [hNe, hSec, hNe1, hNe2, hNe3, Bool.false_and, Bool.and_false, Bool.or_false,
        Bool.false_eq_true, ↓reduceIte]
      have hMay : ∀ b : Bool,
          (if b then LinuxSyscall.Process.isKernelFdAllocTransient Errno.ENOSPC
           else LinuxSyscall.Process.isKernelNonFdTransient Errno.ENOSPC) = true := by
        intro b; cases b <;> assumption
      simp only [hMay, ↓reduceIte, hSpcEintr, Bool.false_eq_true]
  | kill tgt sig =>
    cases hR : sig.isNptlReserved
    · dsimp only [execRawFdProcReq, witnessProc, mapRawFdProcReq]
      rw [stateM_map_run, stateM_pure_run]
      refine ⟨rfl, .err Errno.ENOSPC, ?_, ?_⟩
      · simp [RawFdProcOut.MatchesModel, hR]
      · unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.isCriticalFault
          LinuxSyscall.Process.isEintrOutcome LinuxSyscall.Process.allowedStep
          LinuxSyscall.Process.validateReqBeforeKernel LinuxSyscall.Process.allowedStepKill
        dsimp only; simp only [hWf, hSpcCrit, hR, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
        have hSec : LinuxSyscall.Process.HealthyEnv.initial.state.ambientSeccomp = false := rfl
        cases hEv : LinuxSyscall.Process.evalKill LinuxSyscall.Process.HealthyEnv.initial.state tgt sig with
        | ok _ => dsimp only; simp [hSec, hSpcNonFd, hSpcEintr]
        | error expErr =>
          have hNe := evalKillInit_err_ne_enospc _ _ _ hEv
          dsimp only; simp [hNe, hSec, hSpcNonFd, hSpcEintr]
    · dsimp only [execRawFdProcReq, witnessProc, mapRawFdProcReq]
      rw [stateM_map_run, stateM_pure_run]
      refine ⟨rfl, .err Errno.EINVAL, ?_, ?_⟩
      · simp [RawFdProcOut.MatchesModel, hR]
      · unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.allowedStep
          LinuxSyscall.Process.validateReqBeforeKernel
        dsimp only; simp only [hR, ↓reduceIte]; rfl

private def witnessSys : FullSysOpsM (StateM WitnessWorld) where
  files := witnessFiles
  net := witnessNet
  poll := witnessPoll
  proc := witnessProc
  sandbox := witnessSandbox
  timeRand := witnessTimeRand
  passwd := witnessPasswd
  postFork := witnessPostFork
  envVars := witnessEnvVars

private theorem witnessSys_obeys :
    Core.ObeysStep witnessProjRaw fullWorldWf (execFullRawStep witnessSys) allowedFullRawStep ∧
    (∀ w req, fullWorldWf (witnessProjRaw w) = true →
      witnessProjCell ((execFullRawStep witnessSys req).run w).2 = witnessProjCell w) := by
  constructor
  · intro w req _
    cases req with
    | timeRand r =>
      have hT := witnessTimeRand_healthy w r
      dsimp only [execFullRawStep, witnessSys]
      rw [stateM_map_run]
      exact ⟨witnessProjRaw_wf _, hT.2⟩
    | passwd r =>
      have ⟨hP1, hP2⟩ := witnessPasswd_healthy w r
      have hEq : ((Passwd.execPasswdReq witnessPasswd r).run w).2 = w := hP1
      dsimp only [execFullRawStep, witnessSys]; rw [stateM_map_run, hEq]
      exact ⟨witnessProjRaw_wf _, hP2⟩
    | envGet k =>
      dsimp only [execFullRawStep, witnessSys, witnessEnvVars]
      rw [stateM_map_run, stateM_pure_run]
      exact ⟨witnessProjRaw_wf _, rfl, rfl⟩
    | files freq =>
      have hDir : ∀ r, (∀ h ∈ Files.candidateDirFds (mapRawFdFilesReq dummyHid r), h = 100) := by
        intro r h hh
        cases r with
        | openat d _ _ _ | fstatat d _ _ | faccessat d _ _ _
        | mkdirat d _ _ | unlinkat d _ _ | readlinkat d _ _ =>
          cases d <;> simp [mapRawFdFilesReq, Files.candidateDirFds, dummyHid] at hh
          exact hh
        | _ => simp [mapRawFdFilesReq, Files.candidateDirFds] at hh
      dsimp only [execFullRawStep, witnessSys]
      rw [stateM_map_run]
      cases freq with
      | close _ | read _ _ | write _ _ | fcntl _ _ | reopenReadOnly _ =>
        dsimp only [execRawFdFilesReq, witnessFiles]; rw [stateM_map_run, stateM_pure_run]
        exact ⟨witnessProjRaw_wf _, dummyHid, .err Errno.EBADF, rfl, rfl⟩
      | openat d p fl m =>
        dsimp only [execRawFdFilesReq, witnessFiles]; rw [stateM_map_run, stateM_pure_run]
        exact ⟨witnessProjRaw_wf _, dummyHid, .err _, rfl,
          sampleFilesErrno_at_healthy _ trivial (hDir (.openat d p fl m))⟩
      | fstatat d p fl =>
        dsimp only [execRawFdFilesReq, witnessFiles]; rw [stateM_map_run, stateM_pure_run]
        exact ⟨witnessProjRaw_wf _, dummyHid, .err _, rfl,
          sampleFilesErrno_at_healthy _ trivial (hDir (.fstatat d p fl))⟩
      | faccessat d p mk fl =>
        dsimp only [execRawFdFilesReq, witnessFiles]; rw [stateM_map_run, stateM_pure_run]
        exact ⟨witnessProjRaw_wf _, dummyHid, .err _, rfl,
          sampleFilesErrno_at_healthy _ trivial (hDir (.faccessat d p mk fl))⟩
      | mkdirat d p m =>
        dsimp only [execRawFdFilesReq, witnessFiles]; rw [stateM_map_run, stateM_pure_run]
        exact ⟨witnessProjRaw_wf _, dummyHid, .err _, rfl,
          sampleFilesErrno_at_healthy _ trivial (hDir (.mkdirat d p m))⟩
      | unlinkat d p rm =>
        dsimp only [execRawFdFilesReq, witnessFiles]; rw [stateM_map_run, stateM_pure_run]
        exact ⟨witnessProjRaw_wf _, dummyHid, .err _, rfl,
          sampleFilesErrno_at_healthy _ trivial (hDir (.unlinkat d p rm))⟩
      | readlinkat d p c =>
        dsimp only [execRawFdFilesReq, witnessFiles]; rw [stateM_map_run, stateM_pure_run]
        exact ⟨witnessProjRaw_wf _, dummyHid, .err _, rfl,
          sampleFilesErrno_at_healthy _ trivial (hDir (.readlinkat d p c))⟩
    | net nreq =>
      have hN := sampleNetErrno_healthy nreq
      dsimp only [execFullRawStep, witnessSys]; rw [stateM_map_run]
      cases nreq <;>
        (dsimp only [execRawFdNetReq, witnessNet]; rw [stateM_map_run, stateM_pure_run];
         exact ⟨witnessProjRaw_wf _, dummyHid, .err _, rfl, hN⟩)
    | pollPpoll fds to? =>
      dsimp only [execFullRawStep, witnessSys, witnessPoll]; rw [stateM_map_run, stateM_pure_run]
      exact ⟨witnessProjRaw_wf _, dummyHid, samplePollErrno_healthy fds to?⟩
    | proc preq =>
      have ⟨hPr1, mo, hM, hSt⟩ := witnessProc_healthy w preq
      have hEq : ((execRawFdProcReq witnessProc preq).run w).2 = w := hPr1
      dsimp only [execFullRawStep, witnessSys]; rw [stateM_map_run, hEq]
      exact ⟨witnessProjRaw_wf _, dummyHid, mo, hM, hSt⟩
    | sandbox sreq =>
      have ⟨hSb1, mo, hM, hSt⟩ := witnessSandbox_healthy w sreq
      have hEq : ((execRawFdSandboxReq witnessSandbox sreq).run w).2 = w := hSb1
      dsimp only [execFullRawStep, witnessSys]; rw [stateM_map_run, hEq]
      exact ⟨witnessProjRaw_wf _, mo, hM, hSt⟩
    | postFork pfreq =>
      have ⟨hPf1, mo, hM, hSt⟩ := witnessPostFork_allowed w pfreq
      have hEq : ((execRawFdPostForkReq witnessPostFork pfreq).run w).2 = w := hPf1
      dsimp only [execFullRawStep, witnessSys]; rw [stateM_map_run, hEq]
      exact ⟨witnessProjRaw_wf _, dummyHid, mo, hM, hSt⟩
  · intro w req _
    cases req with
    | timeRand r =>
      dsimp only [execFullRawStep, witnessSys]; rw [stateM_map_run]
      exact (witnessTimeRand_healthy w r).1
    | passwd r =>
      dsimp only [execFullRawStep, witnessSys]; rw [stateM_map_run]
      exact congrArg witnessProjCell (witnessPasswd_healthy w r).1
    | envGet _ =>
      dsimp only [execFullRawStep, witnessSys, witnessEnvVars]; rw [stateM_map_run, stateM_pure_run]
    | files freq =>
      dsimp only [execFullRawStep, witnessSys]; rw [stateM_map_run]
      cases freq <;> (dsimp only [execRawFdFilesReq, witnessFiles]; rw [stateM_map_run, stateM_pure_run])
    | net nreq =>
      dsimp only [execFullRawStep, witnessSys]; rw [stateM_map_run]
      cases nreq <;> (dsimp only [execRawFdNetReq, witnessNet]; rw [stateM_map_run, stateM_pure_run])
    | pollPpoll _ _ =>
      dsimp only [execFullRawStep, witnessSys, witnessPoll]; rw [stateM_map_run, stateM_pure_run]
    | proc preq =>
      dsimp only [execFullRawStep, witnessSys]; rw [stateM_map_run]
      exact congrArg witnessProjCell (witnessProc_healthy w preq).1
    | sandbox sreq =>
      dsimp only [execFullRawStep, witnessSys]; rw [stateM_map_run]
      exact congrArg witnessProjCell (witnessSandbox_healthy w sreq).1
    | postFork pfreq =>
      dsimp only [execFullRawStep, witnessSys]; rw [stateM_map_run]
      exact congrArg witnessProjCell (witnessPostFork_allowed w pfreq).1

/-- Non-vacuity witness showing all capability, frame-disjointness, `Core.ObeysConcFrame`,
    `Core.ObeysStateCell`, and initial `rawHostWorldWf` hypotheses of `obeys_model` are
    simultaneously inhabited for every schedule `sched : Nat → Bool`. -/
theorem obeys_model_nonvacuous (sched : Nat → Bool) :
    ∃ (W : Type) (projRaw : W → Model.HealthyRawSysWorld)
      (raw : Model.FullSysOpsM (StateM W)) (conc : Core.ConcOpsM (StateM W))
      (projCell : W → HostCellState conc.Ref conc.TaskHandle)
      (cell : Core.StateCellM (StateM W) (HostCellState conc.Ref conc.TaskHandle)),
      Core.ObeysStep projRaw Model.fullWorldWf (Model.execFullRawStep raw) Model.allowedFullRawStep ∧
      (∀ w req, Model.fullWorldWf (projRaw w) = true →
        projCell ((Model.execFullRawStep raw req).run w).2 = projCell w) ∧
      Core.ObeysConcFrame (fun w => Model.fullWorldWf (projRaw w) = true)
        (fun w₁ w₂ => projCell w₂ = projCell w₁) conc ∧
      Core.ObeysStateCell projRaw projCell cell ∧
      ∃ w₀ : W, Model.rawHostWorldWf
        (Model.mapFullToRawWorld (projRaw w₀) (Model.cellToRawTable (projCell w₀))) = true := by
  refine ⟨WitnessWorld, witnessProjRaw, witnessSys, witnessConc sched,
    witnessProjCell, witnessCell, witnessSys_obeys.1, witnessSys_obeys.2,
    witnessConc_obeys sched, witnessCell_obeys, ({} : WitnessWorld), ?_⟩
  have hSysWf : (witnessProjRaw {}).wf = true := witnessProjRaw_wf {}
  unfold mapFullToRawWorld
  rw [hSysWf]; simp only [↓reduceIte]
  unfold rawHostWorldWf cellToRawTable cellTableToModel witnessProjCell
  rfl

end LeanSwe.ProcessSandbox.Raw.Proofs
