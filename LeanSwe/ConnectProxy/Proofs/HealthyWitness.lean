import LeanSwe.ConnectProxy.Proofs.HealthyWitnessPollDns

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Internal.SysBridge
open LeanSwe.ConnectProxy.Internal.HealthySys

private theorem tr_entListAux_len (drawIdx rem pos : Nat) (acc : List UInt8) :
    (TimeRand.deterministicEntropyListAux drawIdx rem pos acc).length = acc.length + rem := by
  induction rem generalizing pos acc with
  | zero => simp [TimeRand.deterministicEntropyListAux]
  | succ rem ih => simp only [TimeRand.deterministicEntropyListAux, ih, List.length_cons]; omega

private theorem tr_entBytesAux_sz (drawIdx rem pos : Nat) (acc : ByteArray) :
    (TimeRand.deterministicEntropyBytesAux drawIdx rem pos acc).size = acc.size + rem := by
  induction rem generalizing pos acc with
  | zero => simp [TimeRand.deterministicEntropyBytesAux]
  | succ rem ih => simp only [TimeRand.deterministicEntropyBytesAux, ih, ByteArray.size_push]; omega

private theorem tr_entBytes_sz (drawIdx len : Nat) :
    (TimeRand.deterministicEntropyBytes drawIdx len).size = len := by
  unfold TimeRand.deterministicEntropyBytes
  by_cases h : len ≤ 256
  · simp [h, ByteArray.size, TimeRand.deterministicEntropyList, tr_entListAux_len]
  · simp only [h, ↓reduceIte, tr_entBytesAux_sz]
    have h0 : (ByteArray.emptyWithCapacity len).size = 0 := rfl
    omega

private theorem tr_validGrndLen (len : UInt32) :
    TimeRand.validGetrandomResultLen len (min len.toNat MAX_READ_BYTES.toNat) = true := by
  unfold TimeRand.validGetrandomResultLen
  by_cases h0 : min len.toNat MAX_READ_BYTES.toNat = 0
  · simp [h0]
  · have hgt : 1 ≤ min len.toNat MAX_READ_BYTES.toNat := by omega
    by_cases hle : min len.toNat MAX_READ_BYTES.toNat ≤ TimeRand.GETRANDOM_EXACT_MAX <;> simp [h0, hle, hgt]

private theorem tr_healthyStep_of_core {env : TimeRand.HealthyEnv} {req : TimeRand.TimeRandReq}
    {out : TimeRand.TimeRandOutcome} {s' : TimeRand.TimeRandState}
    (hWf : env.wf = true) (hCore : TimeRand.allowedStepCore env.state req out = some s')
    (hNoCrit : TimeRand.isCriticalFault out = false) (hNoEi : TimeRand.isEintrOutcome out = false) :
    TimeRand.healthyStep env req out = some { env with state := s' } := by
  have hSec : env.state.ambientSeccomp = false := by
    unfold TimeRand.HealthyEnv.wf at hWf
    cases h : env.state.ambientSeccomp <;> simp_all
  unfold TimeRand.healthyStep TimeRand.allowedStep
  simp [hWf, hSec, hCore, hNoCrit, hNoEi]

private def maxMonoTimespec : TimeRand.Timespec :=
  { sec := Int64.ofInt (Int.ofNat TimeRand.MAX_TIMESPEC_SEC)
    nsec := UInt32.ofNat (TimeRand.NSEC_PER_SEC - 1) }

private def fallbackClockGettime (clk : TimeRand.ClockId) (env : TimeRand.HealthyEnv) :
    Except Errno TimeRand.Timespec × TimeRand.HealthyEnv :=
  match clk with
  | .realtime => (.ok { sec := 0, nsec := 0 }, env)
  | .monotonic =>
    (.ok maxMonoTimespec,
      { env with state := { env.state with monoLowerBoundNs := max env.state.monoLowerBoundNs maxMonoTimespec.toNanosNat } })

private def fallbackClockNanosleep (clk : TimeRand.ClockId) (abs : Bool) (reqTs : TimeRand.Timespec)
    (env : TimeRand.HealthyEnv) : Except Errno Unit × TimeRand.HealthyEnv :=
  if !reqTs.isValid then
    (.error Errno.EINVAL, env)
  else
    match clk with
    | .realtime => (.ok (), env)
    | .monotonic =>
      let nextMono :=
        if abs then max env.state.monoLowerBoundNs reqTs.toNanosNat
        else max env.state.monoLowerBoundNs (min TimeRand.MAX_TIMESPEC_NANOS (env.state.monoLowerBoundNs + reqTs.toNanosNat))
      (.ok (), { env with state := { env.state with monoLowerBoundNs := nextMono } })

private def fallbackGetrandom (len : UInt32) (flags : TimeRand.GrndFlags) (env : TimeRand.HealthyEnv) :
    Except Errno ByteArray × TimeRand.HealthyEnv :=
  if flags.isInvalid then
    (.error Errno.EINVAL, env)
  else
    let bs := TimeRand.deterministicEntropyBytes env.state.entropyDraws (min len.toNat MAX_READ_BYTES.toNat)
    (.ok bs,
      { env with state :=
          { env.state with
            crngReady := env.state.crngReady || !flags.insecure
            entropyDraws := env.state.entropyDraws + 1 } })

private theorem fallbackClockGettime_healthy (clk : TimeRand.ClockId) (env : TimeRand.HealthyEnv)
    (hWf : env.wf = true) :
    TimeRand.healthyStep env (.clock_gettime clk)
      (TimeRand.outcomeOfTimespec (fallbackClockGettime clk env).1) = some (fallbackClockGettime clk env).2 ∧
    (fallbackClockGettime clk env).2.wf = true := by
  cases clk with
  | realtime =>
    refine ⟨?_, hWf⟩
    dsimp only [fallbackClockGettime]
    apply tr_healthyStep_of_core hWf _ rfl rfl
    have hVal : ({ sec := 0, nsec := 0 } : TimeRand.Timespec).hasValidNsec = true := by decide
    simp [TimeRand.outcomeOfTimespec, TimeRand.allowedStepCore, hVal]
  | monotonic =>
    refine ⟨?_, hWf⟩
    dsimp only [fallbackClockGettime]
    apply tr_healthyStep_of_core hWf _ rfl rfl
    have hVal : maxMonoTimespec.isValid = true := by decide
    have hNs : maxMonoTimespec.toNanosNat = TimeRand.MAX_TIMESPEC_NANOS := by decide
    have hLe : min env.state.monoLowerBoundNs TimeRand.MAX_TIMESPEC_NANOS ≤ maxMonoTimespec.toNanosNat := by
      rw [hNs]; exact Nat.min_le_right _ _
    have hCond : (maxMonoTimespec.isValid &&
        decide (min env.state.monoLowerBoundNs TimeRand.MAX_TIMESPEC_NANOS ≤ maxMonoTimespec.toNanosNat)) = true := by
      rw [hVal, decide_eq_true hLe]; rfl
    unfold TimeRand.outcomeOfTimespec TimeRand.allowedStepCore
    dsimp only
    rw [hCond]; rfl

private theorem fallbackClockNanosleep_healthy (clk : TimeRand.ClockId) (abs : Bool) (reqTs : TimeRand.Timespec)
    (env : TimeRand.HealthyEnv) (hWf : env.wf = true) :
    TimeRand.healthyStep env (.clock_nanosleep clk abs reqTs)
      (TimeRand.outcomeOfUnit (fallbackClockNanosleep clk abs reqTs env).1) =
        some (fallbackClockNanosleep clk abs reqTs env).2 ∧
    (fallbackClockNanosleep clk abs reqTs env).2.wf = true := by
  unfold fallbackClockNanosleep
  cases hv : reqTs.isValid
  · simp only [Bool.not_false, ↓reduceIte]
    refine ⟨?_, hWf⟩
    apply tr_healthyStep_of_core hWf _ (by decide) (by decide)
    simp [TimeRand.outcomeOfUnit, TimeRand.allowedStepCore, hv]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases clk with
    | realtime =>
      refine ⟨?_, hWf⟩
      apply tr_healthyStep_of_core hWf _ rfl rfl
      simp [TimeRand.outcomeOfUnit, TimeRand.allowedStepCore, hv]
    | monotonic =>
      refine ⟨?_, hWf⟩
      apply tr_healthyStep_of_core hWf _ rfl rfl
      simp [TimeRand.outcomeOfUnit, TimeRand.allowedStepCore, hv]

private theorem fallbackGetrandom_healthy (len : UInt32) (flags : TimeRand.GrndFlags)
    (env : TimeRand.HealthyEnv) (hWf : env.wf = true) :
    TimeRand.healthyStep env (.getrandom len flags)
      (TimeRand.outcomeOfBytes (fallbackGetrandom len flags env).1) =
        some (fallbackGetrandom len flags env).2 ∧
    (fallbackGetrandom len flags env).2.wf = true := by
  unfold fallbackGetrandom
  cases hi : flags.isInvalid
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, hWf⟩
    apply tr_healthyStep_of_core hWf _ rfl rfl
    let bs := TimeRand.deterministicEntropyBytes env.state.entropyDraws (min len.toNat MAX_READ_BYTES.toNat)
    have hLen : TimeRand.validGetrandomResultLen len bs.data.size = true := by
      have hSzEq : bs.data.size = bs.size := rfl
      rw [hSzEq, tr_entBytes_sz]
      exact tr_validGrndLen len
    unfold TimeRand.outcomeOfBytes TimeRand.allowedStepCore
    simp only [hi, Bool.false_eq_true, ↓reduceIte]
    change (if TimeRand.validGetrandomResultLen len bs.data.size = true then _ else none) = _
    rw [hLen]; rfl
  · simp only [↓reduceIte]
    refine ⟨?_, hWf⟩
    apply tr_healthyStep_of_core hWf _ (by decide) (by decide)
    simp [TimeRand.outcomeOfBytes, TimeRand.allowedStepCore, hi]

private def runSampleTimeOp {α : Type}
    (req : TimeRand.TimeRandReq)
    (pack : Except Errno α → TimeRand.TimeRandOutcome)
    (candAct : StateM TimeRand.HealthyEnv (Except Errno α))
    (fbAct : TimeRand.HealthyEnv → Except Errno α × TimeRand.HealthyEnv) :
    StateM HealthySysWorld (Except Errno α) := fun w =>
  let env := w.timeEnv
  let candRes := (candAct.run env).1
  let fbPair := fbAct env
  match TimeRand.healthyStep env req (pack candRes) with
  | some env' =>
    if env'.wf then (candRes, { w with timeEnv := env' })
    else (fbPair.1, { w with timeEnv := fbPair.2 })
  | none => (fbPair.1, { w with timeEnv := fbPair.2 })

private theorem runSampleTimeOp_world_laws {α : Type}
    (req : TimeRand.TimeRandReq)
    (pack : Except Errno α → TimeRand.TimeRandOutcome)
    (candAct : StateM TimeRand.HealthyEnv (Except Errno α))
    (fbAct : TimeRand.HealthyEnv → Except Errno α × TimeRand.HealthyEnv)
    (w : HealthySysWorld)
    (hWf : w.filesEnv.wf = true ∧ w.netEnv.wf = true ∧ w.pollEnv.wf = true ∧ w.dnsEnv.wf = true ∧ w.timeEnv.wf = true)
    (hFb : TimeRand.healthyStep w.timeEnv req (pack (fbAct w.timeEnv).1) = some (fbAct w.timeEnv).2 ∧
      (fbAct w.timeEnv).2.wf = true) :
    let (r, w') := (runSampleTimeOp req pack candAct fbAct).run w
    TimeRand.healthyStep w.timeEnv req (pack r) = some w'.timeEnv ∧
    (w'.filesEnv.wf = true ∧ w'.netEnv.wf = true ∧ w'.pollEnv.wf = true ∧ w'.dnsEnv.wf = true ∧ w'.timeEnv.wf = true) ∧
    w'.proxyTable = w.proxyTable ∧
    ((w.filesEnv.state.fds.map Prod.fst).Nodup → (w'.filesEnv.state.fds.map Prod.fst).Nodup) := by
  unfold runSampleTimeOp
  dsimp only [StateT.run, Id.run]
  let fbWorld : Except Errno α × HealthySysWorld :=
    ((fbAct w.timeEnv).1, { w with timeEnv := (fbAct w.timeEnv).2 })
  have hFbBr :
      TimeRand.healthyStep w.timeEnv req (pack fbWorld.1) = some fbWorld.2.timeEnv ∧
      (fbWorld.2.filesEnv.wf = true ∧ fbWorld.2.netEnv.wf = true ∧ fbWorld.2.pollEnv.wf = true ∧
       fbWorld.2.dnsEnv.wf = true ∧ fbWorld.2.timeEnv.wf = true) ∧
      fbWorld.2.proxyTable = w.proxyTable ∧
      ((w.filesEnv.state.fds.map Prod.fst).Nodup → (fbWorld.2.filesEnv.state.fds.map Prod.fst).Nodup) :=
    ⟨hFb.1, ⟨hWf.1, hWf.2.1, hWf.2.2.1, hWf.2.2.2.1, hFb.2⟩, rfl, id⟩
  cases hSt : TimeRand.healthyStep w.timeEnv req (pack (candAct w.timeEnv).1) with
  | none =>
    dsimp only
    exact hFbBr
  | some env' =>
    dsimp only
    by_cases hNextWf : env'.wf = true
    · simp only [hNextWf, ↓reduceIte]
      exact ⟨hSt, ⟨hWf.1, hWf.2.1, hWf.2.2.1, hWf.2.2.2.1, trivial⟩, trivial, id⟩
    · have hNextWfF : env'.wf = false := Bool.eq_false_iff.mpr hNextWf
      simp only [hNextWfF, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hFb.1, ⟨hWf.1, hWf.2.1, hWf.2.2.1, hWf.2.2.2.1, hFb.2⟩, trivial, id⟩

/-- Sample `TimeRandOpsM` executing `TimeRand.healthyModelOps` with verified healthy fallback. -/
def sampleHealthyTimeOps : TimeRand.TimeRandOpsM (StateM HealthySysWorld) :=
  { clock_gettime := fun clk =>
      runSampleTimeOp (.clock_gettime clk) TimeRand.outcomeOfTimespec
        (TimeRand.healthyModelOps.clock_gettime clk) (fallbackClockGettime clk)
    clock_nanosleep := fun clk abs ts =>
      runSampleTimeOp (.clock_nanosleep clk abs ts) TimeRand.outcomeOfUnit
        (TimeRand.healthyModelOps.clock_nanosleep clk abs ts) (fallbackClockNanosleep clk abs ts)
    getrandom := fun len fl =>
      runSampleTimeOp (.getrandom len fl) TimeRand.outcomeOfBytes
        (TimeRand.healthyModelOps.getrandom len fl) (fallbackGetrandom len fl) }

/-- Canonical concrete healthy OS syscall bundle inhabiting `RefinesHealthyCProxySys`. -/
def sampleHealthySys : CProxySysOpsM (StateM HealthySysWorld) Nat :=
  { files := sampleHealthyFilesOps
    net := sampleHealthyNetOps
    poll := sampleHealthyPollOps
    dns := sampleHealthyDnsOps
    timeRand := sampleHealthyTimeOps }

private theorem runSampleDnsOp_world_laws (host : String) (hints : Dns.ResolveHints) (w : HealthySysWorld)
    (hWf : w.filesEnv.wf = true ∧ w.netEnv.wf = true ∧ w.pollEnv.wf = true ∧ w.dnsEnv.wf = true ∧ w.timeEnv.wf = true) :
    let (out, w') := (runSampleDnsOp host hints).run w
    Dns.healthyStep w.dnsEnv { host := host, hints := hints } out = some w'.dnsEnv ∧
    (w'.filesEnv.wf = true ∧ w'.netEnv.wf = true ∧ w'.pollEnv.wf = true ∧ w'.dnsEnv.wf = true ∧ w'.timeEnv.wf = true) ∧
    w'.proxyTable = w.proxyTable ∧
    ((w.filesEnv.state.fds.map Prod.fst).Nodup → (w'.filesEnv.state.fds.map Prod.fst).Nodup) := by
  have hFb := fallbackDnsOutcome_healthy w.dnsEnv { host := host, hints := hints } hWf.2.2.2.1
  unfold runSampleDnsOp
  dsimp only [StateT.run, Id.run]
  cases hSt : Dns.healthyStep w.dnsEnv { host := host, hints := hints }
      (Dns.healthyModelOps.getaddrinfo host hints w.dnsEnv).1 with
  | none =>
    dsimp only
    exact ⟨hFb, hWf, rfl, id⟩
  | some env' =>
    dsimp only
    by_cases hNextWf : env'.wf = true
    · simp only [hNextWf, ↓reduceIte]
      exact ⟨hSt, ⟨hWf.1, hWf.2.1, hWf.2.2.1, trivial, hWf.2.2.2.2⟩, trivial, id⟩
    · have hNextWfF : env'.wf = false := Bool.eq_false_iff.mpr hNextWf
      simp only [hNextWfF, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hFb, hWf, trivial, id⟩

/-- Non-vacuity theorem: `sampleHealthySys` refines the relational healthy OS world `RefinesHealthyCProxySys`. -/
theorem sampleHealthySys_refines : RefinesHealthyCProxySys sampleHealthySys := by
  unfold RefinesHealthyCProxySys RefinesHealthyCProxySysAt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w h hWf
    have hCl := sampleHealthyFilesOps_close w h hWf.1
    dsimp only [sampleHealthySys] at hCl ⊢
    exact ⟨hCl.1, ⟨hCl.2, hWf.2.1, hWf.2.2.1, hWf.2.2.2.1, hWf.2.2.2.2⟩, rfl⟩
  · intro w req hWf
    have hPack : ∀ {α : Type} (r : Net.NetReq)
        (pack : Except Errno α → Net.NetOutcome)
        (unpack : Net.NetOutcome → Option (Except Errno α)),
        (∀ e, pack (.error e) = .err e) →
        Net.healthyStep w.netEnv r (pack ((runSampleNetOp r pack unpack).run w).1) =
          some ((runSampleNetOp r pack unpack).run w).2.netEnv ∧
        (((runSampleNetOp r pack unpack).run w).2.filesEnv.wf = true ∧
         ((runSampleNetOp r pack unpack).run w).2.netEnv.wf = true ∧
         ((runSampleNetOp r pack unpack).run w).2.pollEnv.wf = true ∧
         ((runSampleNetOp r pack unpack).run w).2.dnsEnv.wf = true ∧
         ((runSampleNetOp r pack unpack).run w).2.timeEnv.wf = true) ∧
        ((runSampleNetOp r pack unpack).run w).2.proxyTable = w.proxyTable ∧
        ((w.filesEnv.state.fds.map Prod.fst).Nodup →
          (((runSampleNetOp r pack unpack).run w).2.filesEnv.state.fds.map Prod.fst).Nodup) := by
      intro α r pack unpack hPE
      have hN := runSampleNetOp_healthy r pack unpack hPE w hWf.2.1
      exact ⟨hN.1, ⟨by rw [hN.2.2.1]; exact hWf.1, hN.2.1, by rw [hN.2.2.2.1]; exact hWf.2.2.1,
        by rw [hN.2.2.2.2.1]; exact hWf.2.2.2.1, by rw [hN.2.2.2.2.2.1]; exact hWf.2.2.2.2⟩,
        hN.2.2.2.2.2.2, fun hNd => by rw [hN.2.2.1]; exact hNd⟩
    cases req <;>
      exact hPack _ _ _ (fun _ => rfl)
  · intro w req hWf
    have hPollOp : ∀ {α : Type} (r : Poll.PollReq)
        (pack : Except Errno α → Poll.PollOutcome)
        (unpack : Poll.PollOutcome → Option (Except Errno α)),
        (∀ e, pack (.error e) = .err e) →
        Poll.healthyStep w.pollEnv r (pack ((runSamplePollOp r pack unpack).run w).1) =
          some ((runSamplePollOp r pack unpack).run w).2.pollEnv ∧
        (((runSamplePollOp r pack unpack).run w).2.filesEnv.wf = true ∧
         ((runSamplePollOp r pack unpack).run w).2.netEnv.wf = true ∧
         ((runSamplePollOp r pack unpack).run w).2.pollEnv.wf = true ∧
         ((runSamplePollOp r pack unpack).run w).2.dnsEnv.wf = true ∧
         ((runSamplePollOp r pack unpack).run w).2.timeEnv.wf = true) ∧
        ((runSamplePollOp r pack unpack).run w).2.proxyTable = w.proxyTable ∧
        ((w.filesEnv.state.fds.map Prod.fst).Nodup →
          (((runSamplePollOp r pack unpack).run w).2.filesEnv.state.fds.map Prod.fst).Nodup) := by
      intro α r pack unpack hPE
      have hFb : Poll.healthyStep w.pollEnv r (pack (.error (fallbackPollErrno w.pollEnv.state r))) = some w.pollEnv := by
        rw [hPE]; exact fallbackPollErrno_healthy w.pollEnv r hWf.2.2.1
      unfold runSamplePollOp
      dsimp only [StateT.run, Id.run]
      cases Poll.stepPollCore w.pollEnv.state r none with
      | none => exact ⟨hFb, hWf, rfl, id⟩
      | some pair =>
        dsimp only
        cases unpack pair.1 with
        | none => exact ⟨hFb, hWf, rfl, id⟩
        | some candRes =>
          dsimp only
          cases hSt : Poll.healthyStep w.pollEnv r (pack candRes) with
          | none => exact ⟨hFb, hWf, rfl, id⟩
          | some env' =>
            dsimp only
            by_cases hNextWf : env'.wf = true
            · have hIf : (if env'.wf = true then (candRes, { w with pollEnv := env' })
                  else (.error (fallbackPollErrno w.pollEnv.state r), w)) =
                  (candRes, { w with pollEnv := env' }) := by simp [hNextWf]
              change Poll.healthyStep w.pollEnv r (pack (if env'.wf = true then (candRes, { w with pollEnv := env' })
                  else (.error (fallbackPollErrno w.pollEnv.state r), w)).1) = _ ∧ _
              rw [hIf]; dsimp only
              exact ⟨hSt, ⟨hWf.1, hWf.2.1, hNextWf, hWf.2.2.2.1, hWf.2.2.2.2⟩, rfl, id⟩
            · have hNextWfF : env'.wf = false := Bool.eq_false_iff.mpr hNextWf
              have hIf : (if env'.wf = true then (candRes, { w with pollEnv := env' })
                  else (.error (fallbackPollErrno w.pollEnv.state r), w)) =
                  (.error (fallbackPollErrno w.pollEnv.state r), w) := by simp [hNextWfF]
              change Poll.healthyStep w.pollEnv r (pack (if env'.wf = true then (candRes, { w with pollEnv := env' })
                  else (.error (fallbackPollErrno w.pollEnv.state r), w)).1) = _ ∧ _
              rw [hIf]; dsimp only
              exact ⟨hFb, hWf, rfl, id⟩
    cases req <;>
      exact hPollOp _ _ _ (fun _ => rfl)
  · intro w req hWf
    rcases req with ⟨host, hints⟩
    exact runSampleDnsOp_world_laws host hints w hWf
  · intro w req hWf
    cases req with
    | clock_gettime clk =>
      exact runSampleTimeOp_world_laws (.clock_gettime clk) TimeRand.outcomeOfTimespec
        (TimeRand.healthyModelOps.clock_gettime clk) (fallbackClockGettime clk) w hWf
        (fallbackClockGettime_healthy clk w.timeEnv hWf.2.2.2.2)
    | clock_nanosleep clk abs ts =>
      exact runSampleTimeOp_world_laws (.clock_nanosleep clk abs ts) TimeRand.outcomeOfUnit
        (TimeRand.healthyModelOps.clock_nanosleep clk abs ts) (fallbackClockNanosleep clk abs ts) w hWf
        (fallbackClockNanosleep_healthy clk abs ts w.timeEnv hWf.2.2.2.2)
    | getrandom len fl =>
      exact runSampleTimeOp_world_laws (.getrandom len fl) TimeRand.outcomeOfBytes
        (TimeRand.healthyModelOps.getrandom len fl) (fallbackGetrandom len fl) w hWf
        (fallbackGetrandom_healthy len fl w.timeEnv hWf.2.2.2.2)
  · intro _ _; rfl
  · intro _ _; exact ⟨id, id⟩

end LeanSwe.ConnectProxy.Proofs
