import Core.Refines
import LeanSwe.Uuid.Model
import LeanSwe.Uuid.Interface
import LeanSwe.Uuid.Proofs.Codec
import LeanSwe.Uuid.Proofs.Entropy

/-!
# Model Refinement Proofs for `LeanSwe.Uuid`

Proves `LeanSwe.Uuid.Proofs.refines_model_impl` relating every pure operation
in `LeanSwe.Uuid.Interface` to `LeanSwe.Uuid.Model` and lifting healthy
`LeanSwe.LinuxSyscall.TimeRand.Model` transitions through `Internal.mkApi`
via `Core.RefinesStepFrom`.
-/

namespace LeanSwe.Uuid.Proofs.RefinesModel

open Core
open LeanSwe.LinuxSyscall (Errno MAX_READ_BYTES)
open LeanSwe.LinuxSyscall.TimeRand
  (TimeRandOpsM TimeRandReq TimeRandOutcome HealthyEnv
   GETRANDOM_EXACT_MAX
   execTimeRandReq healthyStep allowedStep allowedStepCore validGetrandomResultLen)
open LeanSwe.Uuid
open LeanSwe.Uuid.Proofs.Codec
open LeanSwe.Uuid.Proofs.Entropy

private theorem hexCharsToByte_eq (hi lo : Char) :
    Internal.hexCharsToByte hi lo = Model.hexCharsToByte hi lo := rfl

private theorem decodeHexPairs_eq : ∀ cs : List Char,
    Internal.decodeHexPairs cs = Model.decodeHexPairs cs
  | [] => rfl
  | [_] => rfl
  | hi :: lo :: rest => by
    change (match Internal.hexCharsToByte hi lo, Internal.decodeHexPairs rest with
      | some b, some bs => some (b :: bs)
      | _, _ => none) =
      (match Model.hexCharsToByte hi lo, Model.decodeHexPairs rest with
      | some b, some bs => some (b :: bs)
      | _, _ => none)
    rw [hexCharsToByte_eq, decodeHexPairs_eq rest]

private theorem validateV4BytesList_eq (bs : List UInt8) :
    Internal.validateV4BytesList bs = Model.validateV4BytesList bs := rfl

private theorem parseHexChars_eq (cs : List Char) :
    Internal.parseHexChars cs = Model.parseHexChars cs := by
  dsimp only [Internal.parseHexChars, Model.parseHexChars]
  rw [decodeHexPairs_eq]
  cases Model.decodeHexPairs cs <;> rfl

private theorem stripCanonicalHyphens_eq (cs : List Char) :
    Internal.stripCanonicalHyphens cs = Model.stripCanonicalHyphens cs := rfl

private theorem parseCanonicalChars_eq (cs : List Char) :
    Internal.parseCanonicalChars cs = Model.parseCanonicalChars cs := by
  dsimp only [Internal.parseCanonicalChars, Model.parseCanonicalChars]
  rw [stripCanonicalHyphens_eq]
  cases Model.stripCanonicalHyphens cs with
  | none => rfl
  | some hex =>
    by_cases hlen : (cs.length != 36) = true
    · simp [hlen]
    · simp [hlen, parseHexChars_eq]

/-- Pure refinement of `LeanSwe.Uuid.mapRawError` to `Model.mapRawError`. -/
theorem refines_mapRawError :
    Core.RefinesPureEq LeanSwe.Uuid.mapRawError Model.mapRawError := by
  intro raw
  cases raw <;> rfl

/-- Pure refinement of `LeanSwe.Uuid.fromRandomBytes` to `Model.fromRandomBytes`. -/
theorem refines_fromRandomBytes :
    Core.RefinesPureEq LeanSwe.Uuid.fromRandomBytes Model.fromRandomBytes := by
  intro bs
  rfl

/-- Pure refinement of `LeanSwe.Uuid.toString` to `Model.toString`. -/
theorem refines_toString :
    Core.RefinesPureEq LeanSwe.Uuid.toString Model.toString := by
  intro u
  rfl

/-- Pure refinement of `LeanSwe.Uuid.toHex` to `Model.toHex`. -/
theorem refines_toHex :
    Core.RefinesPureEq LeanSwe.Uuid.toHex Model.toHex := by
  intro u
  rfl

/-- Pure refinement of `LeanSwe.Uuid.parse` to `Model.parse`. -/
theorem refines_parse :
    Core.RefinesPureEq LeanSwe.Uuid.parse Model.parse := by
  intro s
  exact parseCanonicalChars_eq s.toList

/-- Pure refinement of `LeanSwe.Uuid.parseHex` to `Model.parseHex`. -/
theorem refines_parseHex :
    Core.RefinesPureEq LeanSwe.Uuid.parseHex Model.parseHex := by
  intro s
  exact parseHexChars_eq s.toList

/-- Pure refinement of `LeanSwe.Uuid.isValid` to `Model.isValid`. -/
theorem refines_isValid :
    Core.RefinesPureEq LeanSwe.Uuid.isValid Model.isValid := by
  intro s
  dsimp [LeanSwe.Uuid.isValid, defaultApi, Internal.mkApi, Internal.isValid, Model.isValid]
  rw [show Internal.parse s = Model.parse s from refines_parse s]

private theorem stateM_bind_run {σ α β : Type} (a : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (a >>= f).run s = (f (a.run s).1).run (a.run s).2 := rfl

private theorem validGetrandom16_size {got : ByteArray}
    (hv : validGetrandomResultLen (UInt32.ofNat 16) got.data.size = true) :
    got.size = 16 := by
  have hcap : min (UInt32.ofNat 16).toNat MAX_READ_BYTES.toNat = 16 := by decide
  have hexact : 16 ≤ GETRANDOM_EXACT_MAX := by decide
  unfold validGetrandomResultLen at hv
  rw [hcap] at hv
  simp only [show (16 == 0) = false by decide, Bool.false_eq_true, ↓reduceIte, hexact] at hv
  exact beq_iff_eq.mp hv

private theorem getrandom16_healthy_step {W : Type}
    (proj : W → HealthyEnv) (sys : TimeRandOpsM (StateM W))
    (hRaw : Core.RefinesStep proj Model.healthyWf (Model.execRawStep sys) Model.allowedRawStep)
    (w : W) (hw : (proj w).wf = true) :
    let (res, w') := (sys.getrandom (UInt32.ofNat 16) {}).run w
    match res with
    | .ok got =>
      got.size = 16 ∧
      (proj w').wf = true ∧
      (proj w').state.monoLowerBoundNs = (proj w).state.monoLowerBoundNs ∧
      (proj w').state.realtimeNs = (proj w).state.realtimeNs ∧
      (proj w').state.crngReady = true ∧
      (proj w').state.entropyDraws = (proj w).state.entropyDraws + 1 ∧
      (proj w').eintrBudget = (proj w).eintrBudget
    | .error e =>
      e = Errno.EINTR ∧
      (proj w').wf = true ∧
      (proj w).state.crngReady = false ∧
      0 < (proj w).eintrBudget ∧
      (proj w').state = (proj w).state ∧
      (proj w').eintrBudget = (proj w).eintrBudget - 1 := by
  have hStep := hRaw w (.getrandom (UInt32.ofNat 16) {}) hw
  dsimp only [Model.execRawStep, execTimeRandReq, Model.allowedRawStep,
    healthyStep, LeanSwe.LinuxSyscall.TimeRand.isCriticalFault,
    LeanSwe.LinuxSyscall.TimeRand.isEintrOutcome] at hStep
  rw [stateM_bind_run] at hStep
  have hns : (proj w).state.ambientSeccomp = false := by
    simpa [HealthyEnv.wf] using hw
  have hwfF : (!HealthyEnv.wf (proj w)) = false := by
    have hwf' : HealthyEnv.wf (proj w) = true := hw
    simp [hwf']
  cases hgr : (sys.getrandom (UInt32.ofNat 16) {}).run w with
  | mk res w' =>
    rw [hgr] at hStep
    dsimp only [Pure.pure, StateT.pure, StateT.run] at hStep ⊢
    rw [hwfF] at hStep
    cases res with
    | ok got =>
      dsimp only [LeanSwe.LinuxSyscall.TimeRand.outcomeOfBytes,
        LeanSwe.LinuxSyscall.Errno.isCriticalOsErrno, allowedStep, allowedStepCore] at hStep
      rw [hns] at hStep
      simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte,
        show ({} : LeanSwe.LinuxSyscall.TimeRand.GrndFlags).isInvalid = false by rfl] at hStep
      by_cases hv : validGetrandomResultLen (UInt32.ofNat 16) got.data.size = true
      · simp only [hv, ↓reduceIte] at hStep
        injection hStep with hProj
        have hsz := validGetrandom16_size hv
        refine ⟨hsz, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [← hProj]; simp [HealthyEnv.wf]
        · rw [← hProj]
        · rw [← hProj]
        · rw [← hProj]; simp
        · rw [← hProj]
        · rw [← hProj]
      · have hvF : validGetrandomResultLen (UInt32.ofNat 16) got.data.size = false :=
          Bool.eq_false_iff.mpr hv
        rw [hvF] at hStep
        simp at hStep
    | error e =>
      dsimp only [LeanSwe.LinuxSyscall.TimeRand.outcomeOfBytes, allowedStep, allowedStepCore] at hStep
      rw [hns] at hStep
      by_cases hcrit : LeanSwe.LinuxSyscall.Errno.isCriticalOsErrno e = true
      · simp [hcrit] at hStep
      · simp only [hcrit, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
          show ({} : LeanSwe.LinuxSyscall.TimeRand.GrndFlags).isInvalid = false by rfl,
          Bool.and_false, Bool.false_and, Bool.not_false, Bool.and_true] at hStep
        by_cases he : e = Errno.EINTR
        · subst he
          simp only [beq_self_eq_true, Bool.and_true] at hStep
          by_cases hcrng : (proj w).state.crngReady = true
          · simp [hcrng] at hStep
          · have hcrngF : (proj w).state.crngReady = false := Bool.eq_false_iff.mpr hcrng
            simp only [hcrngF, Bool.not_false, ↓reduceIte] at hStep
            by_cases hbud : (proj w).eintrBudget > 0
            · simp only [hbud, ↓reduceIte] at hStep
              injection hStep with hProj
              refine ⟨rfl, ?_, hcrngF, hbud, ?_, ?_⟩
              · rw [← hProj]; exact hw
              · rw [← hProj]
              · rw [← hProj]
            · simp [hbud] at hStep
        · simp [beq_false_of_ne he] at hStep

private theorem gatherRandomBytes16_zero_empty {m : Type → Type} [Monad m]
    (sys : TimeRandOpsM m) (last? : Option Errno) :
    Internal.gatherRandomBytes16 sys 0 ByteArray.empty last? =
      match last? with
      | some e => pure (.error (Internal.mapErrnoToUuidError e))
      | none => pure (.error (Internal.mapRawError
          (.shortRead 0 "getrandom retry budget exhausted after 0 of 16 bytes"))) := by
  rw [Internal.gatherRandomBytes16.eq_def]
  rfl

private theorem gatherRandomBytes16_healthy_spec {W : Type}
    (proj : W → HealthyEnv) (sys : TimeRandOpsM (StateM W))
    (hRaw : Core.RefinesStep proj Model.healthyWf (Model.execRawStep sys) Model.allowedRawStep) :
    ∀ (fuel : Nat) (_hfuel : 0 < fuel) (last? : Option Errno) (w : W),
      (proj w).wf = true →
      let (res, w') := (Internal.gatherRandomBytes16 sys fuel ByteArray.empty last?).run w
      match res with
      | .ok bs =>
        bs.size = 16 ∧
        (proj w').wf = true ∧
        (proj w').state.monoLowerBoundNs = (proj w).state.monoLowerBoundNs ∧
        (proj w').state.realtimeNs = (proj w).state.realtimeNs ∧
        (proj w').state.crngReady = true ∧
        (proj w').state.entropyDraws = (proj w).state.entropyDraws + 1 ∧
        (proj w').eintrBudget ≤ (proj w).eintrBudget ∧
        ((proj w).state.crngReady = true → (proj w').eintrBudget = (proj w).eintrBudget)
      | .error err =>
        err = Internal.mapErrnoToUuidError Errno.EINTR ∧
        (proj w).state.crngReady = false ∧
        fuel ≤ (proj w).eintrBudget ∧
        (proj w').state = (proj w).state ∧
        (proj w').eintrBudget = (proj w).eintrBudget - fuel := by
  intro fuel
  induction fuel with
  | zero => intro hfuel; omega
  | succ fuel' ih =>
    intro _ last? w hw
    rw [gatherRandomBytes16_step_succ _ _ ByteArray.empty (by decide) last?, stateM_bind_run]
    have hneed : 16 - ByteArray.empty.size = 16 := rfl
    rw [hneed]
    have hgr := getrandom16_healthy_step proj sys hRaw w hw
    cases hrun : (sys.getrandom (UInt32.ofNat 16) {}).run w with
    | mk r w1 =>
      rw [hrun] at hgr
      dsimp only [Pure.pure, StateT.pure, StateT.run, Bind.bind, StateT.bind] at hgr ⊢
      cases r with
      | ok got =>
        rcases hgr with ⟨hsz, hwf1, hmono1, hreal1, hcrng1, hdraws1, hbud1⟩
        have hcond : (got.size == 0 || decide (got.size > 16)) = false := by
          simp [hsz]
        have happ : Internal.appendBytes ByteArray.empty got = got := rfl
        dsimp only [Internal.stepRandomBytes16]
        rw [hcond]
        simp only [Bool.false_eq_true, ↓reduceIte, happ, show (got.size == 16) = true by simp [hsz]]
        exact ⟨hsz, hwf1, hmono1, hreal1, hcrng1, hdraws1, Nat.le_of_eq hbud1, fun _ => hbud1⟩
      | error e =>
        rcases hgr with ⟨he, hwf1, hcrng0, hbudPos, hst1, hbud1⟩
        subst he
        dsimp only [Internal.stepRandomBytes16]
        have heqT : (Errno.EINTR == Errno.EINTR) = true := rfl
        rw [heqT]
        simp only [↓reduceIte]
        cases fuel' with
        | zero =>
          rw [gatherRandomBytes16_zero_empty]
          dsimp only [Pure.pure, StateT.pure, StateT.run]
          exact ⟨rfl, hcrng0, hbudPos, hst1, hbud1⟩
        | succ k =>
          have hih := ih (Nat.succ_pos k) (some Errno.EINTR) w1 hwf1
          cases hrec : (Internal.gatherRandomBytes16 sys (k + 1) ByteArray.empty (some Errno.EINTR)).run w1 with
          | mk res2 w2 =>
            rw [hrec] at hih
            dsimp only [StateT.run] at hrec
            rw [hrec]
            dsimp only [Pure.pure, StateT.pure, StateT.run] at hih ⊢
            cases res2 with
            | ok bs =>
              rcases hih with ⟨hsz, hwf2, hmono2, hreal2, hcrng2, hdraws2, hbudLe, _⟩
              refine ⟨hsz, hwf2, ?_, ?_, hcrng2, ?_, ?_, ?_⟩
              · rw [hmono2, hst1]
              · rw [hreal2, hst1]
              · rw [hdraws2, hst1]
              · omega
              · intro hcrngT; rw [hcrngT] at hcrng0; cases hcrng0
            | error err =>
              rcases hih with ⟨herr, _, hkle, hst2, hbud2⟩
              refine ⟨herr, hcrng0, ?_, ?_, ?_⟩
              · omega
              · rw [hst2, hst1]
              · omega

private theorem fromRandomBytes_isValidV4 {bs : ByteArray} (hsz : bs.size = 16) :
    ∃ u : Uuid, Internal.fromRandomBytes bs = .ok u ∧ Model.isValidV4Uuid u = true := by
  obtain ⟨u, hfr, hv, _, _, _⟩ := fromRandomBytes_spec hsz
  refine ⟨u, hfr, ?_⟩
  rw [Model.isValidV4Uuid, hv.1, hv.2.1, hv.2.2]
  rfl

private theorem stateM_map_run {W α β : Type} (f : α → β) (x : StateM W α) (w : W) :
    (f <$> x).run w = (f (x.run w).1, (x.run w).2) := rfl

/-- Compositional single-step refinement of `Internal.mkApi` over `TimeRand` healthy worlds. -/
theorem refinesStepFrom_mkApi :
    Core.RefinesStepFrom id Model.healthyWf Model.execRawStep Model.allowedRawStep
      Model.healthyWf Internal.mkApi Model.execPkgStep Model.allowedPkgStep := by
  intro W proj sys hRaw w req hw
  cases req
  dsimp only [Model.execPkgStep, Internal.mkApi]
  rw [stateM_map_run, stateM_bind_run]
  have hg := gatherRandomBytes16_healthy_spec proj sys hRaw Internal.MAX_GETRANDOM_ATTEMPTS
    (by decide) none w hw
  cases hgr : (Internal.gatherRandomBytes16 sys Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty none).run w with
  | mk res w' =>
    rw [hgr] at hg
    dsimp only [Pure.pure, StateT.pure, StateT.run] at hg ⊢
    cases res with
    | ok bs =>
      obtain ⟨hsz, hwf', hmono', hreal', hcrng', hdraws', hbudLe, hbudEq⟩ := hg
      obtain ⟨u, hfr, hv⟩ := fromRandomBytes_isValidV4 hsz
      dsimp only [Function.comp, id, Pure.pure, StateT.pure, StateT.run, Model.allowedPkgStep]
      rw [hfr]
      dsimp only
      exact ⟨rfl, hv, hwf', hmono', hreal', hcrng', hdraws', hbudLe, hbudEq⟩
    | error err =>
      rcases hg with ⟨herr, hcrng0, hbudGe, hst', hbud'⟩
      dsimp only [Function.comp, id, Pure.pure, StateT.pure, StateT.run, Model.allowedPkgStep]
      subst herr
      refine ⟨rfl, rfl, rfl, ?_, hcrng0, hbudGe, hst', hbud'⟩
      have hne := mapRawError_msg_ne
        (.osError Errno.EINTR s!"getrandom failed with {Errno.name Errno.EINTR} ({Errno.EINTR})")
      cases hEmpty : (Internal.mapErrnoToUuidError Errno.EINTR).message.isEmpty with
      | false => rfl
      | true =>
        exfalso
        apply hne
        exact String.isEmpty_iff.mp hEmpty

/-- Full public `Interface` refinement of `LeanSwe.Uuid` against `LeanSwe.Uuid.Model`. -/
theorem refines_model_impl :
    Core.RefinesPureEq LeanSwe.Uuid.mapRawError Model.mapRawError ∧
    Core.RefinesPureEq LeanSwe.Uuid.fromRandomBytes Model.fromRandomBytes ∧
    Core.RefinesPureEq LeanSwe.Uuid.toString Model.toString ∧
    Core.RefinesPureEq LeanSwe.Uuid.toHex Model.toHex ∧
    Core.RefinesPureEq LeanSwe.Uuid.parse Model.parse ∧
    Core.RefinesPureEq LeanSwe.Uuid.parseHex Model.parseHex ∧
    Core.RefinesPureEq LeanSwe.Uuid.isValid Model.isValid ∧
    Core.RefinesStepFrom id Model.healthyWf Model.execRawStep Model.allowedRawStep
      Model.healthyWf Internal.mkApi Model.execPkgStep Model.allowedPkgStep :=
  ⟨refines_mapRawError,
   refines_fromRandomBytes,
   refines_toString,
   refines_toHex,
   refines_parse,
   refines_parseHex,
   refines_isValid,
   refinesStepFrom_mkApi⟩

end LeanSwe.Uuid.Proofs.RefinesModel
