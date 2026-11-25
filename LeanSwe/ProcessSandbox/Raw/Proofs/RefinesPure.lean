import Core.Obeys
import LeanSwe.ProcessSandbox.Raw.Interface
import LeanSwe.ProcessSandbox.Raw.Model.Refines
import LeanSwe.ProcessSandbox.Raw.Proofs.EncodePlan

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.Model

/-- `Raw.mapRawError` equals `Model.Internal.mapRawError` everywhere. -/
theorem refinesPure_mapRawError :
    Core.ObeysPureEq LeanSwe.ProcessSandbox.Raw.mapRawError Model.Internal.mapRawError :=
  fun _ => rfl

/-- `Raw.decodeHostAuditArch` equals `Model.decodeHostAuditArch` everywhere. -/
theorem refinesPure_decodeHostAuditArch :
    Core.ObeysPureEq LeanSwe.ProcessSandbox.Raw.decodeHostAuditArch Model.decodeHostAuditArch :=
  fun _ => rfl

private theorem pushStr_ok_iff (ba : ByteArray) (s : String) :
    (∃ out, Internal.pushStr ba s = .ok out) ↔ wireStringValid s = true := by
  unfold Internal.pushStr Internal.hasNulByte wireStringValid
  by_cases hnul : s.toUTF8.data.toList.contains 0 = true
  · simp only [hnul, ↓reduceIte, Bool.not_true, Bool.false_and, Bool.false_eq_true, iff_false]
    intro ⟨_, h⟩
    cases h
  · have hnf : s.toUTF8.data.toList.contains 0 = false := Bool.eq_false_iff.mpr hnul
    simp only [hnf, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, decide_eq_true_eq]
    by_cases hge : s.toUTF8.size ≥ UInt32.size
    · have hnotlt : ¬ s.toUTF8.size < UInt32.size := by omega
      simp only [hge, ↓reduceIte, hnotlt, iff_false]
      intro ⟨_, h⟩
      cases h
    · have hlt : s.toUTF8.size < UInt32.size := by omega
      simp only [hge, ↓reduceIte, hlt, iff_true, pure, Except.pure]
      exact ⟨_, rfl⟩

private theorem forIn_list_step_ok_iff {α : Type}
    (step : α → ByteArray → Except SandboxError (ForInStep ByteArray))
    (P : α → Bool)
    (hf : ∀ x ba, (∃ out, step x ba = .ok (.yield out)) ↔ P x = true)
    (hNoDone : ∀ x ba out, step x ba ≠ .ok (.done out))
    (xs : List α) (init : ByteArray) :
    (∃ out, forIn xs init step = .ok out) ↔ xs.all P = true := by
  induction xs generalizing init with
  | nil => simp [pure, Except.pure]
  | cons x rest ih =>
    simp only [List.forIn_cons, List.all_cons, Bool.and_eq_true, bind, Except.bind, pure, Except.pure]
    cases hfx : step x init with
    | error e =>
      have hPf : P x ≠ true := by
        intro hPt
        obtain ⟨out, hout⟩ := (hf x init).mpr hPt
        rw [hfx] at hout; cases hout
      constructor
      · intro ⟨_, h⟩; cases h
      · intro ⟨hPx, _⟩; exact absurd hPx hPf
    | ok st =>
      cases st with
      | done b => exact absurd hfx (hNoDone x init b)
      | yield ba1 =>
        have hPx : P x = true := (hf x init).mp ⟨ba1, hfx⟩
        simp only [hPx, true_and]
        exact ih ba1

private theorem forIn_array_step_ok_iff {α : Type}
    (step : α → ByteArray → Except SandboxError (ForInStep ByteArray))
    (P : α → Bool)
    (hf : ∀ x ba, (∃ out, step x ba = .ok (.yield out)) ↔ P x = true)
    (hNoDone : ∀ x ba out, step x ba ≠ .ok (.done out))
    (arr : Array α) (init : ByteArray) :
    (∃ out, forIn arr init step = .ok out) ↔ arr.toList.all P = true := by
  rw [← Array.forIn_toList]
  exact forIn_list_step_ok_iff step P hf hNoDone arr.toList init

private theorem yield1_ok_iff (r : Except SandboxError ByteArray) (P : Prop)
    (h : (∃ out, r = .ok out) ↔ P) :
    (∃ out, (do let b ← r; pure (ForInStep.yield b)) = .ok (.yield out)) ↔ P := by
  rw [← h]
  cases r <;> simp [bind, Except.bind, pure, Except.pure]

private theorem yield1_ne_done (r : Except SandboxError ByteArray) (out : ByteArray) :
    (do let b ← r; pure (ForInStep.yield b)) ≠ .ok (.done out) := by
  cases r <;> simp [bind, Except.bind, pure, Except.pure]

private theorem yield2_ok_iff (r1 : Except SandboxError ByteArray) (f2 : ByteArray → Except SandboxError ByteArray)
    (P1 P2 : Prop)
    (h1 : (∃ out, r1 = .ok out) ↔ P1)
    (h2 : ∀ b, (∃ out, f2 b = .ok out) ↔ P2) :
    (∃ out, (do let b1 ← r1; let b2 ← f2 b1; pure (ForInStep.yield b2)) = .ok (.yield out)) ↔ (P1 ∧ P2) := by
  cases hr1 : r1 with
  | error e =>
    have hn : ¬ P1 := fun hp => by obtain ⟨a, ha⟩ := h1.mpr hp; rw [hr1] at ha; cases ha
    simp only [bind, Except.bind, hn, false_and, iff_false]
    intro ⟨_, h⟩; cases h
  | ok b1 =>
    have hp1 : P1 := h1.mp ⟨b1, hr1⟩
    simp only [hp1, true_and]
    simpa [bind, Except.bind] using yield1_ok_iff (f2 b1) P2 (h2 b1)

private theorem yield2_ne_done (r1 : Except SandboxError ByteArray) (f2 : ByteArray → Except SandboxError ByteArray)
    (out : ByteArray) :
    (do let b1 ← r1; let b2 ← f2 b1; pure (ForInStep.yield b2)) ≠ .ok (.done out) := by
  cases r1 with
  | error _ => simp [bind, Except.bind]
  | ok b1 => simpa [bind, Except.bind] using yield1_ne_done (f2 b1) out

private theorem forIn_portForwards_ok (pfs : Array PortForward) (init : ByteArray) :
    ∃ out, (forIn pfs init fun pf ba =>
      (pure (ForInStep.yield (Internal.pushU16LE (Internal.pushU16LE ba pf.boxPort) pf.hostPort)) :
        Except SandboxError (ForInStep ByteArray))) = .ok out := by
  have h := forIn_array_step_ok_iff
    (fun (pf : PortForward) ba => (pure (ForInStep.yield (Internal.pushU16LE (Internal.pushU16LE ba pf.boxPort) pf.hostPort)) :
      Except SandboxError (ForInStep ByteArray)))
    (fun _ => true)
    (fun _ _ => ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩)
    (fun _ _ _ h => by cases h) pfs init
  have hTrue : pfs.toList.all (fun _ => true) = true := by simp
  exact h.mpr hTrue

private theorem except_bind_ok_iff {α β : Type} (x : Except SandboxError α)
    (k : α → Except SandboxError β) (P Q : Prop)
    (hx : (∃ a, x = .ok a) ↔ P)
    (hk : ∀ a, x = .ok a → ((∃ b, k a = .ok b) ↔ Q)) :
    (∃ b, (x >>= k) = .ok b) ↔ (P ∧ Q) := by
  cases h : x with
  | error e =>
    have hnotP : ¬ P := fun hp => by obtain ⟨a, ha⟩ := hx.mpr hp; rw [h] at ha; cases ha
    constructor
    · intro ⟨_, hb⟩; cases hb
    · intro ⟨hp, _⟩; exact absurd hp hnotP
  | ok a =>
    have hp : P := hx.mp ⟨a, h⟩
    simp only [bind, Except.bind, hp, true_and]
    exact hk a h

private theorem encodePlanPrefix_ok_iff (plan : CompiledSandboxPlan) :
    (∃ out, Internal.encodePlanPrefix plan = .ok out) ↔ planStringsValid plan = true := by
  unfold Internal.encodePlanPrefix planStringsValid
  dsimp only
  simp only [Bool.and_eq_true, and_assoc]
  refine except_bind_ok_iff _ _ _ _ (pushStr_ok_iff _ _) (fun _ _ => ?_)
  refine except_bind_ok_iff _ _ _ _ (pushStr_ok_iff _ _) (fun _ _ => ?_)
  refine except_bind_ok_iff _ _ _ _
    (forIn_array_step_ok_iff (fun a ba => do let ba ← Internal.pushStr ba a; pure (ForInStep.yield ba))
      wireStringValid (fun a ba => yield1_ok_iff _ _ (pushStr_ok_iff ba a)) (fun a ba out => yield1_ne_done _ out) _ _)
    (fun _ _ => ?_)
  refine except_bind_ok_iff _ _ _ _
    (forIn_array_step_ok_iff
      (fun (kv : String × String) ba => do let ba ← Internal.pushStr ba kv.1; let ba ← Internal.pushStr ba kv.2; pure (ForInStep.yield ba))
      (fun kv => wireStringValid kv.1 && wireStringValid kv.2)
      (fun kv ba => by
        simp only [Bool.and_eq_true]
        exact yield2_ok_iff _ _ _ _ (pushStr_ok_iff ba kv.1) (fun b1 => pushStr_ok_iff b1 kv.2))
      (fun kv ba out => yield2_ne_done _ _ out) _ _)
    (fun _ _ => ?_)
  refine except_bind_ok_iff _ _ _ _
    (forIn_array_step_ok_iff
      (fun (e : PresetSystemEntry) ba => match e with
        | .readOnlyDir p => do let ba ← Internal.pushStr (Internal.pushU8 ba 0) p; pure (ForInStep.yield ba)
        | .topSymlink lp tgt => do let ba ← Internal.pushStr (Internal.pushU8 ba 1) lp; let ba ← Internal.pushStr ba tgt; pure (ForInStep.yield ba))
      (fun e => match e with | .readOnlyDir p => wireStringValid p | .topSymlink lp tgt => wireStringValid lp && wireStringValid tgt)
      (fun e ba => by
        cases e with
        | readOnlyDir p => exact yield1_ok_iff _ _ (pushStr_ok_iff _ p)
        | topSymlink lp tgt =>
          simp only [Bool.and_eq_true]
          exact yield2_ok_iff _ _ _ _ (pushStr_ok_iff _ lp) (fun b1 => pushStr_ok_iff b1 tgt))
      (fun e ba out => by
        cases e with
        | readOnlyDir p => exact yield1_ne_done _ out
        | topSymlink lp tgt => exact yield2_ne_done _ _ out) _ _)
    (fun _ _ => ?_)
  refine except_bind_ok_iff _ _ _ _
    (forIn_array_step_ok_iff (fun p ba => do let ba ← Internal.pushStr ba p; pure (ForInStep.yield ba))
      wireStringValid (fun p ba => yield1_ok_iff _ _ (pushStr_ok_iff ba p)) (fun p ba out => yield1_ne_done _ out) _ _)
    (fun _ _ => ?_)
  refine except_bind_ok_iff _ _ _ _
    (forIn_array_step_ok_iff (fun m ba => do let ba ← Internal.pushStr ba m; pure (ForInStep.yield ba))
      wireStringValid (fun m ba => yield1_ok_iff _ _ (pushStr_ok_iff ba m)) (fun m ba out => yield1_ne_done _ out) _ _)
    (fun _ _ => ?_)
  refine (except_bind_ok_iff _ _ _ True
    (forIn_array_step_ok_iff
      (fun (m : SandboxMount) ba => match m with
        | .readOnly hp bp => do let ba ← Internal.pushStr (Internal.pushU8 ba 0) hp; let ba ← Internal.pushStr ba bp; pure (ForInStep.yield ba)
        | .readWrite hp bp => do let ba ← Internal.pushStr (Internal.pushU8 ba 1) hp; let ba ← Internal.pushStr ba bp; pure (ForInStep.yield ba)
        | .scratch bp => do let ba ← Internal.pushStr (Internal.pushU8 ba 2) bp; pure (ForInStep.yield ba))
      (fun m => match m with
        | .readOnly hp bp => wireStringValid hp && wireStringValid bp
        | .readWrite hp bp => wireStringValid hp && wireStringValid bp
        | .scratch bp => wireStringValid bp)
      (fun m ba => by
        cases m with
        | readOnly hp bp =>
          simp only [Bool.and_eq_true]
          exact yield2_ok_iff _ _ _ _ (pushStr_ok_iff _ hp) (fun b1 => pushStr_ok_iff b1 bp)
        | readWrite hp bp =>
          simp only [Bool.and_eq_true]
          exact yield2_ok_iff _ _ _ _ (pushStr_ok_iff _ hp) (fun b1 => pushStr_ok_iff b1 bp)
        | scratch bp => exact yield1_ok_iff _ _ (pushStr_ok_iff _ bp))
      (fun m ba out => by
        cases m with
        | readOnly hp bp => exact yield2_ne_done _ _ out
        | readWrite hp bp => exact yield2_ne_done _ _ out
        | scratch bp => exact yield1_ne_done _ out) _ _)
    (fun ba _ => by
      have hp := forIn_portForwards_ok plan.portForwards (Internal.pushU32LE ba (UInt32.ofNat plan.portForwards.size))
      exact iff_true_intro hp)).trans ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

private theorem bool_eq_true_of_ne_false {b : Bool} (h : b ≠ false) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

private theorem getElem!_of_extract_eq {a tgt : ByteArray} {b e i : Nat}
    (hle : b ≤ e) (he : e ≤ a.size) (hex : a.extract b e = tgt) (hi : i < e - b) :
    a[b + i]! = tgt[i]! := by
  subst hex
  have hbe : b + (e - b) = e := by omega
  have hexData : (a.extract b e).data = a.data.extract b e := by
    simp [ByteArray.extract, ByteArray.copySlice, hbe]
  have hlt1 : b + i < a.size := by omega
  have hlt2 : i < (a.extract b e).size := by
    change i < (a.extract b e).data.size
    rw [hexData, Array.size_extract]
    have hm : min e a.data.size = e := Nat.min_eq_left he
    omega
  rw [getElem!_pos a (b + i) hlt1, getElem!_pos (a.extract b e) i hlt2]
  change a.data[b + i] = (a.extract b e).data[i]
  simp [Array.getElem_extract]

/-- `Raw.encodePlan` refines `Model.allowedEncodePlan` across all plans and seccomp byte payloads. -/
theorem refinesPure_encodePlan :
    Core.ObeysPure2 LeanSwe.ProcessSandbox.Raw.encodePlan Model.allowedEncodePlan := by
  intro plan seccompBytes
  have hinv := encodePlan_inv plan seccompBytes
  have hEq : LeanSwe.ProcessSandbox.Raw.encodePlan plan seccompBytes = Internal.encodePlan plan seccompBytes := rfl
  rw [hEq]
  unfold allowedEncodePlan
  cases hRes : Internal.encodePlan plan seccompBytes with
  | ok wire =>
    rw [hRes] at hinv
    rcases hinv with ⟨hpos, hmod, hle, hsz, hmagic, hb0, hb1, hb2, hb3, htrail⟩
    have hSec : seccompFilterBytesValid seccompBytes = true := by
      unfold seccompFilterBytesValid
      have hne : (seccompBytes.size != 0) = true := by simp [Nat.ne_of_gt hpos]
      have hm : (seccompBytes.size % 8 == 0) = true := by simp [hmod]
      have hmx : decide (seccompBytes.size ≤ 8 * SECCOMP_MAX_INSNS) = true := decide_eq_true hle
      simp [hne, hm, hmx]
    have hInvAndStr : planMandatoryInvariantsOk plan = true ∧ planStringsValid plan = true := by
      unfold Internal.encodePlan at hRes
      repeat (split at hRes; · cases hRes)
      · rename_i h1 h2 h3 h4 _
        have hMand : planMandatoryInvariantsOk plan = true := by
          unfold planMandatoryInvariantsOk
          simp only [Bool.not_eq_true', Bool.or_eq_true, decide_eq_true_eq, not_or,
            Bool.not_eq_false, beq_iff_eq] at h1 h2 h3 h4
          have hAbi : 4 ≤ plan.landlockMinAbi := by omega
          simp [h1, h2, h3, h4, hAbi]
        have hPre : ∃ pfx, Internal.encodePlanPrefix plan = .ok pfx := by
          cases hP : Internal.encodePlanPrefix plan with
          | error _ => rw [hP] at hRes; cases hRes
          | ok pfx => exact ⟨pfx, rfl⟩
        exact ⟨hMand, (encodePlanPrefix_ok_iff plan).mp hPre⟩
    have hm : ∀ (i : Nat), i < 8 → wire[i]! = ("LSWP0002".toUTF8)[i]! := fun i hi => by
      simpa only [Nat.zero_add] using getElem!_of_extract_eq (by omega) (by omega) hmagic (by omega)
    exact ⟨hInvAndStr.1, hSec, hInvAndStr.2, hsz,
      (hm 0 (by omega)).trans (by decide), (hm 1 (by omega)).trans (by decide),
      (hm 2 (by omega)).trans (by decide), (hm 3 (by omega)).trans (by decide),
      (hm 4 (by omega)).trans (by decide), (hm 5 (by omega)).trans (by decide),
      (hm 6 (by omega)).trans (by decide), (hm 7 (by omega)).trans (by decide),
      hb0, hb1, hb2, hb3,
      fun i hi => getElem!_of_extract_eq (by omega) (Nat.le_refl _) htrail (by omega)⟩
  | error err =>
    rw [hRes] at hinv
    refine ⟨hinv.1, hinv.2, ?_⟩
    by_cases hM : planMandatoryInvariantsOk plan = false
    · exact Or.inl hM
    · by_cases hS : seccompFilterBytesValid seccompBytes = false
      · exact Or.inr (Or.inl hS)
      · right; right
        have hMt : planMandatoryInvariantsOk plan = true := bool_eq_true_of_ne_false hM
        have hSt : seccompFilterBytesValid seccompBytes = true := bool_eq_true_of_ne_false hS
        cases hStr : planStringsValid plan with
        | false => rfl
        | true =>
          obtain ⟨pfx, hPfx⟩ := (encodePlanPrefix_ok_iff plan).mpr hStr
          unfold planMandatoryInvariantsOk at hMt
          unfold seccompFilterBytesValid at hSt
          simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, beq_iff_eq, decide_eq_true_eq] at hMt hSt
          unfold Internal.encodePlan at hRes
          have hc1 : (!plan.emptyRoot || !plan.unshareAllNamespaces || !plan.mountFreshProc || !plan.mountSafeDev ||
              !plan.directCgroupV2Fs || decide (plan.landlockMinAbi < 4) || !plan.blockUnixSocketAndSmc ||
              !plan.allowAnonUnixSocketpair || !plan.clone3EnosysFallback || !plan.seccompStrictDenylist ||
              !plan.noNewPrivs || !plan.rlimitCoreZero || !plan.subreaperAndPdeathsig || !plan.cleanEnv) = false := by
            have hNotLt : ¬ plan.landlockMinAbi < 4 := by omega
            simp [hMt, hNotLt]
          have hc2 : (plan.program.isEmpty || plan.cwd.isEmpty) = false := by simp [hMt]
          have hc3 : (plan.limits.timeoutMs == 0 || plan.limits.memoryMaxBytes == some 0 || plan.limits.pidsMax == some 0) = false := by
            simp [hMt]
          have hc4 : plan.portForwards.any (fun pf => pf.boxPort == 0 || pf.hostPort == 0) = false := by
            exact hMt.2
          have hc5 : (seccompBytes.size == 0 || seccompBytes.size % 8 != 0 || decide (seccompBytes.size > 8 * SECCOMP_MAX_INSNS)) = false := by
            have ha : (seccompBytes.size == 0) = false := by simp [hSt.1.1]
            have hb : (seccompBytes.size % 8 != 0) = false := by simp [hSt.1.2]
            have hc : decide (seccompBytes.size > 8 * SECCOMP_MAX_INSNS) = false := decide_eq_false (Nat.not_lt.mpr hSt.2)
            simp [ha, hb, hc]
          simp [hc1, hc2, hc3, hc4, hc5, hPfx, bind, Except.bind, pure, Except.pure] at hRes

end LeanSwe.ProcessSandbox.Raw.Proofs
