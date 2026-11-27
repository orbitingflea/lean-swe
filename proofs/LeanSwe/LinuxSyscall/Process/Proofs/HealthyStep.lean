import LeanSwe.LinuxSyscall.Process.Model

namespace LeanSwe.LinuxSyscall.Process

open LeanSwe.LinuxSyscall

/-- Soundness: every `healthyStep` transition refines `allowedStep` with `ambientSeccomp = false`, `isCriticalFault = false`, and exact `eintrBudget` accounting. -/
theorem healthyStep_implies_allowedStep
    {env env' : HealthyEnv} {req : ProcessReq} {out : ProcessOutcome}
    (h : healthyStep env req out = some env') :
    allowedStep env.state req out = some env'.state ∧
    env.wf = true ∧
    env.state.ambientSeccomp = false ∧
    isCriticalFault out = false ∧
    env'.eintrBudget ≤ env.eintrBudget ∧
    (isEintrOutcome out = true → env.eintrBudget > 0 ∧ env'.eintrBudget = env.eintrBudget - 1) ∧
    (isEintrOutcome out = false → env'.eintrBudget = env.eintrBudget) := by
  unfold healthyStep at h
  by_cases hBad : (!env.wf || isCriticalFault out) = true
  · simp [hBad] at h
  · have hWf : env.wf = true := by cases hw : env.wf <;> simp_all
    have hSec : env.state.ambientSeccomp = false := by
      unfold HealthyEnv.wf at hWf; cases hs : env.state.ambientSeccomp <;> simp_all
    have hCrit : isCriticalFault out = false := by cases hc : isCriticalFault out <;> simp_all
    simp only [hBad, Bool.false_eq_true, ↓reduceIte] at h
    cases hAl : allowedStep env.state req out with
    | none => simp [hAl] at h
    | some s' =>
      rw [hAl] at h; dsimp only at h
      cases hEi : isEintrOutcome out with
      | false =>
        simp only [hEi, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hWf, hSec, hCrit, Nat.le_refl _, (by intro hc; cases hc), fun _ => rfl⟩
      | true =>
        simp only [hEi, ↓reduceIte] at h
        by_cases hPos : env.eintrBudget > 0
        · simp only [hPos, ↓reduceIte, Option.some.injEq] at h
          subst h
          exact ⟨rfl, hWf, hSec, hCrit, Nat.sub_le _ _, fun _ => ⟨hPos, rfl⟩, (by intro hc; cases hc)⟩
        · simp [hPos] at h

/-- Tightness by construction: every non-critical `allowedStep` transition from a healthy `Process` environment (with positive `eintrBudget` on `EINTR`) is accepted by `healthyStep`. -/
theorem allowedStep_healthy_tight
    {env : HealthyEnv} {req : ProcessReq} {out : ProcessOutcome} {s' : ProcessSysState}
    (hStep : allowedStep env.state req out = some s')
    (hWf : env.wf = true)
    (hNoCrit : isCriticalFault out = false)
    (hBudget : isEintrOutcome out = true → 0 < env.eintrBudget) :
    healthyStep env req out =
      some { state := s',
             eintrBudget := if isEintrOutcome out then env.eintrBudget - 1 else env.eintrBudget } := by
  unfold healthyStep
  have hGuard : (!env.wf || isCriticalFault out) = false := by simp [hWf, hNoCrit]
  simp only [hGuard, Bool.false_eq_true, ↓reduceIte, hStep]
  cases hEi : isEintrOutcome out
  · simp
  · have hPos : env.eintrBudget > 0 := hBudget hEi
    simp [hPos]

end LeanSwe.LinuxSyscall.Process
