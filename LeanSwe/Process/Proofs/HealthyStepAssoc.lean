import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Process.Model
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Model

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall

/-- `Files.assocGet xs k = none` holds iff `k ∉ xs.map Prod.fst`. -/
theorem assocGet_none_iff_not_mem_fst {α β : Type} [DecidableEq α]
    (xs : List (α × β)) (k : α) :
    LinuxSyscall.Files.assocGet xs k = none ↔ k ∉ xs.map Prod.fst := by
  induction xs with
  | nil => simp [LinuxSyscall.Files.assocGet]
  | cons hd rest ih =>
    rcases hd with ⟨k', v⟩
    simp only [LinuxSyscall.Files.assocGet, List.map_cons, List.mem_cons, not_or]
    by_cases hEq : k' = k
    · subst hEq
      simp
    · have hNe : (k' == k) = false := beq_false_of_ne hEq
      rw [hNe]
      simp [ih, Ne.symm hEq]

/-- `(Files.assocErase xs k).map Prod.fst` equals `(xs.map Prod.fst).erase k`. -/
theorem map_fst_assocErase {α β : Type} [DecidableEq α]
    (xs : List (α × β)) (k : α) :
    (LinuxSyscall.Files.assocErase xs k).map Prod.fst = (xs.map Prod.fst).erase k := by
  rw [← List.nil_append ((xs.map Prod.fst).erase k)]
  change (LinuxSyscall.Files.assocErase xs k).map Prod.fst =
    ([] : List (α × β)).reverse.map Prod.fst ++ (xs.map Prod.fst).erase k
  unfold LinuxSyscall.Files.assocErase
  generalize ([] : List (α × β)) = acc
  induction xs generalizing acc with
  | nil =>
    change acc.reverse.map Prod.fst = _
    simp
  | cons hd rest ih =>
    rcases hd with ⟨k', v⟩
    change (if k' == k then acc.reverseAux rest else _).map Prod.fst = _
    by_cases hEq : (k' == k) = true
    · simp [hEq, List.erase_cons, List.reverseAux_eq]
    · have hF : (k' == k) = false := Bool.eq_false_iff.mpr hEq
      rw [ite_eq_right hEq]
      simp only [List.map_cons, List.erase_cons, hF, Bool.false_eq_true, ↓reduceIte, ih]
      simp [List.reverse_cons, List.map_append]

/-- `Files.assocErase` commutes with value mapping `Prod.map id f`. -/
theorem assocErase_map_val {α β γ : Type} [DecidableEq α]
    (xs : List (α × β)) (f : β → γ) (k : α) :
    LinuxSyscall.Files.assocErase (xs.map fun (a, b) => (a, f b)) k =
      (LinuxSyscall.Files.assocErase xs k).map fun (a, b) => (a, f b) := by
  have hInit : ([] : List (α × γ)) = ([] : List (α × β)).map fun (a, b) => (a, f b) := rfl
  unfold LinuxSyscall.Files.assocErase
  rw [hInit]
  generalize ([] : List (α × β)) = acc
  induction xs generalizing acc with
  | nil =>
    change (List.map (fun (a, b) => (a, f b)) acc).reverse =
      List.map (fun (a, b) => (a, f b)) acc.reverse
    simp [List.map_reverse]
  | cons hd rest ih =>
    rcases hd with ⟨k', v⟩
    simp only [List.map_cons]
    change (if k' == k then (acc.map fun (a, b) => (a, f b)).reverseAux (rest.map fun (a, b) => (a, f b)) else _) =
      List.map (fun (a, b) => (a, f b)) (if k' == k then acc.reverseAux rest else _)
    by_cases hEq : (k' == k) = true
    · simp [hEq, List.reverseAux_eq, List.map_reverse]
    · rw [ite_eq_right hEq, ite_eq_right hEq]
      exact ih ((k', v) :: acc)

/-- `Files.assocSet` commutes with value mapping `Prod.map id f`. -/
theorem assocSet_map_val {α β γ : Type} [DecidableEq α]
    (xs : List (α × β)) (f : β → γ) (k : α) (v : β) :
    LinuxSyscall.Files.assocSet (xs.map fun (a, b) => (a, f b)) k (f v) =
      (LinuxSyscall.Files.assocSet xs k v).map fun (a, b) => (a, f b) := by
  have hInit : ([] : List (α × γ)) = ([] : List (α × β)).map fun (a, b) => (a, f b) := rfl
  unfold LinuxSyscall.Files.assocSet
  rw [hInit]
  generalize ([] : List (α × β)) = acc
  induction xs generalizing acc with
  | nil =>
    change (acc.map fun (a, b) => (a, f b)).reverseAux [(k, f v)] =
      List.map (fun (a, b) => (a, f b)) (acc.reverseAux [(k, v)])
    simp [List.reverseAux_eq, List.map_reverse]
  | cons hd rest ih =>
    rcases hd with ⟨k', v'⟩
    simp only [List.map_cons]
    change (if k' == k then (acc.map fun (a, b) => (a, f b)).reverseAux ((k, f v) :: rest.map fun (a, b) => (a, f b)) else _) =
      List.map (fun (a, b) => (a, f b)) (if k' == k then acc.reverseAux ((k, v) :: rest) else _)
    by_cases hEq : (k' == k) = true
    · simp [hEq, List.reverseAux_eq, List.map_reverse]
    · rw [ite_eq_right hEq, ite_eq_right hEq]
      exact ih ((k', v') :: acc)

/-- Replacing an existing key `k ∈ xs.map Prod.fst` via `Files.assocSet` preserves `map Prod.fst` identically. -/
theorem map_fst_assocSet_of_mem {α β : Type} [DecidableEq α]
    (xs : List (α × β)) (k : α) (v : β) (hMem : k ∈ xs.map Prod.fst) :
    (LinuxSyscall.Files.assocSet xs k v).map Prod.fst = xs.map Prod.fst := by
  rw [← List.nil_append (xs.map Prod.fst)]
  change (LinuxSyscall.Files.assocSet xs k v).map Prod.fst =
    ([] : List (α × β)).reverse.map Prod.fst ++ xs.map Prod.fst
  unfold LinuxSyscall.Files.assocSet
  generalize ([] : List (α × β)) = acc
  induction xs generalizing acc with
  | nil => simp at hMem
  | cons hd rest ih =>
    rcases hd with ⟨k', v'⟩
    change (if k' == k then acc.reverseAux ((k, v) :: rest) else _).map Prod.fst = _
    by_cases hEq : (k' == k) = true
    · have hk : k' = k := beq_iff_eq.mp hEq
      subst hk
      simp [List.reverseAux_eq]
    · rw [ite_eq_right hEq]
      have hkNe : k ≠ k' := fun h => hEq (beq_iff_eq.mpr h.symm)
      have hMemRest : k ∈ rest.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons] at hMem
        exact hMem.resolve_left hkNe
      rw [ih hMemRest ((k', v') :: acc)]
      simp [List.reverse_cons, List.map_append]

/-- Every `LinuxSyscall.Process.healthyStep` excludes critical OS faults. -/
theorem proc_healthyStep_noCrit
    {env env' : LinuxSyscall.Process.HealthyEnv}
    {req : LinuxSyscall.Process.ProcessReq} {out : LinuxSyscall.Process.ProcessOutcome}
    (h : LinuxSyscall.Process.healthyStep env req out = some env') :
    LinuxSyscall.Process.isCriticalFault out = false := by
  unfold LinuxSyscall.Process.healthyStep at h
  cases hc : LinuxSyscall.Process.isCriticalFault out <;> simp_all

/-- Decompose `LinuxSyscall.Files.healthyStep` into `allowedStep`, no seccomp, no critical fault, and no `.close`/`EBUSY`. -/
theorem files_healthyStep_props
    {env env' : LinuxSyscall.Files.HealthyEnv}
    {req : LinuxSyscall.Files.FilesReq} {out : LinuxSyscall.Files.FilesOutcome}
    (h : LinuxSyscall.Files.healthyStep env req out = some env') :
    LinuxSyscall.Files.allowedStep env.state req out = some env'.state ∧
    env.state.ambientSeccomp = false ∧
    LinuxSyscall.Files.isCriticalFault out = false ∧
    LinuxSyscall.Files.isCloseEbusy req out = false := by
  unfold LinuxSyscall.Files.healthyStep at h
  by_cases hBad : (!env.wf || LinuxSyscall.Files.isCriticalFault out ||
      LinuxSyscall.Files.isCloseEbusy req out) = true
  · simp [hBad] at h
  · have hWf : env.wf = true := by cases hw : env.wf <;> simp_all
    have hSec : env.state.ambientSeccomp = false := by
      unfold LinuxSyscall.Files.HealthyEnv.wf at hWf
      cases hs : env.state.ambientSeccomp <;> simp_all
    have hCrit : LinuxSyscall.Files.isCriticalFault out = false := by
      cases hc : LinuxSyscall.Files.isCriticalFault out <;> simp_all
    have hBusy : LinuxSyscall.Files.isCloseEbusy req out = false := by
      cases hb : LinuxSyscall.Files.isCloseEbusy req out <;> simp_all
    simp only [hBad, Bool.false_eq_true, ↓reduceIte] at h
    cases hAl : LinuxSyscall.Files.allowedStep env.state req out with
    | none => simp [hAl] at h
    | some s' =>
      rw [hAl] at h; dsimp only at h
      cases hEi : LinuxSyscall.Files.isEintrOutcome out with
      | false =>
        simp only [hEi, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h; exact ⟨rfl, hSec, hCrit, hBusy⟩
      | true =>
        simp only [hEi, ↓reduceIte] at h
        by_cases hPos : env.eintrBudget > 0
        · simp only [hPos, ↓reduceIte, Option.some.injEq] at h
          subst h; exact ⟨rfl, hSec, hCrit, hBusy⟩
        · simp [hPos] at h

/-- Under canonical `LinuxSyscall.Files.healthyStep` (excluding `.close`/`EBUSY` and `ambientSeccomp`), every `.close hid` transition erases `hid` from `state.fds.map Prod.fst`. -/
theorem healthyFilesStep_close_fds
    {env env' : LinuxSyscall.Files.HealthyEnv}
    {hid : LinuxSyscall.Files.HandleId} {out : LinuxSyscall.Files.FilesOutcome}
    (h : LinuxSyscall.Files.healthyStep env (.close hid) out = some env') :
    env'.state.fds.map Prod.fst = (env.state.fds.map Prod.fst).erase hid := by
  obtain ⟨hStep, hSec, _, hNoBusy⟩ := files_healthyStep_props h
  unfold LinuxSyscall.Files.allowedStep LinuxSyscall.Files.allowedCloseStep at hStep
  dsimp only at hStep
  cases hGet : LinuxSyscall.Files.assocGet env.state.fds hid with
  | none =>
    rw [hGet] at hStep
    unfold LinuxSyscall.Files.verifyStep at hStep
    dsimp only at hStep
    by_cases hEb : LinuxSyscall.Files.isOutcomeErr out Errno.EBADF = true
    · rw [ite_eq_left hEb] at hStep
      injection hStep with hEq
      rw [← hEq]
      have hNotMem := (assocGet_none_iff_not_mem_fst env.state.fds hid).mp hGet
      exact (List.erase_of_not_mem hNotMem).symm
    · rw [ite_eq_right hEb] at hStep
      cases hStep
  | some desc =>
    rw [hGet] at hStep
    cases out with
    | unit =>
      simp only [Option.some.injEq] at hStep
      rw [← hStep]
      have hFds : (LinuxSyscall.Files.closeDescInState env.state hid desc).fds =
          LinuxSyscall.Files.assocErase env.state.fds hid := rfl
      rw [hFds, map_fst_assocErase]
    | err e =>
      dsimp only [LinuxSyscall.Files.isCloseEbusy] at hNoBusy
      simp only [hNoBusy, hSec, Bool.not_false, Bool.and_true, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte] at hStep
      cases hK : LinuxSyscall.Files.isKernelCloseErr e
      · simp [hK] at hStep
      · simp only [hK, ↓reduceIte] at hStep
        cases hEb : e == Errno.EBADF
        · simp only [hEb, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hStep
          rw [← hStep]
          exact map_fst_assocErase env.state.fds hid
        · simp [hEb] at hStep
    | opened _ | bytes _ | u32 _ | u64 _ | statted _ =>
      cases hStep

end LeanSwe.Process.Proofs
