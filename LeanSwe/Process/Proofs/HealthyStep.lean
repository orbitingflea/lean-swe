import Core.NondetTest
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Process.Model
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Model
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.LinuxSyscall.TimeRand.Model
import LeanSwe.PostFork.Types
import LeanSwe.PostFork.Model
import LeanSwe.Process.Types
import LeanSwe.Process.SysBridge

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process
open LeanSwe.Process.SysBridge

/-!
Canonical relational `healthyStep` definitions, tightness and `close` descriptor-erasure theorems,
per-layer `RefinesHealthy*At` contracts, `refinesHealthySysDeps_of_components`, and `RawProcessLaws`
with full process-slot and OS pipe file-descriptor (`openFds`) conservation.
-/

/-- Curated catastrophic host OS faults (`ENOMEM`, `EIO`, `ENFILE`) excluded by `healthyStep`. -/
def isCriticalOsErrno (e : Errno) : Bool :=
  e == Errno.ENOMEM || e == Errno.EIO || e == Errno.ENFILE

/-- Everyday process/filesystem resource-limit errnos (`EMFILE`, `ENOSPC`) retained inside `healthyStep`. -/
def isResourceLimitErrno (e : Errno) : Bool :=
  e == Errno.EMFILE || e == Errno.ENOSPC

/-- Everyday resource-limit errnos (`EMFILE`, `ENOSPC`) are strictly disjoint from `isCriticalOsErrno`. -/
theorem resourceLimit_disjoint_criticalOs (e : Errno)
    (h : isResourceLimitErrno e = true) :
    isCriticalOsErrno e = false := by
  simp only [isResourceLimitErrno, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> decide

/-- Return `true` iff `(req, out)` is `.close _` failing with `Errno.EBUSY` (impossible in sequential `StateM` where `in_flight = 0`). -/
def isFilesCloseEbusy (req : LinuxSyscall.Files.FilesReq) (out : LinuxSyscall.Files.FilesOutcome) : Bool :=
  match req, out with
  | .close _, .err code => code == Errno.EBUSY
  | _, _ => false

/-- Healthy kernel environment pairing a model state `state` with a finite `EINTR` budget. -/
structure HealthyEnv (Sys : Type) where
  /-- Underlying syscall model state (`ambientSeccomp = false`). -/
  state : Sys
  /-- Remaining bounded `EINTR` retry budget. -/
  eintrBudget : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Relational `healthyStep` for `LinuxSyscall.Process`: refines `allowedStep` without `ambientSeccomp` or `isCriticalOsErrno`, consuming `eintrBudget` on `EINTR`. -/
def healthyProcessStep (s : LinuxSyscall.Process.ProcessSysState) (eintrBudget : Nat)
    (req : LinuxSyscall.Process.ProcessReq) (out : LinuxSyscall.Process.ProcessOutcome) :
    Option (LinuxSyscall.Process.ProcessSysState × Nat) :=
  if s.ambientSeccomp then none
  else
    match LinuxSyscall.Process.allowedStep s req out with
    | none => none
    | some s' =>
      match out with
      | .err code =>
        if isCriticalOsErrno code then none
        else if code == Errno.EINTR then
          if eintrBudget == 0 then none else some (s', eintrBudget - 1)
        else
          some (s', eintrBudget)
      | _ => some (s', eintrBudget)

/-- Soundness: every `healthyProcessStep` transition is a valid `LinuxSyscall.Process.allowedStep` transition with non-increasing `EINTR` budget. -/
theorem healthyProcessStep_implies_allowedStep
    {s s' : LinuxSyscall.Process.ProcessSysState} {b b' : Nat}
    {req : LinuxSyscall.Process.ProcessReq} {out : LinuxSyscall.Process.ProcessOutcome}
    (h : healthyProcessStep s b req out = some (s', b')) :
    LinuxSyscall.Process.allowedStep s req out = some s' ∧
    s.ambientSeccomp = false ∧
    b' ≤ b ∧
    (∀ code, out = .err code → isCriticalOsErrno code = false ∧ (code = Errno.EINTR → b' < b)) := by
  unfold healthyProcessStep at h
  cases hSec : s.ambientSeccomp
  · simp only [hSec, Bool.false_eq_true, ↓reduceIte] at h
    cases hStep : LinuxSyscall.Process.allowedStep s req out with
    | none => simp [hStep] at h
    | some st =>
      simp only [hStep] at h
      cases out with
      | err code =>
        simp only at h
        cases hCrit : isCriticalOsErrno code
        · simp only [hCrit, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hEi : code = Errno.EINTR
          · subst hEi
            simp only [beq_self_eq_true, ↓reduceIte] at h
            cases b with
            | zero => simp at h
            | succ n =>
              simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte,
                Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨rfl, rfl, by omega, ?_⟩
              intro c hc
              injection hc with hEq
              subst hEq
              exact ⟨hCrit, fun _ => by omega⟩
          · have hEiF : (code == Errno.EINTR) = false := beq_false_of_ne hEi
            simp only [hEiF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨rfl, rfl, Nat.le_refl _, ?_⟩
            intro c hc
            injection hc with hEq
            subst hEq
            exact ⟨hCrit, fun hContra => absurd hContra hEi⟩
        · simp [hCrit] at h
      | piped _ _ | waited _ | opened _ | u32 _ | unit =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl, Nat.le_refl _, fun _ hc => by cases hc⟩
  · simp [hSec] at h

/-- Tightness by construction: every non-critical `LinuxSyscall.Process.allowedStep` transition under `ambientSeccomp = false` (with positive budget on `EINTR`) is accepted by `healthyProcessStep`. -/
theorem allowedStep_healthyProcess_tight
    {s s' : LinuxSyscall.Process.ProcessSysState} {b : Nat}
    {req : LinuxSyscall.Process.ProcessReq} {out : LinuxSyscall.Process.ProcessOutcome}
    (hHealthy : s.ambientSeccomp = false)
    (hNoCrit : ∀ code, out = .err code → isCriticalOsErrno code = false ∧ (code = Errno.EINTR → 0 < b))
    (hStep : LinuxSyscall.Process.allowedStep s req out = some s') :
    ∃ b', healthyProcessStep s b req out = some (s', b') := by
  unfold healthyProcessStep
  simp only [hHealthy, Bool.false_eq_true, ↓reduceIte, hStep]
  cases out with
  | err code =>
    obtain ⟨hCrit, hBud⟩ := hNoCrit code rfl
    simp only [hCrit, Bool.false_eq_true, ↓reduceIte]
    by_cases hEi : code = Errno.EINTR
    · subst hEi
      have hPos := hBud rfl
      have hNe : (b == 0) = false := beq_false_of_ne (by omega)
      simp [hNe]
    · simp [beq_false_of_ne hEi]
  | piped _ _ | waited _ | opened _ | u32 _ | unit =>
    exact ⟨b, rfl⟩

/-- Canonical relational `healthyStep` for `LinuxSyscall.Files`: refines `allowedStep` without `ambientSeccomp`, `isCriticalOsErrno`, or `.close`/`EBUSY` (`isFilesCloseEbusy`), consuming `eintrBudget` on `EINTR` while retaining all short `read`/`write` and everyday errors (`EMFILE`, `ENOSPC`, `EAGAIN`, `EPIPE`, `ENOENT`, `EACCES`). -/
def healthyFilesStep (s : LinuxSyscall.Files.FilesState) (eintrBudget : Nat)
    (req : LinuxSyscall.Files.FilesReq) (out : LinuxSyscall.Files.FilesOutcome) :
    Option (LinuxSyscall.Files.FilesState × Nat) :=
  if s.ambientSeccomp || isFilesCloseEbusy req out then none
  else
    match LinuxSyscall.Files.allowedStep s req out with
    | none => none
    | some s' =>
      match out with
      | .err code =>
        if isCriticalOsErrno code then none
        else if code == Errno.EINTR then
          if eintrBudget == 0 then none else some (s', eintrBudget - 1)
        else
          some (s', eintrBudget)
      | _ => some (s', eintrBudget)

/-- Soundness: every `healthyFilesStep` transition refines `LinuxSyscall.Files.allowedStep` with `ambientSeccomp = false`, `isFilesCloseEbusy = false`, and non-increasing `EINTR` budget. -/
theorem healthyFilesStep_implies_allowedStep
    {s s' : LinuxSyscall.Files.FilesState} {b b' : Nat}
    {req : LinuxSyscall.Files.FilesReq} {out : LinuxSyscall.Files.FilesOutcome}
    (h : healthyFilesStep s b req out = some (s', b')) :
    LinuxSyscall.Files.allowedStep s req out = some s' ∧
    s.ambientSeccomp = false ∧
    isFilesCloseEbusy req out = false ∧
    b' ≤ b ∧
    (∀ code, out = .err code → isCriticalOsErrno code = false ∧ (code = Errno.EINTR → b' < b)) := by
  unfold healthyFilesStep at h
  cases hSec : s.ambientSeccomp
  · cases hBusy : isFilesCloseEbusy req out
    · simp only [hSec, hBusy, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at h
      cases hStep : LinuxSyscall.Files.allowedStep s req out with
      | none => simp [hStep] at h
      | some st =>
        simp only [hStep] at h
        cases out with
        | err code =>
          simp only at h
          cases hCrit : isCriticalOsErrno code
          · simp only [hCrit, Bool.false_eq_true, ↓reduceIte] at h
            by_cases hEi : code = Errno.EINTR
            · subst hEi
              simp only [beq_self_eq_true, ↓reduceIte] at h
              cases b with
              | zero => simp at h
              | succ n =>
                simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte,
                  Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                refine ⟨rfl, rfl, rfl, by omega, ?_⟩
                intro c hc
                injection hc with hEq
                subst hEq
                exact ⟨hCrit, fun _ => by omega⟩
            · have hEiF : (code == Errno.EINTR) = false := beq_false_of_ne hEi
              simp only [hEiF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨rfl, rfl, rfl, Nat.le_refl _, ?_⟩
              intro c hc
              injection hc with hEq
              subst hEq
              exact ⟨hCrit, fun hContra => absurd hContra hEi⟩
          · simp [hCrit] at h
        | opened _ | unit | bytes _ | u32 _ | u64 _ | statted _ =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, rfl, rfl, Nat.le_refl _, fun _ hc => by cases hc⟩
    · simp [hSec, hBusy] at h
  · simp [hSec] at h

/-- Tightness by construction: every non-critical, non-close-`EBUSY` `LinuxSyscall.Files.allowedStep` transition under `ambientSeccomp = false` (with positive budget on `EINTR`) is accepted by `healthyFilesStep`. -/
theorem allowedStep_healthyFiles_tight
    {s s' : LinuxSyscall.Files.FilesState} {b : Nat}
    {req : LinuxSyscall.Files.FilesReq} {out : LinuxSyscall.Files.FilesOutcome}
    (hHealthy : s.ambientSeccomp = false)
    (hNoBusy : isFilesCloseEbusy req out = false)
    (hNoCrit : ∀ code, out = .err code → isCriticalOsErrno code = false ∧ (code = Errno.EINTR → 0 < b))
    (hStep : LinuxSyscall.Files.allowedStep s req out = some s') :
    ∃ b', healthyFilesStep s b req out = some (s', b') := by
  unfold healthyFilesStep
  simp only [hHealthy, hNoBusy, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hStep]
  cases out with
  | err code =>
    obtain ⟨hCrit, hBud⟩ := hNoCrit code rfl
    simp only [hCrit, Bool.false_eq_true, ↓reduceIte]
    by_cases hEi : code = Errno.EINTR
    · subst hEi
      have hPos := hBud rfl
      have hNe : (b == 0) = false := beq_false_of_ne (by omega)
      simp [hNe]
    · simp [beq_false_of_ne hEi]
  | opened _ | unit | bytes _ | u32 _ | u64 _ | statted _ =>
    exact ⟨b, rfl⟩

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

/-- Under canonical `healthyFilesStep` (excluding `.close`/`EBUSY` and `ambientSeccomp`), **every** `.close hid` transition erases `hid` from `s.fds.map Prod.fst`! -/
theorem healthyFilesStep_close_fds
    {s s' : LinuxSyscall.Files.FilesState} {b b' : Nat}
    {hid : LinuxSyscall.Files.HandleId} {out : LinuxSyscall.Files.FilesOutcome}
    (h : healthyFilesStep s b (.close hid) out = some (s', b')) :
    s'.fds.map Prod.fst = (s.fds.map Prod.fst).erase hid := by
  obtain ⟨hStep, hSec, hNoBusy, _, _⟩ := healthyFilesStep_implies_allowedStep h
  unfold LinuxSyscall.Files.allowedStep LinuxSyscall.Files.allowedCloseStep at hStep
  dsimp only at hStep
  cases hGet : LinuxSyscall.Files.assocGet s.fds hid with
  | none =>
    rw [hGet] at hStep
    unfold LinuxSyscall.Files.verifyStep at hStep
    dsimp only at hStep
    by_cases hEb : LinuxSyscall.Files.isOutcomeErr out Errno.EBADF = true
    · rw [ite_eq_left hEb] at hStep
      injection hStep with hEq
      subst hEq
      have hNotMem := (assocGet_none_iff_not_mem_fst s.fds hid).mp hGet
      exact (List.erase_of_not_mem hNotMem).symm
    · rw [ite_eq_right hEb] at hStep
      cases hStep
  | some desc =>
    rw [hGet] at hStep
    cases out with
    | unit =>
      simp only [Option.some.injEq] at hStep
      subst hStep
      have hFds : (LinuxSyscall.Files.closeDescInState s hid desc).fds =
          LinuxSyscall.Files.assocErase s.fds hid := rfl
      rw [hFds, map_fst_assocErase]
    | err e =>
      dsimp only [isFilesCloseEbusy] at hNoBusy
      simp only [hNoBusy, hSec, Bool.not_false, Bool.and_true, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte] at hStep
      cases hK : LinuxSyscall.Files.isKernelCloseErr e
      · simp [hK] at hStep
      · simp only [hK, ↓reduceIte] at hStep
        cases hEb : e == Errno.EBADF
        · simp only [hEb, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hStep
          subst hStep
          exact map_fst_assocErase s.fds hid
        · simp [hEb] at hStep
    | opened _ | bytes _ | u32 _ | u64 _ | statted _ =>
      cases hStep

/-- Relational `healthyStep` for `LinuxSyscall.TimeRand`: refines `allowedStep` without `ambientSeccomp` or `isCriticalOsErrno`, consuming `eintrBudget` on `EINTR`. -/
def healthyTimeRandStep (s : LinuxSyscall.TimeRand.TimeRandState) (eintrBudget : Nat)
    (req : LinuxSyscall.TimeRand.TimeRandReq) (out : LinuxSyscall.TimeRand.TimeRandOutcome) :
    Option (LinuxSyscall.TimeRand.TimeRandState × Nat) :=
  if s.ambientSeccomp then none
  else
    match LinuxSyscall.TimeRand.allowedStep s req out with
    | none => none
    | some s' =>
      match out with
      | .err code =>
        if isCriticalOsErrno code then none
        else if code == Errno.EINTR then
          if eintrBudget == 0 then none else some (s', eintrBudget - 1)
        else
          some (s', eintrBudget)
      | _ => some (s', eintrBudget)

/-- Soundness: every `healthyTimeRandStep` transition refines `LinuxSyscall.TimeRand.allowedStep` with non-increasing `EINTR` budget. -/
theorem healthyTimeRandStep_implies_allowedStep
    {s s' : LinuxSyscall.TimeRand.TimeRandState} {b b' : Nat}
    {req : LinuxSyscall.TimeRand.TimeRandReq} {out : LinuxSyscall.TimeRand.TimeRandOutcome}
    (h : healthyTimeRandStep s b req out = some (s', b')) :
    LinuxSyscall.TimeRand.allowedStep s req out = some s' ∧
    s.ambientSeccomp = false ∧
    b' ≤ b ∧
    (∀ code, out = .err code → isCriticalOsErrno code = false ∧ (code = Errno.EINTR → b' < b)) := by
  unfold healthyTimeRandStep at h
  cases hSec : s.ambientSeccomp
  · simp only [hSec, Bool.false_eq_true, ↓reduceIte] at h
    cases hStep : LinuxSyscall.TimeRand.allowedStep s req out with
    | none => simp [hStep] at h
    | some st =>
      simp only [hStep] at h
      cases out with
      | err code =>
        simp only at h
        cases hCrit : isCriticalOsErrno code
        · simp only [hCrit, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hEi : code = Errno.EINTR
          · subst hEi
            simp only [beq_self_eq_true, ↓reduceIte] at h
            cases b with
            | zero => simp at h
            | succ n =>
              simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte,
                Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨rfl, rfl, by omega, ?_⟩
              intro c hc
              injection hc with hEq
              subst hEq
              exact ⟨hCrit, fun _ => by omega⟩
          · have hEiF : (code == Errno.EINTR) = false := beq_false_of_ne hEi
            simp only [hEiF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨rfl, rfl, Nat.le_refl _, ?_⟩
            intro c hc
            injection hc with hEq
            subst hEq
            exact ⟨hCrit, fun hContra => absurd hContra hEi⟩
        · simp [hCrit] at h
      | unit | timespec _ | bytes _ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl, Nat.le_refl _, fun _ hc => by cases hc⟩
  · simp [hSec] at h

/-- Tightness by construction: every non-critical `LinuxSyscall.TimeRand.allowedStep` transition under `ambientSeccomp = false` (with positive budget on `EINTR`) is accepted by `healthyTimeRandStep`. -/
theorem allowedStep_healthyTimeRand_tight
    {s s' : LinuxSyscall.TimeRand.TimeRandState} {b : Nat}
    {req : LinuxSyscall.TimeRand.TimeRandReq} {out : LinuxSyscall.TimeRand.TimeRandOutcome}
    (hHealthy : s.ambientSeccomp = false)
    (hNoCrit : ∀ code, out = .err code → isCriticalOsErrno code = false ∧ (code = Errno.EINTR → 0 < b))
    (hStep : LinuxSyscall.TimeRand.allowedStep s req out = some s') :
    ∃ b', healthyTimeRandStep s b req out = some (s', b') := by
  unfold healthyTimeRandStep
  simp only [hHealthy, Bool.false_eq_true, ↓reduceIte, hStep]
  cases out with
  | err code =>
    obtain ⟨hCrit, hBud⟩ := hNoCrit code rfl
    simp only [hCrit, Bool.false_eq_true, ↓reduceIte]
    by_cases hEi : code = Errno.EINTR
    · subst hEi
      have hPos := hBud rfl
      have hNe : (b == 0) = false := beq_false_of_ne (by omega)
      simp [hNe]
    · simp [beq_false_of_ne hEi]
  | unit | timespec _ | bytes _ =>
    exact ⟨b, rfl⟩

/-- Under `healthyTimeRandStep`, `clock_gettime` never fails with `.err` (since `ambientSeccomp = false`). -/
theorem healthyTimeRandStep_clock_gettime_never_err
    (s : LinuxSyscall.TimeRand.TimeRandState) (b : Nat)
    (clk : LinuxSyscall.TimeRand.ClockId) (e : Errno) :
    healthyTimeRandStep s b (.clock_gettime clk) (.err e) = none := by
  unfold healthyTimeRandStep
  cases hSec : s.ambientSeccomp
  · simp [LinuxSyscall.TimeRand.allowedStep, LinuxSyscall.TimeRand.allowedStepCore, hSec]
  · simp

/-- Universal refinement predicate for `LinuxSyscall.Process.ProcessOpsM (StateM S) fd` against `healthyProcessStep`. -/
structure RefinesHealthyProcessAt {S fd : Type}
    (proj : S → HealthyEnv LinuxSyscall.Process.ProcessSysState)
    (toHid : fd → LinuxSyscall.Process.HandleId)
    (ops : LinuxSyscall.Process.ProcessOpsM (StateM S) fd) : Prop where
  /-- `pipe2` transitions via `healthyProcessStep` and yields distinct descriptors on `.ok`. -/
  pipe2_healthy : ∀ s flags, (proj s).state.ambientSeccomp = false →
    let r := (ops.pipe2 flags).run s
    let out : LinuxSyscall.Process.ProcessOutcome :=
      match r.1 with | .ok (rf, wf) => .piped (toHid rf) (toHid wf) | .error e => .err e
    healthyProcessStep (proj s).state (proj s).eintrBudget (.pipe2 flags) out =
      some ((proj r.2).state, (proj r.2).eintrBudget) ∧
    (proj r.2).state.ambientSeccomp = false
  /-- `waitpid` transitions via `healthyProcessStep`. -/
  waitpid_healthy : ∀ s pid flags, (proj s).state.ambientSeccomp = false →
    let r := (ops.waitpid pid flags).run s
    let out : LinuxSyscall.Process.ProcessOutcome :=
      match r.1 with | .ok wr => .waited wr | .error e => .err e
    healthyProcessStep (proj s).state (proj s).eintrBudget (.waitpid pid flags) out =
      some ((proj r.2).state, (proj r.2).eintrBudget) ∧
    (proj r.2).state.ambientSeccomp = false
  /-- `kill` transitions via `healthyProcessStep`. -/
  kill_healthy : ∀ s target sig, (proj s).state.ambientSeccomp = false →
    let r := (ops.kill target sig).run s
    let out : LinuxSyscall.Process.ProcessOutcome :=
      match r.1 with | .ok () => .unit | .error e => .err e
    healthyProcessStep (proj s).state (proj s).eintrBudget (.kill target sig) out =
      some ((proj r.2).state, (proj r.2).eintrBudget) ∧
    (proj r.2).state.ambientSeccomp = false

/-- Universal refinement predicate for `LinuxSyscall.Files.FilesOpsM (StateM S) fd` against canonical `healthyFilesStep` on all operations consumed by `SysBridge`. -/
structure RefinesHealthyFilesAt {S fd : Type}
    (proj : S → HealthyEnv LinuxSyscall.Files.FilesState)
    (toHid : fd → LinuxSyscall.Files.HandleId)
    (ops : LinuxSyscall.Files.FilesOpsM (StateM S) fd) : Prop where
  /-- `close` transitions via `healthyFilesStep` (which excludes `EBUSY` and erases `toHid h` from `fds`). -/
  close_healthy : ∀ s h, (proj s).state.ambientSeccomp = false →
    let r := (ops.close h).run s
    let out : LinuxSyscall.Files.FilesOutcome :=
      match r.1 with | .ok () => .unit | .error e => .err e
    healthyFilesStep (proj s).state (proj s).eintrBudget (.close (toHid h)) out =
      some ((proj r.2).state, (proj r.2).eintrBudget) ∧
    (proj r.2).state.ambientSeccomp = false
  /-- `read` transitions via `healthyFilesStep` (permitting short pipe reads `0 ≤ chunk.size ≤ cap`, `EAGAIN`, and bounded `EINTR`). -/
  read_healthy : ∀ s h cap, (proj s).state.ambientSeccomp = false →
    let r := (ops.read h cap).run s
    let out : LinuxSyscall.Files.FilesOutcome :=
      match r.1 with | .ok bs => .bytes bs | .error e => .err e
    healthyFilesStep (proj s).state (proj s).eintrBudget (.read (toHid h) cap) out =
      some ((proj r.2).state, (proj r.2).eintrBudget) ∧
    (proj r.2).state.ambientSeccomp = false ∧
    (∀ bs, r.1 = .ok bs → bs.size ≤ cap.toNat)
  /-- `write` transitions via `healthyFilesStep` (permitting short pipe writes `0 ≤ n ≤ data.size`, `EAGAIN`, `EPIPE`, and bounded `EINTR`). -/
  write_healthy : ∀ s h data, (proj s).state.ambientSeccomp = false →
    let r := (ops.write h data).run s
    let out : LinuxSyscall.Files.FilesOutcome :=
      match r.1 with | .ok n => .u32 n | .error e => .err e
    healthyFilesStep (proj s).state (proj s).eintrBudget (.write (toHid h) data) out =
      some ((proj r.2).state, (proj r.2).eintrBudget) ∧
    (proj r.2).state.ambientSeccomp = false ∧
    (∀ n, r.1 = .ok n → n.toNat ≤ data.size)
  /-- `fstatat` transitions via `healthyFilesStep`. -/
  fstatat_healthy : ∀ s dir path flags, (proj s).state.ambientSeccomp = false →
    let r := (ops.fstatat dir path flags).run s
    let out : LinuxSyscall.Files.FilesOutcome :=
      match r.1 with | .ok st => .statted st | .error e => .err e
    healthyFilesStep (proj s).state (proj s).eintrBudget (.fstatat (dir.map toHid) path flags) out =
      some ((proj r.2).state, (proj r.2).eintrBudget) ∧
    (proj r.2).state.ambientSeccomp = false
  /-- `faccessat` transitions via `healthyFilesStep`. -/
  faccessat_healthy : ∀ s dir path mask flags, (proj s).state.ambientSeccomp = false →
    let r := (ops.faccessat dir path mask flags).run s
    let out : LinuxSyscall.Files.FilesOutcome :=
      match r.1 with | .ok () => .unit | .error e => .err e
    healthyFilesStep (proj s).state (proj s).eintrBudget (.faccessat (dir.map toHid) path mask flags) out =
      some ((proj r.2).state, (proj r.2).eintrBudget) ∧
    (proj r.2).state.ambientSeccomp = false
  /-- `fcntl` transitions via `healthyFilesStep`. -/
  fcntl_healthy : ∀ s h cmd, (proj s).state.ambientSeccomp = false →
    let r := (ops.fcntl h cmd).run s
    let out : LinuxSyscall.Files.FilesOutcome :=
      match r.1 with | .ok v => .u32 v | .error e => .err e
    healthyFilesStep (proj s).state (proj s).eintrBudget (.fcntl (toHid h) cmd) out =
      some ((proj r.2).state, (proj r.2).eintrBudget) ∧
    (proj r.2).state.ambientSeccomp = false

/-- Universal refinement predicate for `LinuxSyscall.TimeRand.TimeRandOpsM (StateM S)` against `healthyTimeRandStep`. -/
structure RefinesHealthyTimeRandAt {S : Type}
    (proj : S → HealthyEnv LinuxSyscall.TimeRand.TimeRandState)
    (ops : LinuxSyscall.TimeRand.TimeRandOpsM (StateM S)) : Prop where
  /-- `clock_gettime` transitions via `healthyTimeRandStep` (always succeeding when `ambientSeccomp = false`). -/
  clock_gettime_healthy : ∀ s clk, (proj s).state.ambientSeccomp = false →
    let r := (ops.clock_gettime clk).run s
    healthyTimeRandStep (proj s).state (proj s).eintrBudget (.clock_gettime clk)
      (LinuxSyscall.TimeRand.outcomeOfTimespec r.1) =
      some ((proj r.2).state, (proj r.2).eintrBudget) ∧
    (proj r.2).state.ambientSeccomp = false
  /-- `clock_nanosleep` transitions via `healthyTimeRandStep`. -/
  clock_nanosleep_healthy : ∀ s clk abs req, (proj s).state.ambientSeccomp = false →
    let r := (ops.clock_nanosleep clk abs req).run s
    healthyTimeRandStep (proj s).state (proj s).eintrBudget (.clock_nanosleep clk abs req)
      (LinuxSyscall.TimeRand.outcomeOfUnit r.1) =
      some ((proj r.2).state, (proj r.2).eintrBudget) ∧
    (proj r.2).state.ambientSeccomp = false

/-- Universal refinement predicate for `PostFork.PostForkOpsM (StateM S) fd` under a healthy kernel. -/
structure RefinesHealthyPostFork {S fd : Type}
    (ops : PostFork.PostForkOpsM (StateM S) fd) : Prop where
  /-- On valid `ChildSpecM` with `.newGroup`, `spawn` either yields a positive Linux PID/PGID or fails without critical OS faults. -/
  spawn_healthy : ∀ s spec,
    let r := (ops.spawn spec).run s
    (∀ child, r.1 = .ok child →
      1 ≤ child.pid ∧ child.pid ≤ MAX_LINUX_PID ∧
      (spec.processGroup = .newGroup → child.pgid = some child.pid)) ∧
    (∀ err, r.1 = .error err →
      (∀ e, err.errno = some e → isCriticalOsErrno e = false) ∧
      (∀ cf, err.childFailure = some cf → isCriticalOsErrno cf.errno = false))

/-- Combined healthy-kernel refinement, descriptor-freshness, `close`-erasure, and table-lens contract for `SysBridge.SysDepsM (StateM S) fd`. -/
structure RefinesHealthySysDeps {S fd : Type} [DecidableEq fd]
    (getTbl : S → ProcTableState fd)
    (setTbl : S → ProcTableState fd → S)
    (openFds : S → List fd)
    (deps : SysDepsM (StateM S) fd) : Prop where
  /-- Lens law `getTbl (setTbl s t) = t`. -/
  get_set : ∀ s t, getTbl (setTbl s t) = t
  /-- Lens law `openFds (setTbl s t) = openFds s`. -/
  openFds_set : ∀ s t, openFds (setTbl s t) = openFds s
  /-- `proc.pipe2` preserves `getTbl`, leaves `openFds` unchanged on `.error`, and on `.ok (rf, wf)` allocates fresh `rf ≠ wf` (`rf ∉ openFds s`, `wf ∉ openFds s`) with `openFds r.2 = wf :: rf :: openFds s`. -/
  pipe2_frame : ∀ s flags,
    let r := (deps.proc.pipe2 flags).run s
    getTbl r.2 = getTbl s ∧
    (∀ e, r.1 = .error e → openFds r.2 = openFds s ∧ isCriticalOsErrno e = false) ∧
    (∀ rf wf, r.1 = .ok (rf, wf) →
      rf ≠ wf ∧ rf ∉ openFds s ∧ wf ∉ openFds s ∧ openFds r.2 = wf :: rf :: openFds s)
  /-- `proc.waitpid` preserves `getTbl` and `openFds` and never fails with `isCriticalOsErrno`. -/
  waitpid_frame : ∀ s pid flags,
    let r := (deps.proc.waitpid pid flags).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ e, r.1 = .error e → isCriticalOsErrno e = false)
  /-- `proc.kill` preserves `getTbl` and `openFds` and never fails with `isCriticalOsErrno`. -/
  kill_frame : ∀ s target sig,
    let r := (deps.proc.kill target sig).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ e, r.1 = .error e → isCriticalOsErrno e = false)
  /-- `files.close` preserves `getTbl`, erases `h` from `openFds` (`openFds r.2 = (openFds s).erase h`), and never fails with `isCriticalOsErrno`. -/
  close_frame : ∀ s h,
    let r := (deps.files.close h).run s
    getTbl r.2 = getTbl s ∧
    openFds r.2 = (openFds s).erase h ∧
    (∀ e, r.1 = .error e → isCriticalOsErrno e = false)
  /-- `files.read` preserves `getTbl` and `openFds`, obeys `bs.size ≤ cap.toNat`, and never fails with `isCriticalOsErrno`. -/
  read_frame : ∀ s h cap,
    let r := (deps.files.read h cap).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ bs, r.1 = .ok bs → bs.size ≤ cap.toNat) ∧
    (∀ e, r.1 = .error e → isCriticalOsErrno e = false)
  /-- `files.write` preserves `getTbl` and `openFds`, obeys `n.toNat ≤ data.size`, and never fails with `isCriticalOsErrno`. -/
  write_frame : ∀ s h data,
    let r := (deps.files.write h data).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ n, r.1 = .ok n → n.toNat ≤ data.size) ∧
    (∀ e, r.1 = .error e → isCriticalOsErrno e = false)
  /-- `files.fstatat` preserves `getTbl` and `openFds` and never fails with `isCriticalOsErrno`. -/
  fstatat_frame : ∀ s dir path flags,
    let r := (deps.files.fstatat dir path flags).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ e, r.1 = .error e → isCriticalOsErrno e = false)
  /-- `files.faccessat` preserves `getTbl` and `openFds` and never fails with `isCriticalOsErrno`. -/
  faccessat_frame : ∀ s dir path mask flags,
    let r := (deps.files.faccessat dir path mask flags).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ e, r.1 = .error e → isCriticalOsErrno e = false)
  /-- `files.fcntl` preserves `getTbl` and `openFds` and never fails with `isCriticalOsErrno`. -/
  fcntl_frame : ∀ s h cmd,
    let r := (deps.files.fcntl h cmd).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ e, r.1 = .error e → isCriticalOsErrno e = false)
  /-- `poll.ppoll` preserves `getTbl` and `openFds` and never fails with `isCriticalOsErrno`. -/
  ppoll_frame : ∀ s entries timeout,
    let r := (deps.poll.ppoll entries timeout).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ e, r.1 = .error e → isCriticalOsErrno e = false)
  /-- `timeRand.clock_gettime` preserves `getTbl` and `openFds` and never fails with `isCriticalOsErrno`. -/
  clock_gettime_frame : ∀ s clk,
    let r := (deps.timeRand.clock_gettime clk).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ e, r.1 = .error e → isCriticalOsErrno e = false)
  /-- `timeRand.clock_nanosleep` preserves `getTbl` and `openFds`. -/
  clock_nanosleep_frame : ∀ s clk abs req,
    let r := (deps.timeRand.clock_nanosleep clk abs req).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s
  /-- `postFork.spawn` satisfies `RefinesHealthyPostFork`. -/
  postFork_healthy : RefinesHealthyPostFork deps.postFork
  /-- `postFork.spawn` preserves `getTbl` and `openFds`. -/
  postFork_frame : ∀ s spec,
    let r := (deps.postFork.spawn spec).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s
  /-- `listAmbientEnv` preserves `getTbl` and `openFds`, and any error has a non-outcome error kind. -/
  listAmbientEnv_frame : ∀ s,
    let r := deps.listAmbientEnv.run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = openFds s ∧
    (∀ e, r.1 = .error e →
      e.kind ≠ .timedOut ∧ e.kind ≠ .outputLimitExceeded ∧ e.kind ≠ .terminatedBySignal)

/-- Composition theorem deriving `RefinesHealthySysDeps` (including `close_frame`'s `openFds r.2 = (openFds s).erase h` directly from canonical `healthyFilesStep` without `.close`/`EBUSY`) over shared `HandleId` (`Nat`). -/
theorem refinesHealthySysDeps_of_components {S : Type}
    (getTbl : S → ProcTableState LinuxSyscall.Files.HandleId)
    (setTbl : S → ProcTableState LinuxSyscall.Files.HandleId → S)
    (projProc : S → HealthyEnv LinuxSyscall.Process.ProcessSysState)
    (projFiles : S → HealthyEnv LinuxSyscall.Files.FilesState)
    (projTime : S → HealthyEnv LinuxSyscall.TimeRand.TimeRandState)
    (deps : SysDepsM (StateM S) LinuxSyscall.Files.HandleId)
    (hSec : ∀ s : S,
      (projProc s).state.ambientSeccomp = false ∧
      (projFiles s).state.ambientSeccomp = false ∧
      (projTime s).state.ambientSeccomp = false)
    (hProc : RefinesHealthyProcessAt projProc id deps.proc)
    (hFiles : RefinesHealthyFilesAt projFiles id deps.files)
    (hTime : RefinesHealthyTimeRandAt projTime deps.timeRand)
    (hPostFork : RefinesHealthyPostFork deps.postFork)
    (hGetSet : ∀ s t, getTbl (setTbl s t) = t)
    (hOpenSet : ∀ s t,
      (projFiles (setTbl s t)).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hPipeLens : ∀ s flags,
      let openFds := fun st : S => (projFiles st).state.fds.map Prod.fst
      let r := (deps.proc.pipe2 flags).run s
      getTbl r.2 = getTbl s ∧
      (∀ e, r.1 = .error e → openFds r.2 = openFds s) ∧
      (∀ rf wf, r.1 = .ok (rf, wf) →
        rf ≠ wf ∧ rf ∉ openFds s ∧ wf ∉ openFds s ∧ openFds r.2 = wf :: rf :: openFds s))
    (hWaitLens : ∀ s pid flags,
      let r := (deps.proc.waitpid pid flags).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hKillLens : ∀ s target sig,
      let r := (deps.proc.kill target sig).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hCloseTblLens : ∀ s h, getTbl ((deps.files.close h).run s).2 = getTbl s)
    (hReadLens : ∀ s h cap,
      let r := (deps.files.read h cap).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hWriteLens : ∀ s h data,
      let r := (deps.files.write h data).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hStatLens : ∀ s dir path flags,
      let r := (deps.files.fstatat dir path flags).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hAccLens : ∀ s dir path mask flags,
      let r := (deps.files.faccessat dir path mask flags).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hFcntlLens : ∀ s h cmd,
      let r := (deps.files.fcntl h cmd).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hPollLens : ∀ s entries timeout,
      let r := (deps.poll.ppoll entries timeout).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst ∧
      (∀ e, r.1 = .error e → isCriticalOsErrno e = false))
    (hCgLens : ∀ s clk,
      let r := (deps.timeRand.clock_gettime clk).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hNsLens : ∀ s clk abs req,
      let r := (deps.timeRand.clock_nanosleep clk abs req).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hPfLens : ∀ s spec,
      let r := (deps.postFork.spawn spec).run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst)
    (hEnvLens : ∀ s,
      let r := deps.listAmbientEnv.run s
      getTbl r.2 = getTbl s ∧
      (projFiles r.2).state.fds.map Prod.fst = (projFiles s).state.fds.map Prod.fst ∧
      (∀ e, r.1 = .error e →
        e.kind ≠ .timedOut ∧ e.kind ≠ .outputLimitExceeded ∧ e.kind ≠ .terminatedBySignal)) :
    RefinesHealthySysDeps getTbl setTbl (fun s => (projFiles s).state.fds.map Prod.fst) deps where
  get_set := hGetSet
  openFds_set := hOpenSet
  pipe2_frame s flags := by
    obtain ⟨hT, hE, hO⟩ := hPipeLens s flags
    obtain ⟨hSt, _⟩ := hProc.pipe2_healthy s flags (hSec s).1
    refine ⟨hT, ?_, hO⟩
    intro e he
    exact ⟨hE e he, ((healthyProcessStep_implies_allowedStep hSt).2.2.2 e (by simp [he])).1⟩
  waitpid_frame s pid flags := by
    obtain ⟨hT, hO⟩ := hWaitLens s pid flags
    obtain ⟨hSt, _⟩ := hProc.waitpid_healthy s pid flags (hSec s).1
    refine ⟨hT, hO, ?_⟩
    intro e he
    exact ((healthyProcessStep_implies_allowedStep hSt).2.2.2 e (by simp [he])).1
  kill_frame s target sig := by
    obtain ⟨hT, hO⟩ := hKillLens s target sig
    obtain ⟨hSt, _⟩ := hProc.kill_healthy s target sig (hSec s).1
    refine ⟨hT, hO, ?_⟩
    intro e he
    exact ((healthyProcessStep_implies_allowedStep hSt).2.2.2 e (by simp [he])).1
  close_frame s h := by
    obtain ⟨hSt, _⟩ := hFiles.close_healthy s h (hSec s).2.1
    refine ⟨hCloseTblLens s h, healthyFilesStep_close_fds hSt, ?_⟩
    intro e he
    exact ((healthyFilesStep_implies_allowedStep hSt).2.2.2.2 e (by simp [he])).1
  read_frame s h cap := by
    obtain ⟨hT, hO⟩ := hReadLens s h cap
    obtain ⟨hSt, _, hSz⟩ := hFiles.read_healthy s h cap (hSec s).2.1
    refine ⟨hT, hO, hSz, ?_⟩
    intro e he
    exact ((healthyFilesStep_implies_allowedStep hSt).2.2.2.2 e (by simp [he])).1
  write_frame s h data := by
    obtain ⟨hT, hO⟩ := hWriteLens s h data
    obtain ⟨hSt, _, hSz⟩ := hFiles.write_healthy s h data (hSec s).2.1
    refine ⟨hT, hO, hSz, ?_⟩
    intro e he
    exact ((healthyFilesStep_implies_allowedStep hSt).2.2.2.2 e (by simp [he])).1
  fstatat_frame s dir path flags := by
    obtain ⟨hT, hO⟩ := hStatLens s dir path flags
    obtain ⟨hSt, _⟩ := hFiles.fstatat_healthy s dir path flags (hSec s).2.1
    refine ⟨hT, hO, ?_⟩
    intro e he
    exact ((healthyFilesStep_implies_allowedStep hSt).2.2.2.2 e (by simp [he])).1
  faccessat_frame s dir path mask flags := by
    obtain ⟨hT, hO⟩ := hAccLens s dir path mask flags
    obtain ⟨hSt, _⟩ := hFiles.faccessat_healthy s dir path mask flags (hSec s).2.1
    refine ⟨hT, hO, ?_⟩
    intro e he
    exact ((healthyFilesStep_implies_allowedStep hSt).2.2.2.2 e (by simp [he])).1
  fcntl_frame s h cmd := by
    obtain ⟨hT, hO⟩ := hFcntlLens s h cmd
    obtain ⟨hSt, _⟩ := hFiles.fcntl_healthy s h cmd (hSec s).2.1
    refine ⟨hT, hO, ?_⟩
    intro e he
    exact ((healthyFilesStep_implies_allowedStep hSt).2.2.2.2 e (by simp [he])).1
  ppoll_frame := hPollLens
  clock_gettime_frame s clk := by
    obtain ⟨hT, hO⟩ := hCgLens s clk
    obtain ⟨hSt, _⟩ := hTime.clock_gettime_healthy s clk (hSec s).2.2
    refine ⟨hT, hO, ?_⟩
    intro e he
    exact ((healthyTimeRandStep_implies_allowedStep hSt).2.2.2 e
      (by simp [LinuxSyscall.TimeRand.outcomeOfTimespec, he])).1
  clock_nanosleep_frame := hNsLens
  postFork_healthy := hPostFork
  postFork_frame := hPfLens
  listAmbientEnv_frame := hEnvLens

/-- Relational contract on `RawProcessOpsM (StateM S)` enforcing both `activeProcessCount` conservation and OS descriptor (`openFds`) conservation across all `spawn`, `awaitOutput`, `killProcessGroup`, and `reap` paths. -/
structure RawProcessLaws {S fd : Type}
    (openFds : S → List fd)
    (raw : RawProcessOpsM (StateM S)) : Prop where
  /-- `mapRawError` agrees with `SysBridge.mapRawError`. -/
  mapRawError_eq : raw.mapRawError = SysBridge.mapRawError
  /-- `spawn` on error preserves both `activeProcessCount` and `openFds`, returns non-empty message, and never reports post-spawn outcome kinds. -/
  spawn_err : ∀ s req err, (raw.spawn req).run s = (.error err, ((raw.spawn req).run s).2) →
    (raw.activeProcessCount.run ((raw.spawn req).run s).2).1 = (raw.activeProcessCount.run s).1 ∧
    openFds ((raw.spawn req).run s).2 = openFds s ∧
    err.message ≠ "" ∧
    err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal
  /-- `activeProcessCount` is a pure read (`s' = s`). -/
  activeCount_pure : ∀ s, (raw.activeProcessCount.run s).2 = s
  /-- Full `spawn → awaitOutput → [killProcessGroup] → reap` lifecycle preserves both `activeProcessCount` and `openFds`, and enforces timeout/cap/signal invariants. -/
  spawn_lifecycle : ∀ s₀ req h s₁,
    (raw.spawn req).run s₀ = (.ok h, s₁) →
    h.pid > 0 ∧ h.pgid > 0 ∧
    let aw := (raw.awaitOutput h req.stdin req.timeoutMs req.maxOutputBytes).run s₁
    (∀ err, aw.1 = .error err →
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal ∧
      let kl := (raw.killProcessGroup h).run aw.2
      let rp := (raw.reap h).run kl.2
      (raw.activeProcessCount.run rp.2).1 = (raw.activeProcessCount.run s₀).1 ∧
      openFds rp.2 = openFds s₀) ∧
    (∀ res, aw.1 = .ok (.exited res) →
      (∀ limit, req.maxOutputBytes = some limit → res.stdout.size + res.stderr.size ≤ limit) ∧
      let rp := (raw.reap h).run aw.2
      (raw.activeProcessCount.run rp.2).1 = (raw.activeProcessCount.run s₀).1 ∧
      openFds rp.2 = openFds s₀ ∧
      (∀ rerr, rp.1 = .error rerr →
        rerr.kind ≠ .timedOut ∧ rerr.kind ≠ .outputLimitExceeded ∧ rerr.kind ≠ .terminatedBySignal)) ∧
    (∀ sig out errB, aw.1 = .ok (.signaled sig out errB) →
      let kl := (raw.killProcessGroup h).run aw.2
      let rp := (raw.reap h).run kl.2
      (raw.activeProcessCount.run rp.2).1 = (raw.activeProcessCount.run s₀).1 ∧
      openFds rp.2 = openFds s₀) ∧
    (∀ out errB, aw.1 = .ok (.timedOut out errB) →
      req.timeoutMs.isSome = true ∧
      let kl := (raw.killProcessGroup h).run aw.2
      let rp := (raw.reap h).run kl.2
      (raw.activeProcessCount.run rp.2).1 = (raw.activeProcessCount.run s₀).1 ∧
      openFds rp.2 = openFds s₀) ∧
    (∀ out errB, aw.1 = .ok (.outputLimitExceeded out errB) →
      req.maxOutputBytes.isSome = true ∧
      (∀ limit, req.maxOutputBytes = some limit → out.size + errB.size ≤ limit) ∧
      let kl := (raw.killProcessGroup h).run aw.2
      let rp := (raw.reap h).run kl.2
      (raw.activeProcessCount.run rp.2).1 = (raw.activeProcessCount.run s₀).1 ∧
      openFds rp.2 = openFds s₀)

end LeanSwe.Process.Proofs
