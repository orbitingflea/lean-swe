import LeanSwe.Process.Model.HealthySim
import LeanSwe.Process.SysBridge
import LeanSwe.Process.Proofs.HealthyStep

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process.SysBridge

export LeanSwe.Process.Model.Internal
  (HealthySimFd mkSimVNode healthySimInodes toSimOpenDesc toSimFilesState
   child100Procs HealthySimState toSimProcState toSimTimeState
   projSimProc projSimFiles projSimTime maxKey healthySimDeps)

@[simp] private theorem stateM_modifyGet_run {S α : Type} (f : S → α × S) (s : S) :
    (modifyGet f : StateM S α).run s = f s := rfl

@[simp] private theorem stateM_pure_run {S α : Type} (a : α) (s : S) :
    (pure a : StateM S α).run s = (a, s) := rfl

private theorem le_foldl_max {β : Type} (xs : List (Nat × β)) (init : Nat) :
    init ≤ maxKey xs init := by
  unfold maxKey
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left init hd.1) (ih (Nat.max init hd.1))

/-- Every key present in `xs.map Prod.fst` is bounded above by `maxKey xs init`. -/
theorem mem_fst_le_maxKey {β : Type} (xs : List (Nat × β)) (init k : Nat)
    (hMem : k ∈ xs.map Prod.fst) :
    k ≤ maxKey xs init := by
  unfold maxKey
  induction xs generalizing init with
  | nil => simp at hMem
  | cons hd tl ih =>
    rcases hd with ⟨k', v⟩
    simp only [List.map_cons, List.mem_cons] at hMem
    simp only [List.foldl_cons]
    rcases hMem with rfl | hRest
    · exact Nat.le_trans (Nat.le_max_right init k) (le_foldl_max tl (Nat.max init k))
    · exact ih (Nat.max init k') hRest


private theorem proc_assocGet_none_of_gt_maxKey {β : Type} (xs : List (Nat × β)) (init k : Nat)
    (hGt : maxKey xs init < k) :
    LinuxSyscall.Process.assocGet xs k = none := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k', v⟩
    have hkLe : k' ≤ maxKey ((k', v) :: tl) init :=
      mem_fst_le_maxKey ((k', v) :: tl) init k' List.mem_cons_self
    have hNe : (k' == k) = false := beq_false_of_ne (by omega)
    simp only [LinuxSyscall.Process.assocGet, hNe, Bool.false_eq_true, ↓reduceIte]
    apply ih
    have hTlLe : maxKey tl init ≤ maxKey ((k', v) :: tl) init := by
      unfold maxKey
      simp only [List.foldl_cons]
      suffices ∀ (ys : List (Nat × β)) (a b : Nat), a ≤ b →
          ys.foldl (fun m x => Nat.max m x.1) a ≤ ys.foldl (fun m x => Nat.max m x.1) b from
        this tl init (Nat.max init k') (Nat.le_max_left _ _)
      intro ys
      induction ys with
      | nil => intro a b hab; exact hab
      | cons y ys' ihy =>
        intro a b hab
        simp only [List.foldl_cons]
        exact ihy (Nat.max a y.1) (Nat.max b y.1)
          (Nat.max_le.mpr ⟨Nat.le_trans hab (Nat.le_max_left _ _), Nat.le_max_right _ _⟩)
    omega

private def child100Entry (z : LinuxSyscall.Process.ZombieStatus) : LinuxSyscall.Process.ProcEntry :=
  { pgid := 100, role := .child .sigchld false, lifecycle := .zombie z }

private theorem deliverSignalToEntry_zombie
    (ps : LinuxSyscall.Process.ProcessSysState) (pid : UInt32) (sig : LinuxSyscall.Process.Signal)
    (z : LinuxSyscall.Process.ZombieStatus) (ts : Bool)
    (a c g arb : Std.TreeSet UInt32 compare) :
    LinuxSyscall.Process.deliverSignalToEntry ps pid sig (child100Entry z) ts a c g arb =
      child100Entry z := by
  unfold LinuxSyscall.Process.deliverSignalToEntry
  dsimp only [child100Entry]
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, ite_self]

private theorem reapThreadGroup_child100
    (ps : LinuxSyscall.Process.ProcessSysState) (z : LinuxSyscall.Process.ZombieStatus)
    (hProcs : ps.procs = [(100, child100Entry z)]) :
    (LinuxSyscall.Process.reapThreadGroup ps 100).procs = [] := by
  unfold LinuxSyscall.Process.reapThreadGroup
  rw [hProcs]
  cases z <;> rfl

private theorem normWaitSig_props (sig : UInt32) :
    (1 ≤ LinuxSyscall.Process.normalizeWaitSig sig ∧
      LinuxSyscall.Process.normalizeWaitSig sig ≤ 126) ∧
    LinuxSyscall.Process.normalizeWaitSig (LinuxSyscall.Process.normalizeWaitSig sig) =
      LinuxSyscall.Process.normalizeWaitSig sig := by
  unfold LinuxSyscall.Process.normalizeWaitSig
  by_cases h : (1 ≤ sig && sig ≤ 126) = true
  · simp only [h, ↓reduceIte]
    exact ⟨by simpa [Bool.and_eq_true, decide_eq_true_eq] using h, trivial⟩
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    decide

private theorem evalModelWaitpid_child100
    (s : HealthySimState) (pid : Int32) (flags : LinuxSyscall.Process.WaitFlags) :
    let ps := toSimProcState s
    let (res, ps') := LinuxSyscall.Process.evalModelWaitpid ps pid flags
    LinuxSyscall.Process.allowedStep ps (.waitpid pid flags)
      (LinuxSyscall.Process.outcomeOfWaited res) = some ps' ∧
    (∀ e, res = .error e → Errno.isCriticalOsErrno e = false ∧ e ≠ Errno.EINTR) ∧
    toSimProcState { s with child100? := if ps'.procs.isEmpty then none else s.child100? } = ps' := by
  dsimp only
  cases hCh : s.child100? with
  | none =>
    dsimp only [LinuxSyscall.Process.evalModelWaitpid, LinuxSyscall.Process.allowedStep,
      LinuxSyscall.Process.validateReqBeforeKernel, LinuxSyscall.Process.allowedStepWaitpid]
    have hPsProcs : (toSimProcState s).procs = [] := by simp [toSimProcState, child100Procs, hCh]
    split
    · exact ⟨rfl, (fun e h => by injection h with hE; subst hE; decide),
        by simp [toSimProcState, child100Procs, hCh]⟩
    · split
      · exact ⟨rfl, (fun e h => by injection h with hE; subst hE; decide),
          by simp [toSimProcState, child100Procs, hCh]⟩
      · have hMatch : LinuxSyscall.Process.matchingUnreapedChildren (toSimProcState s) pid flags = [] := by
          simp [LinuxSyscall.Process.matchingUnreapedChildren,
            LinuxSyscall.Process.matchingUnreapedChildrenGo, hPsProcs]
        rw [hMatch]
        dsimp only [List.isEmpty, LinuxSyscall.Process.outcomeOfWaited]
        exact ⟨rfl, (fun e h => by injection h with hE; subst hE; decide),
          by simp [toSimProcState, child100Procs, hCh]⟩
  | some z =>
    have hPsProcs : (toSimProcState s).procs = [(100, child100Entry z)] := by
      simp [toSimProcState, child100Procs, child100Entry, hCh]
    dsimp only [LinuxSyscall.Process.evalModelWaitpid, LinuxSyscall.Process.allowedStep,
      LinuxSyscall.Process.validateReqBeforeKernel, LinuxSyscall.Process.allowedStepWaitpid]
    split
    · exact ⟨rfl, (fun e h => by injection h with hE; subst hE; decide),
        by simp [toSimProcState, child100Procs, hCh]⟩
    · split
      · exact ⟨rfl, (fun e h => by injection h with hE; subst hE; decide),
          by simp [toSimProcState, child100Procs, hCh]⟩
      · have hCases : LinuxSyscall.Process.matchingUnreapedChildren (toSimProcState s) pid flags = [] ∨
            LinuxSyscall.Process.matchingUnreapedChildren (toSimProcState s) pid flags = [(100, child100Entry z)] := by
          unfold LinuxSyscall.Process.matchingUnreapedChildren
            LinuxSyscall.Process.matchingUnreapedChildrenGo
          rw [hPsProcs]
          have hNotSeen : ({} : Std.TreeSet UInt32 compare).contains 100 = false := rfl
          dsimp only
          simp only [hNotSeen, Bool.false_eq_true, ↓reduceIte]
          split
          · exact Or.inr rfl
          · exact Or.inl rfl
        rcases hCases with hEmpty | hOne
        · rw [hEmpty]
          dsimp only [List.isEmpty, LinuxSyscall.Process.outcomeOfWaited]
          exact ⟨rfl, (fun e h => by injection h with hE; subst hE; decide),
            by simp [toSimProcState, child100Procs, hCh]⟩
        · have hPick : LinuxSyscall.Process.pickImmediateWaitResult (toSimProcState s).procs
              [(100, child100Entry z)] flags = some (z.toWaitResult 100) := by
            unfold LinuxSyscall.Process.pickImmediateWaitResult
              LinuxSyscall.Process.pickImmediateWaitResultSet
              LinuxSyscall.Process.pickImmediateWaitStep
            cases z <;> rfl
          have hStepEq : LinuxSyscall.Process.allowedStepWaitResult (toSimProcState s)
              [(100, child100Entry z)] flags (z.toWaitResult 100) =
              some (LinuxSyscall.Process.reapThreadGroup (toSimProcState s) 100) := by
            cases z with
            | exited zc =>
              change LinuxSyscall.Process.waitChildStep (toSimProcState s) 100
                (child100Entry (.exited zc)) flags (.exited 100 zc) = _
              simp [LinuxSyscall.Process.waitChildStep, child100Entry]
            | signaled zs zcore =>
              obtain ⟨⟨hLo, hHi⟩, _⟩ := normWaitSig_props zs
              change LinuxSyscall.Process.waitChildStep (toSimProcState s) 100
                (child100Entry (.signaled zs zcore)) flags
                (.signaled 100 (LinuxSyscall.Process.normalizeWaitSig zs) zcore) = _
              simp [LinuxSyscall.Process.waitChildStep, child100Entry, hLo, hHi]
          rw [hOne]
          simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, hPick, hStepEq,
            Option.getD, LinuxSyscall.Process.outcomeOfWaited]
          refine ⟨trivial, (fun _ h => by cases h), ?_⟩
          have hRE : (LinuxSyscall.Process.reapThreadGroup (toSimProcState s) 100).procs = [] :=
            reapThreadGroup_child100 (toSimProcState s) z hPsProcs
          simp only [hRE, List.isEmpty_nil, ↓reduceIte]
          unfold LinuxSyscall.Process.reapThreadGroup
          rw [show LinuxSyscall.Process.markThreadGroupLifecycleGo 100 .reaped (toSimProcState s).procs {} [] = [] from hRE]
          rfl

private theorem evalKill_child100
    (ps : LinuxSyscall.Process.ProcessSysState) (target : Int32) (sig : LinuxSyscall.Process.Signal)
    (hProcs : ps.procs = [] ∨ ∃ z, ps.procs = [(100, child100Entry z)]) :
    (∀ e, LinuxSyscall.Process.evalKill ps target sig = .error e →
      Errno.isCriticalOsErrno e = false ∧ e ≠ Errno.EINTR ∧
      (e = Errno.ESRCH → LinuxSyscall.Process.esrchKillNext ps target = ps)) ∧
    (∀ st, LinuxSyscall.Process.evalKill ps target sig = .ok st → st = ps) := by
  have hReapSingle : ∀ pid, LinuxSyscall.Process.reapExitDeadSingleTarget ps pid = ps := by
    intro pid
    unfold LinuxSyscall.Process.reapExitDeadSingleTarget
    dsimp only
    split
    · rfl
    · rcases hProcs with hNil | ⟨z, hOne⟩
      · rw [hNil]; rfl
      · rw [hOne]
        by_cases hp : (100 == pid) = true
        · simp only [LinuxSyscall.Process.assocGet, hp, ↓reduceIte, child100Entry]; rfl
        · have hpF : (100 == pid) = false := Bool.eq_false_iff.mpr hp
          simp only [LinuxSyscall.Process.assocGet, hpF, Bool.false_eq_true, ↓reduceIte]
  have hNonLead : ∀ pid, LinuxSyscall.Process.nonLeaderEsrch? ps pid = none := by
    intro pid
    unfold LinuxSyscall.Process.nonLeaderEsrch?
    dsimp only
    split
    · rfl
    · rcases hProcs with hNil | ⟨z, hOne⟩
      · rw [hNil]; rfl
      · rw [hOne]
        by_cases hp : (100 == pid) = true
        · simp only [LinuxSyscall.Process.assocGet, hp, ↓reduceIte, child100Entry]
        · have hpF : (100 == pid) = false := Bool.eq_false_iff.mpr hp
          simp only [LinuxSyscall.Process.assocGet, hpF, Bool.false_eq_true, ↓reduceIte]
  have hReapGrp : ∀ pred, LinuxSyscall.Process.reapExitDeadGroup ps pred = ps := by
    intro pred
    unfold LinuxSyscall.Process.reapExitDeadGroup LinuxSyscall.Process.reapActiveLeadersWhere
    rcases hProcs with hNil | ⟨z, hOne⟩
    · rw [hNil]; rfl
    · rw [hOne]
      have hNotDead : ((child100Entry z).lifecycle == .exitDead) = false := by cases z <;> rfl
      unfold LinuxSyscall.Process.collectActivePidSetGo
      dsimp only
      have hNS : ({} : Std.TreeSet UInt32 compare).contains 100 = false := rfl
      simp only [hNS, hNotDead, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rfl
  have hEsrch : LinuxSyscall.Process.esrchKillNext ps target = ps := by
    unfold LinuxSyscall.Process.esrchKillNext
    split
    · split
      · dsimp only; rw [hReapSingle, hNonLead]; rfl
      · split
        · exact hReapGrp _
        · split
          · exact hReapGrp _
          · rfl
    · rfl
  have hApply : ∀ pred, LinuxSyscall.Process.applySignalWhere ps ps.procs pred sig = ps.procs := by
    intro pred
    unfold LinuxSyscall.Process.applySignalWhere
    rcases hProcs with hNil | ⟨z, hOne⟩
    · rw [hNil]; rfl
    · rw [hOne]
      unfold LinuxSyscall.Process.applySignalWhereGo
      have hNS : ({} : Std.TreeSet UInt32 compare).contains 100 = false := rfl
      simp only [hNS, Bool.false_eq_true, ↓reduceIte]
      split
      · simp only [deliverSignalToEntry_zombie]; rfl
      · rfl
  have hGroup : ∀ pgid,
      (∀ e, LinuxSyscall.Process.evalKillProcessGroup ps pgid sig = .error e →
        Errno.isCriticalOsErrno e = false ∧ e ≠ Errno.EINTR) ∧
      (∀ st, LinuxSyscall.Process.evalKillProcessGroup ps pgid sig = .ok st → st = ps) := by
    intro pgid
    unfold LinuxSyscall.Process.evalKillProcessGroup
    dsimp only
    split
    · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
    · split
      · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
      · split
        · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
        · split
          · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
          · refine ⟨(fun _ h => by cases h), fun st hOk => ?_⟩
            injection hOk with hEq; subst hEq
            rw [hApply]
  have hSingle : ∀ tpid,
      (∀ e, LinuxSyscall.Process.deliverSignalToTarget ps tpid sig false = .error e →
        Errno.isCriticalOsErrno e = false ∧ e ≠ Errno.EINTR) ∧
      (∀ st, LinuxSyscall.Process.deliverSignalToTarget ps tpid sig false = .ok st → st = ps) := by
    intro tpid
    unfold LinuxSyscall.Process.deliverSignalToTarget
    dsimp only
    split
    · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
    · split
      · split
        · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
        · exact ⟨(fun _ h => by cases h), fun st h => by injection h with hE; exact hE.symm⟩
      · rcases hProcs with hNil | ⟨z, hOne⟩
        · rw [hNil]; dsimp only [LinuxSyscall.Process.assocGet]
          exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
        · rw [hOne]
          by_cases hEqPid : (100 == tpid) = true
          · have hT : tpid = 100 := (beq_iff_eq.mp hEqPid).symm
            subst hT
            simp only [LinuxSyscall.Process.assocGet, beq_self_eq_true, ↓reduceIte, child100Entry]
            split
            · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
            · split
              · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
              · split
                · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
                · refine ⟨(fun _ h => by cases h), fun st hOk => ?_⟩
                  injection hOk with hEq; subst hEq
                  cases ps with
                  | mk a b c d e f g h i j k l =>
                    simp only at hOne ⊢
                    subst hOne
                    dsimp only [LinuxSyscall.Process.assocSet, LinuxSyscall.Process.assocSetAux]
                    have hDel := deliverSignalToEntry_zombie
                      { selfPid := a, selfPgid := b, selfUid := c, sigchld := d,
                        ambientIgnoredSigs := e, closedPidNamespace := f,
                        ambientSeccomp := g, watchQueueSupported := h,
                        pidfdThreadSupported := i, procs := [(100, child100Entry z)],
                        fds := k, nextHid := l }
                      100 sig z false
                      (LinuxSyscall.Process.collectActiveSubthreadTgids [(100, child100Entry z)])
                      (LinuxSyscall.Process.collectControlledSubthreadTgids [(100, child100Entry z)])
                      (LinuxSyscall.Process.collectGroupExitSubthreadTgids [(100, child100Entry z)])
                      (LinuxSyscall.Process.collectArbitraryRunningSubthreadTgids [(100, child100Entry z)])
                    simp only [child100Entry] at hDel ⊢
                    rw [hDel]
                    rfl
          · have hNePid : (100 == tpid) = false := Bool.eq_false_iff.mpr hEqPid
            simp only [LinuxSyscall.Process.assocGet, hNePid, Bool.false_eq_true, ↓reduceIte]
            exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
  unfold LinuxSyscall.Process.evalKill
  refine ⟨?_, ?_⟩
  · intro e hErr
    split at hErr
    · injection hErr with hE; subst hE; exact ⟨by decide, by decide, fun _ => hEsrch⟩
    · split at hErr
      · injection hErr with hE; subst hE; exact ⟨by decide, by decide, fun _ => hEsrch⟩
      · split at hErr
        · have h := (hSingle target.toUInt32).1 e hErr; exact ⟨h.1, h.2, fun _ => hEsrch⟩
        · split at hErr
          · have h := (hGroup _).1 e hErr; exact ⟨h.1, h.2, fun _ => hEsrch⟩
          · split at hErr
            · dsimp only at hErr
              split at hErr
              · injection hErr with hE; subst hE; exact ⟨by decide, by decide, fun _ => hEsrch⟩
              · split at hErr
                · injection hErr with hE; subst hE; exact ⟨by decide, by decide, fun _ => hEsrch⟩
                · cases hErr
            · have h := (hGroup _).1 e hErr; exact ⟨h.1, h.2, fun _ => hEsrch⟩
  · intro st hOk
    split at hOk
    · cases hOk
    · split at hOk
      · cases hOk
      · split at hOk
        · exact (hSingle target.toUInt32).2 st hOk
        · split at hOk
          · exact (hGroup _).2 st hOk
          · split at hOk
            · dsimp only at hOk
              split at hOk
              · cases hOk
              · split at hOk
                · cases hOk
                · injection hOk with hEq; subst hEq; rw [hApply]
            · exact (hGroup _).2 st hOk

/-- `healthySimDeps.proc` refines canonical `LinuxSyscall.Process.healthyStep` via `projSimProc`. -/
theorem healthySimDeps_proc_refinesHealthy :
    RefinesHealthyProcOpsAt projSimProc id healthySimDeps.proc where
  pipe2_healthy s flags _ := by
    dsimp only [healthySimDeps, stateM_modifyGet_run, projSimProc, id]
    by_cases hVal : flags.isValid = true
    · by_cases hNotif : flags.notificationPipe = true
      · simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hNotif,
          Except.map, LinuxSyscall.Process.outcomeOfPiped]
        unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.HealthyEnv.wf
          LinuxSyscall.Process.isCriticalFault LinuxSyscall.Process.isEintrOutcome
          LinuxSyscall.Process.allowedStep LinuxSyscall.Process.validateReqBeforeKernel
        have hCrit65 : Errno.isCriticalOsErrno Errno.ENOPKG = false := by decide
        have hNeEi65 : (Errno.ENOPKG == Errno.EINTR) = false := by decide
        simp [toSimProcState, LinuxSyscall.Process.ProcessSysState.initial, hVal, hNotif,
          hCrit65, hNeEi65]
      · have hNotifF : flags.notificationPipe = false := Bool.eq_false_iff.mpr hNotif
        simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hNotifF,
          Except.map, LinuxSyscall.Process.outcomeOfPiped]
        let base := Nat.max (maxKey s.procFds s.procNextHid) (maxKey s.simFds 10)
        have hLeB : maxKey s.procFds s.procNextHid ≤ base := Nat.le_max_left _ _
        have hNoneR : LinuxSyscall.Process.assocGet s.procFds (base + 1) = none :=
          proc_assocGet_none_of_gt_maxKey s.procFds s.procNextHid (base + 1) (by omega)
        have hNoneW : LinuxSyscall.Process.assocGet s.procFds (base + 2) = none :=
          proc_assocGet_none_of_gt_maxKey s.procFds s.procNextHid (base + 2) (by omega)
        have hNe : ((base + 1 : Files.HandleId) != (base + 2 : Files.HandleId)) = true :=
          bne_iff_ne.mpr (by omega)
        unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.HealthyEnv.wf
          LinuxSyscall.Process.isCriticalFault LinuxSyscall.Process.isEintrOutcome
          LinuxSyscall.Process.allowedStep LinuxSyscall.Process.validateReqBeforeKernel
        dsimp only
        have hSec : (toSimProcState s).ambientSeccomp = false := rfl
        have hFds : (toSimProcState s).fds = s.procFds := rfl
        rw [hSec]
        simp only [Bool.not_false, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
        rw [hVal, hNotifF, hFds, hNe, hNoneR, hNoneW]
        simp [LinuxSyscall.Process.commitPipeFds, toSimProcState, LinuxSyscall.Process.ProcessSysState.initial]
    · have hValF : flags.isValid = false := Bool.eq_false_iff.mpr hVal
      simp only [hValF, Bool.not_false, ↓reduceIte, Except.map, LinuxSyscall.Process.outcomeOfPiped]
      unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.HealthyEnv.wf
        LinuxSyscall.Process.isCriticalFault LinuxSyscall.Process.isEintrOutcome
        LinuxSyscall.Process.allowedStep LinuxSyscall.Process.validateReqBeforeKernel
      simp [toSimProcState, LinuxSyscall.Process.ProcessSysState.initial, hValF,
        Errno.isCriticalOsErrno, Errno.EINVAL, Errno.EINTR, Errno.ENOMEM, Errno.EIO, Errno.ENFILE]
  waitpid_healthy s pid flags _ := by
    have hPres := evalModelWaitpid_child100 s pid flags
    dsimp only [healthySimDeps, stateM_modifyGet_run, projSimProc]
    have hWaitRun : (LinuxSyscall.Process.modelOps.waitpid pid flags).run (toSimProcState s) =
        LinuxSyscall.Process.evalModelWaitpid (toSimProcState s) pid flags := by
      dsimp only [LinuxSyscall.Process.modelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure, StateT.run,
        get, MonadState.get, getThe, MonadStateOf.get, StateT.get,
        set, MonadState.set, MonadStateOf.set, StateT.set]
    rw [hWaitRun]
    dsimp only at hPres
    cases hEv : LinuxSyscall.Process.evalModelWaitpid (toSimProcState s) pid flags with
    | mk res ps' =>
      rw [hEv] at hPres
      obtain ⟨hSound, hNoCrit, hStEq⟩ := hPres
      dsimp only at hSound ⊢
      unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.HealthyEnv.wf
        LinuxSyscall.Process.isCriticalFault LinuxSyscall.Process.isEintrOutcome
      have hSec : (toSimProcState s).ambientSeccomp = false := rfl
      cases res with
      | ok wr =>
        dsimp only [LinuxSyscall.Process.outcomeOfWaited] at hSound ⊢
        rw [hSec, hSound, hStEq]
        rfl
      | error e =>
        obtain ⟨hCrit, hNeEi⟩ := hNoCrit e rfl
        dsimp only [LinuxSyscall.Process.outcomeOfWaited] at hSound hStEq ⊢
        simp only [hSec, hCrit, hSound, beq_false_of_ne hNeEi, hStEq,
          Bool.not_false, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  kill_healthy s target sig _ := by
    have hProcsShape : (toSimProcState s).procs = [] ∨ ∃ z, (toSimProcState s).procs = [(100, child100Entry z)] := by
      cases hCh : s.child100? with
      | none => exact Or.inl (by simp [toSimProcState, child100Procs, hCh])
      | some z => exact Or.inr ⟨z, by simp [toSimProcState, child100Procs, child100Entry, hCh]⟩
    dsimp only [healthySimDeps, stateM_modifyGet_run, projSimProc]
    obtain ⟨res, ps', hEvRun⟩ : ∃ res ps',
        (LinuxSyscall.Process.modelOps.kill target sig).run (toSimProcState s) = (res, ps') :=
      ⟨_, _, rfl⟩
    rw [hEvRun]
    have hRun : LinuxSyscall.Process.modelOps.kill target sig (toSimProcState s) = (res, ps') := hEvRun
    dsimp only
    unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.HealthyEnv.wf
      LinuxSyscall.Process.isCriticalFault LinuxSyscall.Process.isEintrOutcome
    have hSec : (toSimProcState s).ambientSeccomp = false := rfl
    have hKillUnf : LinuxSyscall.Process.modelOps.kill target sig (toSimProcState s) =
        match LinuxSyscall.Process.validateReqBeforeKernel (toSimProcState s) (.kill target sig) with
        | some e => (.error e, toSimProcState s)
        | none =>
          match LinuxSyscall.Process.evalKill (toSimProcState s) target sig with
          | .ok st => (.ok (), st)
          | .error e =>
            (.error e,
             if e == Errno.ESRCH then LinuxSyscall.Process.esrchKillNext (toSimProcState s) target
             else toSimProcState s) := by
      unfold LinuxSyscall.Process.modelOps
      dsimp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure,
        get, MonadState.get, getThe, MonadStateOf.get, StateT.get,
        set, MonadState.set, MonadStateOf.set, StateT.set]
      cases LinuxSyscall.Process.validateReqBeforeKernel (toSimProcState s) (.kill target sig) with
      | some _ => rfl
      | none =>
        dsimp only
        cases LinuxSyscall.Process.evalKill (toSimProcState s) target sig with
        | ok _ => rfl
        | error e =>
          cases (e == Errno.ESRCH) <;> rfl
    rw [hKillUnf] at hRun
    cases hPre : LinuxSyscall.Process.validateReqBeforeKernel (toSimProcState s) (.kill target sig) with
    | some preE =>
      rw [hPre] at hRun
      injection hRun with hR hS
      subst hR hS
      have hPreEq : preE = Errno.EINVAL := by
        unfold LinuxSyscall.Process.validateReqBeforeKernel at hPre
        dsimp only at hPre
        split at hPre
        · injection hPre with hEq; exact hEq.symm
        · cases hPre
      subst hPreEq
      have hSound2 : LinuxSyscall.Process.allowedStep (toSimProcState s) (.kill target sig)
          (.err Errno.EINVAL) = some (toSimProcState s) := by
        simp [LinuxSyscall.Process.allowedStep, hPre]
      dsimp only [LinuxSyscall.Process.outcomeOfUnit]
      have hCrit22 : Errno.isCriticalOsErrno Errno.EINVAL = false := by decide
      have hNeEi22 : (Errno.EINVAL == Errno.EINTR) = false := by decide
      simp [hSec, hCrit22, hSound2, hNeEi22]
    | none =>
      rw [hPre] at hRun
      dsimp only at hRun
      obtain ⟨hKillErr, hKillOk⟩ := evalKill_child100 (toSimProcState s) target sig hProcsShape
      cases hEv : LinuxSyscall.Process.evalKill (toSimProcState s) target sig with
      | ok st =>
        rw [hEv] at hRun
        injection hRun with hR hS
        subst hR hS
        have hEq := hKillOk st hEv
        subst hEq
        have hSound2 : LinuxSyscall.Process.allowedStep (toSimProcState s) (.kill target sig)
            .unit = some (toSimProcState s) := by
          simp [LinuxSyscall.Process.allowedStep, hPre, LinuxSyscall.Process.allowedStepKill, hEv]
        dsimp only [LinuxSyscall.Process.outcomeOfUnit]
        rw [hSec, hSound2]
        rfl
      | error e =>
        rw [hEv] at hRun
        injection hRun with hR hS
        subst hR
        obtain ⟨hCrit, hNeEi, hEsrchEq⟩ := hKillErr e hEv
        have hNextEq : ps' = toSimProcState s := by
          rw [← hS]
          split
          · next hIs => exact hEsrchEq (beq_iff_eq.mp hIs)
          · rfl
        subst hNextEq
        have hSound2 : LinuxSyscall.Process.allowedStep (toSimProcState s) (.kill target sig)
            (.err e) = some (toSimProcState s) := by
          unfold LinuxSyscall.Process.allowedStep
          rw [hPre]
          dsimp only [LinuxSyscall.Process.allowedStepKill]
          rw [hEv]
          simp only [beq_self_eq_true, ↓reduceIte]
          exact congrArg some (by
            split
            · next hIs => exact hEsrchEq (beq_iff_eq.mp hIs)
            · rfl)
        dsimp only [LinuxSyscall.Process.outcomeOfUnit]
        simp [hSec, hCrit, hSound2, beq_false_of_ne hNeEi]

end LeanSwe.Process.Proofs
