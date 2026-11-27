import LeanSweProofs.PostFork.Proofs.FdOps
import LeanSweProofs.PostFork.Proofs.FdOpsClose
import LeanSweProofs.PostFork.Proofs.IoAndReport

/-!
# Shared Child Entrypoint Proof Combinators

Shared constants, `report_and_exit` exit-status/byte-payload wrappers,
trace helpers for `closedBeforeSyncRead`, arbitrary-oracle (`*_safety`) specs
for FD helpers called by `run_child`, and non-running totality combinators.
-/

namespace LeanSwe.PostFork.Proofs

open _root_.Aeneas _root_.Aeneas.Std
open LeanSwe.PostFork
open LeanSwe.PostFork.Aeneas.Internal
open LeanSwe.PostFork.Aeneas.Internal.World
open LeanSwe.PostFork.Aeneas
open LeanSwe.PostFork.Aeneas.Model

section Constants

/-- `postfork.child.SIGPIPE` equals `13#i32`. -/
theorem child_sigpipe_eq : postfork.child.SIGPIPE = 13#i32 := by
  unfold postfork.child.SIGPIPE; rfl

/-- `postfork.child.EXIT_EXEC_FAILED` equals `127#i32`. -/
theorem child_exit_exec_failed_eq : postfork.child.EXIT_EXEC_FAILED = 127#i32 := by
  unfold postfork.child.EXIT_EXEC_FAILED; rfl

/-- `postfork.child.EXIT_SYNC_ABORT` equals `125#i32`. -/
theorem child_exit_sync_abort_eq : postfork.child.EXIT_SYNC_ABORT = 125#i32 := by
  unfold postfork.child.EXIT_SYNC_ABORT; rfl

/-- `postfork.child.STAGE_VALIDATE` equals `1#u8`. -/
theorem child_stage_validate_eq : postfork.child.STAGE_VALIDATE = 1#u8 := by
  unfold postfork.child.STAGE_VALIDATE; rfl

/-- `postfork.child.STAGE_PROCESS_GROUP` equals `2#u8`. -/
theorem child_stage_process_group_eq : postfork.child.STAGE_PROCESS_GROUP = 2#u8 := by
  unfold postfork.child.STAGE_PROCESS_GROUP; rfl

/-- `postfork.child.STAGE_SIGNAL_RESET` equals `3#u8`. -/
theorem child_stage_signal_reset_eq : postfork.child.STAGE_SIGNAL_RESET = 3#u8 := by
  unfold postfork.child.STAGE_SIGNAL_RESET; rfl

/-- `postfork.child.STAGE_FD_SETUP` equals `4#u8`. -/
theorem child_stage_fd_setup_eq : postfork.child.STAGE_FD_SETUP = 4#u8 := by
  unfold postfork.child.STAGE_FD_SETUP; rfl

/-- `postfork.child.STAGE_CLOSE_UNKEPT` equals `5#u8`. -/
theorem child_stage_close_unkept_eq : postfork.child.STAGE_CLOSE_UNKEPT = 5#u8 := by
  unfold postfork.child.STAGE_CLOSE_UNKEPT; rfl

/-- `postfork.child.STAGE_CHDIR` equals `6#u8`. -/
theorem child_stage_chdir_eq : postfork.child.STAGE_CHDIR = 6#u8 := by
  unfold postfork.child.STAGE_CHDIR; rfl

/-- `postfork.child.STAGE_EXECVE` equals `7#u8`. -/
theorem child_stage_execve_eq : postfork.child.STAGE_EXECVE = 7#u8 := by
  unfold postfork.child.STAGE_EXECVE; rfl

/-- `postfork.fd_ops.EBADF` equals `World.EBADF`. -/
theorem fd_ops_ebadf_eq : postfork.fd_ops.EBADF = EBADF := by
  unfold postfork.fd_ops.EBADF EBADF; rfl

/-- `postfork.fd_ops.EINVAL` equals `World.EINVAL`. -/
theorem fd_ops_einval_eq : postfork.fd_ops.EINVAL = EINVAL := by
  unfold postfork.fd_ops.EINVAL EINVAL; rfl

/-- `postfork.fd_ops.EIO` equals `World.EIO`. -/
theorem fd_ops_eio_eq : postfork.fd_ops.EIO = World.EIO := by
  unfold postfork.fd_ops.EIO World.EIO; rfl

end Constants

section ReportWrappers

private theorem reportBytesPost_exited127 {s s' : ChildState} {repW : I32} {payload : Bytes}
    (hRun : s.status = .running) (hPost : ReportBytesPost s repW payload s') :
    s'.status = .exited 127#i32 := by
  dsimp only [ReportBytesPost] at hPost
  have hNot : ¬ (s.status ≠ .running) := fun h => h hRun
  rw [ite_eq_right_of_eq_false _ _ (eq_false hNot)] at hPost
  exact hPost.1

private theorem reportBytesPost_not_running {s s' : ChildState} {repW : I32} {payload : Bytes}
    (hNot : s.status ≠ .running) (hPost : ReportBytesPost s repW payload s') :
    s' = s := by
  dsimp only [ReportBytesPost] at hPost
  rw [ite_eq_left_of_eq_true _ _ (eq_true hNot)] at hPost
  exact hPost

private theorem reportBytesPost_bytes_oracle_nil {s s' : ChildState} {repW : I32} {payload : Bytes}
    {rd : Bool} {rem : Bytes}
    (hRun : s.status = .running) (hOr : s.oracle = []) (hRepGe : 0#i32 ≤ repW)
    {repEnt : FdEntry} (hRepFd : s.getFd repW.val = some repEnt)
    (hDesc : s.getDesc repEnt.desc = .stream rd true false rem)
    (hPost : ReportBytesPost s repW payload s') :
    s'.status = .exited 127#i32 ∧ appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc = payload := by
  dsimp only [ReportBytesPost] at hPost
  have hNot : ¬ (s.status ≠ .running) := fun h => h hRun
  rw [ite_eq_right_of_eq_false _ _ (eq_false hNot)] at hPost
  refine ⟨hPost.1, ?_⟩
  have hW := hPost.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hRepGe
  simp only [hRepFd, hDesc] at hW
  exact hW.2 (fun rawE => ⟨fun h => by simp [currentFault, hOr] at h,
    fun h => by simp [currentFault, hOr] at h⟩) (fun f hf => by simp [hOr] at hf)

/-- `report_and_exit` terminates with `status = .exited 127#i32` on any running state. -/
theorem report_and_exit_status127 (s : ChildState) (hRun : s.status = .running)
    (repW : I32) (stage : U8) (errnum fallback : I32) :
    OkPost (postfork.child.report_and_exit s repW stage errnum fallback) fun s' =>
      s'.status = .exited 127#i32 :=
  okPost_mono (report_and_exit_spec s repW stage errnum fallback)
    (fun _ h => reportBytesPost_exited127 hRun h)

/-- `report_and_exit` preserves a non-running state verbatim. -/
theorem report_and_exit_not_running (s : ChildState) (hNot : s.status ≠ .running)
    (repW : I32) (stage : U8) (errnum fallback : I32) :
    OkPost (postfork.child.report_and_exit s repW stage errnum fallback) fun s' => s' = s :=
  okPost_mono (report_and_exit_spec s repW stage errnum fallback)
    (fun _ h => reportBytesPost_not_running hNot h)

/-- `report_and_exit` writes `expectedFailureWireBytes` when `oracle = []` on an open non-broken stream. -/
theorem report_and_exit_bytes (s : ChildState) (hRun : s.status = .running)
    (hOr : s.oracle = []) (repW : I32) (stage : U8) (errnum fallback : I32) (hRepGe : 0#i32 ≤ repW)
    {repEnt : FdEntry} (hRepFd : s.getFd repW.val = some repEnt)
    {rd : Bool} {rem : Bytes} (hDesc : s.getDesc repEnt.desc = .stream rd true false rem) :
    OkPost (postfork.child.report_and_exit s repW stage errnum fallback) fun s' =>
      s'.status = .exited 127#i32 ∧
      appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc =
        expectedFailureWireBytes stage (normalizeErrnoSpec errnum fallback) :=
  okPost_mono (report_and_exit_spec s repW stage errnum fallback)
    (fun _ h => reportBytesPost_bytes_oracle_nil hRun hOr hRepGe hRepFd hDesc h)

end ReportWrappers

section TraceHelpers

private theorem takeWhile_append_of_forall_ne {t1 t2 : List Event} {syncR : I32}
    (hNoRead : ∀ ev ∈ t1, ev.req ≠ .read1 syncR) :
    List.takeWhile (fun ev => ev.req != .read1 syncR) (t1 ++ t2) =
      t1 ++ List.takeWhile (fun ev => ev.req != .read1 syncR) t2 := by
  induction t1 with
  | nil => simp
  | cons ev rest ih =>
    have hne : (ev.req != .read1 syncR) = true := by
      simpa using hNoRead ev (List.mem_cons_self ..)
    simp only [List.cons_append, List.takeWhile_cons, hne, ↓reduceIte]
    rw [ih (fun e he => hNoRead e (List.mem_cons_of_mem _ he))]

/-- Trace prefix of `close` events before any `read1 syncR` preserves `closedBeforeSyncRead` under any suffix. -/
theorem closedBeforeSyncRead_append {t1 t2 : List Event} {closeFds : List I32} {syncR : I32}
    (hNoRead : ∀ ev ∈ t1, ev.req ≠ .read1 syncR)
    (hClosed : ∀ cfd ∈ closeFds, 0#i32 ≤ cfd → ∃ out, Event.mk (.close cfd) out ∈ t1) :
    closedBeforeSyncRead (t1 ++ t2) closeFds syncR := by
  dsimp only [closedBeforeSyncRead]
  rw [takeWhile_append_of_forall_ne hNoRead]
  exact fun cfd hmem h0 => by
    rcases hClosed cfd hmem h0 with ⟨out, hout⟩
    exact ⟨out, List.mem_append_left _ hout⟩

end TraceHelpers

section SafetyFdOps

private theorem slice_idx_succ_local {α : Type} (s : Slice α) {j : Usize} (hlt : j < s.len) :
    ∃ hjlt : j.val < s.val.length,
      s.index_usize j = .ok s.val[j.val] ∧
      ∃ z : Usize, j + 1#usize = Result.ok z ∧ z.val = j.val + 1 := by
  have hjlt : j.val < s.val.length := by simpa [Slice.len] using hlt
  have hlen : s.val.length ≤ Usize.max := s.property
  have h1 : (1#usize : Usize).val = 1 := rfl
  have hmax : j.val + 1 ≤ Usize.max := by omega
  have hidx : s.index_usize j = .ok s.val[j.val] := by
    simp [Slice.index_usize, hjlt]
  have hlt2 : j.val + 1 < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
  have hchk : UScalar.check_bounds .Usize (j.val + 1) = true := decide_eq_true hlt2
  have hadd : j + 1#usize = UScalar.tryMk .Usize (j.val + 1) := by
    change UScalar.tryMk .Usize (j.val + (1#usize : Usize).val) = _
    rw [h1]
  rw [hadd]
  unfold UScalar.tryMk UScalar.tryMkOpt
  simp only [hchk, ↓reduceDIte, Result.ofOption]
  exact ⟨hjlt, hidx, UScalar.ofNatCore (j.val + 1) hlt2, rfl, rfl⟩

private theorem eraseFdEntries_length_le (l : List (Int × FdEntry)) (k : Int) :
    (eraseFdEntries l k).length ≤ l.length := by
  exact List.length_filter_le _ _

private theorem getFd_eq_of_fds_eq_local {s1 s2 : ChildState} (h : s1.fds = s2.fds) (k : Int) :
    s1.getFd k = s2.getFd k := by
  simp [ChildState.getFd, h]

/-- Arbitrary-oracle safety specification for `postfork.fd_ops.set_cloexec`. -/
theorem set_cloexec_safety (s : ChildState) (hRun : s.status = .running) (fd : I32) :
    OkPost (postfork.fd_ops.set_cloexec s fd) fun p =>
      p.2.status = .running ∧ SameChildConfig p.2 s ∧
      p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
      p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
      p.2.fds.length ≤ s.fds.length + 1 ∧
      (p.1 = .Ok () → CloexecTogglePost true s fd (.Ok ()) p.2) := by
  unfold postfork.fd_ops.set_cloexec
  obtain ⟨r1, s1, h1, hs1eq, _, _, hget1⟩ := sys_fcntl_getfd_running s hRun fd
  rw [h1, bind_ok]
  have hs1Cfg : SameChildConfig s1 s := by
    rw [hs1eq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hs1Run : s1.status = .running := by rw [hs1eq]; exact hRun
  have hs1Pg : s1.pgid = s.pgid := by rw [hs1eq]
  have hs1Cw : s1.cwd = s.cwd := by rw [hs1eq]
  have hs1Si : s1.sig = s.sig := by rw [hs1eq]
  have hs1De : s1.descs = s.descs := by rw [hs1eq]
  have hs1Wl : s1.writeLog = s.writeLog := by rw [hs1eq]
  have hs1Fds : s1.fds = s.fds := by rw [hs1eq]
  have hs1Mask : s1.kernelMasksSetfd = s.kernelMasksSetfd := by rw [hs1eq]
  cases hFd : s.getFd fd.val with
  | none =>
    rw [hFd] at hget1
    cases hf : currentFault s <;> (
      simp only [hf] at hget1
      rw [hget1]
      exact okPost_ok _ _ ⟨hs1Run, hs1Cfg, hs1Pg, hs1Cw, hs1Si, hs1De, hs1Wl,
        by rw [hs1Fds]; exact Nat.le_succ _, fun h => by cases h⟩)
  | some e =>
    rw [hFd] at hget1
    cases hf : currentFault s with
    | seccomp rawE | fail rawE =>
      rw [hf] at hget1
      rw [hget1]
      exact okPost_ok _ _ ⟨hs1Run, hs1Cfg, hs1Pg, hs1Cw, hs1Si, hs1De, hs1Wl,
        by rw [hs1Fds]; exact Nat.le_succ _, fun h => by cases h⟩
    | normal | partialWrite _ | dentsBatch _ =>
      rw [hf] at hget1
      rw [hget1]
      change OkPost (do
        let i ← lift (fdFlagsWord e ||| postfork.fd_ops.FD_CLOEXEC)
        sys.fcntl_setfd s1 fd i) _
      have hclo : postfork.fd_ops.FD_CLOEXEC = 1#i32 := by
        unfold postfork.fd_ops.FD_CLOEXEC; rfl
      rw [show lift (fdFlagsWord e ||| postfork.fd_ops.FD_CLOEXEC) =
            Result.ok (fdFlagsWord e ||| 1#i32) from by rw [hclo]; rfl,
          bind_ok]
      obtain ⟨r2, s2, h2, hcfg2, hpg2, hcw2, hsi2, hde2, hwl2, _, hErrFds, hOk2, _⟩ :=
        sys_fcntl_setfd_running s1 hs1Run fd (fdFlagsWord e ||| 1#i32)
      rw [h2]
      have hs2Len : s2.fds.length ≤ s.fds.length + 1 := by
        cases r2 with
        | Err e' => rw [hErrFds e' rfl, hs1Fds]; exact Nat.le_succ _
        | Ok u =>
          cases u
          have hfd2 := hOk2 rfl
          rw [hfd2]
          cases hs1Get : s1.getFd fd.val with
          | none =>
            have : s.getFd fd.val = none := by
              simpa [ChildState.getFd, hs1Fds] using hs1Get
            rw [this] at hFd; cases hFd
          | some e1 =>
            simp only [ChildState.putSlot, List.length_cons, hs1Fds]
            exact Nat.succ_le_succ (eraseFdEntries_length_le s.fds fd.val)
      refine okPost_ok _ _ ⟨(hcfg2.trans hs1Cfg).status.trans hRun, hcfg2.trans hs1Cfg,
        hpg2.trans hs1Pg, hcw2.trans hs1Cw, hsi2.trans hs1Si, hde2.trans hs1De, hwl2.trans hs1Wl,
        hs2Len, fun hr2 => ?_⟩
      subst hr2
      have hfd2 := hOk2 rfl
      have hs1Get : s1.getFd fd.val = some e := by rw [getFd_eq_of_fds_eq_local hs1Fds, hFd]
      have hs2GetEq := fun k => getFd_eq_of_fds_eq_local hfd2 k
      simp only [hs1Get] at hs2GetEq
      have hupd := updateFdFlags_set_cloexec s e
      change CloexecTogglePost true s fd (.Ok ()) s2
      simp only [CloexecTogglePost, hFd]
      refine ⟨trivial, ?_, fun k hne => ?_⟩
      · rw [hs2GetEq fd.val, getFd_putSlot_self, hs1Mask]; exact congrArg some hupd
      · rw [hs2GetEq k, getFd_putSlot_ne _ hne, getFd_eq_of_fds_eq_local hs1Fds]

/-- Arbitrary-oracle safety specification for `postfork.fd_ops.relocate_rep_above2`. -/
theorem relocate_rep_above2_safety (s : ChildState) (hRun : s.status = .running) (fd : I32) :
    OkPost (postfork.fd_ops.relocate_rep_above2 s fd) fun p =>
      p.2.status = .running ∧ SameChildConfig p.2 s ∧
      p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
      p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
      p.2.fds.length ≤ s.fds.length + 1 ∧
      (∀ newFd, p.1 = .Ok newFd →
        2 < newFd.val ∧
        (∃ e f, s.getFd fd.val = some e ∧ p.2.getFd newFd.val = some f ∧
          f.desc = e.desc ∧ f.cloexec = true) ∧
        (fd.val ≤ 2 → newFd.val ≠ fd.val ∧ (oracleHasSeccomp s.oracle = false → p.2.getFd fd.val = none) ∧ s.getFd newFd.val = none) ∧
        (2 < fd.val → newFd = fd) ∧
        (∀ k, k ≠ fd.val → k ≠ newFd.val → p.2.getFd k = s.getFd k)) := by
  unfold postfork.fd_ops.relocate_rep_above2
  by_cases hneg : fd < 0#i32
  · simp only [hneg, ↓reduceIte]
    exact okPost_ok _ _ ⟨hRun, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl,
      Nat.le_succ _, fun _ h => by cases h⟩
  · simp only [hneg, ↓reduceIte]
    by_cases hle : fd ≤ 2#i32
    · have hleInt : fd.val ≤ 2 := hle
      simp only [hle, ↓reduceIte]
      obtain ⟨r1, s1, h1, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1, _, hErrFds1, hok1, _⟩ :=
        sys_fcntl_dupfd_cloexec_running s hRun fd 3#i32
      rw [h1, bind_ok]
      have hs1Run : s1.status = .running := hcfg1.status.trans hRun
      have hs1Len : s1.fds.length ≤ s.fds.length + 1 := by
        cases r1 with
        | Err e =>
          rw [hErrFds1 e rfl]
          exact Nat.le_succ _
        | Ok dst =>
          rcases hok1 dst rfl with ⟨_, _, _, _, _, _, _, _, hs1Fds⟩
          rw [hs1Fds]
          simp only [ChildState.putSlot, List.length_cons]
          exact Nat.succ_le_succ (eraseFdEntries_length_le s.fds _)
      cases r1 with
      | Err e =>
        exact okPost_ok _ _ ⟨hs1Run, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1, hs1Len, fun _ h => by cases h⟩
      | Ok dst =>
        rcases hok1 dst rfl with ⟨e, dstInt, hgetFd, _, hdstEq, hge3, _, hfree, hs1Fds⟩
        have h3v : (3#i32 : I32).val = 3 := rfl
        have hdstGt2 : 2 < dst.val := by omega
        obtain ⟨r2, s2, h2, hcfg2, hpg2, hcw2, hsi2, hde2, hwl2, _, hfds2, _⟩ :=
          sys_close_running s1 hs1Run fd
        have hs2Len : s2.fds.length ≤ s.fds.length + 1 := by
          have hcl : s2.fds.length ≤ s1.fds.length := by
            cases hf1 : currentFault s1 with
            | seccomp _ => simp [hfds2, hf1]
            | normal | fail _ | partialWrite _ | dentsBatch _ =>
              simp only [hf1] at hfds2
              rw [hfds2]
              exact eraseFdEntries_length_le s1.fds fd.val
          omega
        change OkPost (do let (_, s2) ← sys.close s1 fd; Result.ok (core.result.Result.Ok dst, s2)) _
        rw [h2, bind_ok]
        refine okPost_ok _ _ ⟨hcfg2.status.trans hs1Run, hcfg2.trans hcfg1,
          hpg2.trans hpg1, hcw2.trans hcw1, hsi2.trans hsi1, hde2.trans hde1, hwl2.trans hwl1,
          hs2Len, ?_⟩
        intro newFd hEq
        injection hEq with hNewEq
        subst hNewEq
        have hdstNe : dst.val ≠ fd.val := by omega
        have hs2GetNe : ∀ k, k ≠ fd.val → s2.getFd k = s1.getFd k := by
          intro k hkNe
          cases hf1 : currentFault s1 with
          | seccomp _ => simp [ChildState.getFd, hfds2, hf1]
          | normal | fail _ | partialWrite _ | dentsBatch _ =>
            simp only [hf1] at hfds2
            rw [getFd_eq_of_fds_eq_local hfds2]
            exact getFd_closeSlot_ne (s := s1) (fd := fd.val) (k := k) hkNe
        refine ⟨hdstGt2, ⟨e, { desc := e.desc, cloexec := true }, hgetFd, ?_, rfl, rfl⟩,
          fun _ => ⟨hdstNe, fun hNoSec => ?_, by rw [hdstEq]; exact hfree⟩, fun hgt2 => absurd hleInt (by omega), fun k hne1 hne2 => ?_⟩
        · rw [hs2GetNe dst.val hdstNe, getFd_eq_of_fds_eq_local hs1Fds, ← hdstEq, getFd_putSlot_self]
        · have hNoSec1 : oracleHasSeccomp s1.oracle = false := hcfg1.oracle.symm ▸ hNoSec
          cases hf1 : currentFault s1 with
          | seccomp rawE => exact absurd hf1 (fun h => not_seccomp_of_oracleHasSeccomp_false hNoSec1 h)
          | normal | fail _ | partialWrite _ | dentsBatch _ =>
            simp only [hf1] at hfds2
            rw [getFd_eq_of_fds_eq_local hfds2, getFd_closeSlot_self]
        · rw [hs2GetNe k hne1, getFd_eq_of_fds_eq_local hs1Fds, getFd_putSlot_ne _ (by omega)]
    · have hgt2 : 2 < fd.val := by change ¬ fd.val ≤ 2 at hle; omega
      simp only [hle, ↓reduceIte]
      refine okPost_bind (set_cloexec_safety s hRun fd) ?_
      rintro ⟨r1, s1⟩ ⟨hs1Run, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1, hs1Len, hok1⟩
      cases r1 with
      | Err e =>
        exact okPost_ok _ _ ⟨hs1Run, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1, hs1Len, fun _ h => by cases h⟩
      | Ok u =>
        refine okPost_ok _ _ ⟨hs1Run, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1, hs1Len, fun newFd hEq => ?_⟩
        have hNew : newFd = fd := by cases hEq; rfl
        have hct := hok1 (by cases u; rfl)
        rw [hNew]
        change CloexecTogglePost true s fd (.Ok ()) s1 at hct
        cases hget : s.getFd fd.val with
        | none => simp [CloexecTogglePost, hget] at hct
        | some e =>
          simp only [CloexecTogglePost, hget, true_and] at hct
          refine ⟨hgt2, ⟨e, _, rfl, hct.1, rfl, rfl⟩,
            fun hle' => absurd hgt2 (by omega), fun _ => rfl, fun k hne _ => hct.2 k hne⟩

/-- Arbitrary-oracle safety specification for `postfork.fd_ops.probe_open_slice`. -/
theorem probe_open_slice_safety (s : ChildState) (hRun : s.status = .running) (fds : Slice I32) :
    OkPost (postfork.fd_ops.probe_open_slice s fds) fun p =>
      p.2.status = .running ∧ SameChildConfig p.2 s ∧ p.2.fds = s.fds ∧
      p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
      p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
      (p.1 = .Ok () → ∀ fd ∈ fds.val, 0 ≤ fd.val → s.isOpen fd.val = true) := by
  unfold postfork.fd_ops.probe_open_slice postfork.fd_ops.probe_open_slice_loop
  let inv : ChildState × Usize → Prop := fun p =>
    p.1.status = .running ∧ SameChildConfig p.1 s ∧ p.1.fds = s.fds ∧
    p.1.pgid = s.pgid ∧ p.1.cwd = s.cwd ∧ p.1.sig = s.sig ∧
    p.1.descs = s.descs ∧ p.1.writeLog = s.writeLog ∧
    p.2.val ≤ fds.val.length ∧
    ∀ j (hj : j < fds.val.length), j < p.2.val → 0 ≤ fds.val[j].val →
      s.isOpen fds.val[j].val = true
  let post : ChildState × I32 × Bool → Prop := fun (s1, _, failed) =>
    s1.status = .running ∧ SameChildConfig s1 s ∧ s1.fds = s.fds ∧
    s1.pgid = s.pgid ∧ s1.cwd = s.cwd ∧ s1.sig = s.sig ∧
    s1.descs = s.descs ∧ s1.writeLog = s.writeLog ∧
    (failed = false → ∀ j (hj : j < fds.val.length), 0 ≤ fds.val[j].val →
      s.isOpen fds.val[j].val = true)
  have hLoop : OkPost (loop (fun (s1, i1) => postfork.fd_ops.probe_open_slice_loop.body fds fds.len s1 i1)
      (s, 0#usize)) post := by
    refine okPost_loop_decr_nat (fun p => fds.val.length - p.2.val) inv post _ (s, 0#usize) ?_
      ⟨hRun, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, fun _ _ h _ => by simp at h⟩
    intro ⟨s1, j⟩ ⟨hRun1, hcfg1, hfds1, hpg1, hcwd1, hsig1, hdescs1, hwl1, hjle, hprev⟩
    dsimp only at hjle hprev
    unfold postfork.fd_ops.probe_open_slice_loop.body
    by_cases hlt : j < fds.len
    · rcases slice_idx_succ_local fds hlt with ⟨hjlt, hidx, z, hinc, hval⟩
      simp only [hlt, ↓reduceIte]
      rw [hidx, bind_ok]
      by_cases hnonneg : fds.val[j.val] ≥ 0#i32
      · have hj_nonneg : 0 ≤ fds.val[j.val].val := hnonneg
        simp only [hnonneg, ↓reduceIte]
        obtain ⟨r, s2, hcall, hs2eq, _, _, hget2⟩ := sys_fcntl_getfd_running s1 hRun1 fds.val[j.val]
        rw [hcall, bind_ok]
        have hs2Cfg : SameChildConfig s2 s1 := by
          rw [hs2eq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        have hRun2 : s2.status = .running := by rw [hs2eq]; exact hRun1
        have hfds2 : s2.fds = s.fds := by rw [hs2eq]; exact hfds1
        have hpg2 : s2.pgid = s.pgid := by rw [hs2eq]; exact hpg1
        have hcw2 : s2.cwd = s.cwd := by rw [hs2eq]; exact hcwd1
        have hsi2 : s2.sig = s.sig := by rw [hs2eq]; exact hsig1
        have hde2 : s2.descs = s.descs := by rw [hs2eq]; exact hdescs1
        have hwl2 : s2.writeLog = s.writeLog := by rw [hs2eq]; exact hwl1
        cases r with
        | Err e =>
          exact okPost_ok _ _ ⟨hRun2, hs2Cfg.trans hcfg1, hfds2, hpg2, hcw2, hsi2, hde2, hwl2, fun h => by cases h⟩
        | Ok v =>
          have hOpenJ : s.isOpen fds.val[j.val].val = true := by
            unfold ChildState.isOpen
            rw [← getFd_eq_of_fds_eq_local hfds1]
            cases hG : s1.getFd fds.val[j.val].val with
            | none =>
              rw [hG] at hget2
              cases hf : currentFault s1 <;> (simp only [hf] at hget2; cases hget2)
            | some _ => rfl
          change OkPost (do let i1 ← j + 1#usize; Result.ok (ControlFlow.cont (s2, i1))) _
          rw [hinc, bind_ok]
          refine okPost_ok _ _ ⟨⟨hRun2, hs2Cfg.trans hcfg1, hfds2, hpg2, hcw2, hsi2, hde2, hwl2,
            by change z.val ≤ fds.val.length; rw [hval]; exact hjlt, fun k hk hlt' hk0 => ?_⟩, ?_⟩
          · change k < z.val at hlt'
            rw [hval] at hlt'
            by_cases hkj : k = j.val
            · subst hkj; exact hOpenJ
            · exact hprev k hk (by omega) hk0
          · change fds.val.length - z.val < fds.val.length - j.val
            rw [hval]; exact Nat.sub_succ_lt_self fds.val.length j.val hjlt
      · simp only [hnonneg, ↓reduceIte]
        rw [hinc, bind_ok]
        refine okPost_ok _ _ ⟨⟨hRun1, hcfg1, hfds1, hpg1, hcwd1, hsig1, hdescs1, hwl1,
          by change z.val ≤ fds.val.length; rw [hval]; exact hjlt, fun k hk hlt' hk0 => ?_⟩, ?_⟩
        · change k < z.val at hlt'
          rw [hval] at hlt'
          by_cases hkj : k = j.val
          · subst hkj; exact False.elim (hnonneg hk0)
          · exact hprev k hk (by omega) hk0
        · change fds.val.length - z.val < fds.val.length - j.val
          rw [hval]; exact Nat.sub_succ_lt_self fds.val.length j.val hjlt
    · simp only [hlt, ↓reduceIte]
      have hge : fds.val.length ≤ j.val := by
        have hlt' : ¬ j.val < fds.val.length := hlt
        omega
      exact okPost_ok _ _ ⟨hRun1, hcfg1, hfds1, hpg1, hcwd1, hsig1, hdescs1, hwl1,
        fun _ k hk hk0 => hprev k hk (Nat.lt_of_lt_of_le hk hge) hk0⟩
  refine okPost_bind hLoop ?_
  intro ⟨s1, err, failed⟩ ⟨hRun1, hcfg1, hfds1, hpg1, hcw1, hsig1, hdescs1, hwl1, hok⟩
  by_cases hfail : failed = true
  · simp only [hfail]
    exact okPost_ok _ _ ⟨hRun1, hcfg1, hfds1, hpg1, hcw1, hsig1, hdescs1, hwl1, fun h => by cases h⟩
  · have hfalse : failed = false := Bool.eq_false_iff.mpr hfail
    simp only [hfail]
    refine okPost_ok _ _ ⟨hRun1, hcfg1, hfds1, hpg1, hcw1, hsig1, hdescs1, hwl1, fun _ fd hmem h0 => ?_⟩
    rcases List.mem_iff_getElem.mp hmem with ⟨k, hk, hkeq⟩
    subst hkeq
    exact hok hfalse k hk h0

/-- Arbitrary-oracle safety specification for `postfork.fd_ops.clear_cloexec_slice`. -/
theorem clear_cloexec_slice_safety (s : ChildState) (hRun : s.status = .running) (fds : Slice I32) :
    OkPost (postfork.fd_ops.clear_cloexec_slice s fds) fun p =>
      p.2.status = .running ∧ SameChildConfig p.2 s ∧
      p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
      p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
      (p.1 = .Ok () →
        (∀ k : Int, (∀ fd ∈ fds.val, 0 ≤ fd.val → k ≠ fd.val) → p.2.getFd k = s.getFd k) ∧
        (∀ fd ∈ fds.val, 0 ≤ fd.val →
          ∃ e f, s.getFd fd.val = some e ∧ p.2.getFd fd.val = some f ∧
            f.desc = e.desc ∧ f.cloexec = false)) := by
  unfold postfork.fd_ops.clear_cloexec_slice postfork.fd_ops.clear_cloexec_slice_loop
  let inv : ChildState × Usize → Prop := fun p =>
    p.1.status = .running ∧ SameChildConfig p.1 s ∧
    p.1.pgid = s.pgid ∧ p.1.cwd = s.cwd ∧ p.1.sig = s.sig ∧
    p.1.descs = s.descs ∧ p.1.writeLog = s.writeLog ∧
    p.2.val ≤ fds.val.length ∧
    (∀ k : Int, (∀ j (hj : j < fds.val.length), j < p.2.val → 0 ≤ fds.val[j].val →
      k ≠ fds.val[j].val) → p.1.getFd k = s.getFd k) ∧
    (∀ j (hj : j < fds.val.length), j < p.2.val → 0 ≤ fds.val[j].val →
      ∃ e f, s.getFd fds.val[j].val = some e ∧ p.1.getFd fds.val[j].val = some f ∧
        f.desc = e.desc ∧ f.cloexec = false)
  let post : ChildState × I32 × Bool → Prop := fun (s1, _, failed) =>
    s1.status = .running ∧ SameChildConfig s1 s ∧
    s1.pgid = s.pgid ∧ s1.cwd = s.cwd ∧ s1.sig = s.sig ∧
    s1.descs = s.descs ∧ s1.writeLog = s.writeLog ∧
    (failed = false →
      (∀ k : Int, (∀ fd ∈ fds.val, 0 ≤ fd.val → k ≠ fd.val) → s1.getFd k = s.getFd k) ∧
      (∀ fd ∈ fds.val, 0 ≤ fd.val →
        ∃ e f, s.getFd fd.val = some e ∧ s1.getFd fd.val = some f ∧
          f.desc = e.desc ∧ f.cloexec = false))
  have hLoop : OkPost (loop (fun (s1, i1) => postfork.fd_ops.clear_cloexec_slice_loop.body fds fds.len s1 i1)
      (s, 0#usize)) post := by
    refine okPost_loop_decr_nat (fun p => fds.val.length - p.2.val) inv post _ (s, 0#usize) ?_
      ⟨hRun, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, Nat.zero_le _,
        fun _ _ => rfl, fun _ _ h _ => by simp at h⟩
    intro ⟨s1, j⟩ ⟨hRun1, hcfg1, hpg1, hcwd1, hsig1, hdescs1, hwl1, hjle, hother, hprev⟩
    dsimp only at hjle hother hprev
    unfold postfork.fd_ops.clear_cloexec_slice_loop.body
    by_cases hlt : j < fds.len
    · rcases slice_idx_succ_local fds hlt with ⟨hjlt, hidx, z, hinc, hval⟩
      simp only [hlt, ↓reduceIte]
      rw [hidx, bind_ok]
      by_cases hnonneg : fds.val[j.val] ≥ 0#i32
      · have hj_nonneg : 0 ≤ fds.val[j.val].val := hnonneg
        simp only [hnonneg, ↓reduceIte]
        refine okPost_bind (clear_cloexec_safety s1 hRun1 fds.val[j.val]) fun ⟨r, s2⟩ hs2 => ?_
        rcases hs2 with ⟨hRun2, hcfg2, hpg2, hcwd2, hsig2, hdescs2, hwl2, hok2⟩
        cases r with
        | Err e =>
          exact okPost_ok _ _ ⟨hRun2, hcfg2.trans hcfg1, hpg2.trans hpg1, hcwd2.trans hcwd1,
            hsig2.trans hsig1, hdescs2.trans hdescs1, hwl2.trans hwl1, fun h => by cases h⟩
        | Ok u =>
          have hct := hok2 (by cases u; rfl)
          change CloexecTogglePost false s1 fds.val[j.val] (.Ok ()) s2 at hct
          cases hs1J : s1.getFd fds.val[j.val].val with
          | none => simp [CloexecTogglePost, hs1J] at hct
          | some e1 =>
            simp only [CloexecTogglePost, hs1J, true_and] at hct
            rcases hct with ⟨hs2J, hs2Ne⟩
            change OkPost (do let i1 ← j + 1#usize; Result.ok (ControlFlow.cont (s2, i1))) _
            rw [hinc, bind_ok]
            refine okPost_ok _ _ ⟨⟨hRun2, hcfg2.trans hcfg1, hpg2.trans hpg1, hcwd2.trans hcwd1,
              hsig2.trans hsig1, hdescs2.trans hdescs1, hwl2.trans hwl1,
              by change z.val ≤ fds.val.length; rw [hval]; exact hjlt, fun k hk => ?_, fun m hm hlt' hm0 => ?_⟩, ?_⟩
            · have hkPrev : s1.getFd k = s.getFd k := by
                apply hother k
                intro l hl hltl hl0
                exact hk l hl (by change l < z.val; rw [hval]; omega) hl0
              have hkne : k ≠ fds.val[j.val].val :=
                hk j.val hjlt (by change j.val < z.val; rw [hval]; omega) hj_nonneg
              rw [hs2Ne k hkne, hkPrev]
            · change m < z.val at hlt'
              rw [hval] at hlt'
              by_cases hmj : m = j.val
              · subst hmj
                by_cases hseen : ∃ p, ∃ hp : p < j.val, fds.val[p].val = fds.val[j.val].val
                · rcases hseen with ⟨p, hp, hpeq⟩
                  rcases hprev p (by omega) hp (by omega) with ⟨e0, fp, hs0, hs1p, hdp, _⟩
                  have he1Eq : e1.desc = e0.desc := by
                    rw [hpeq] at hs1p
                    rw [hs1p] at hs1J
                    cases hs1J
                    exact hdp
                  exact ⟨e0, _, hpeq ▸ hs0, hs2J, he1Eq, rfl⟩
                · have hsJ : s.getFd fds.val[j.val].val = some e1 := by
                    have hPrevK : s1.getFd fds.val[j.val].val = s.getFd fds.val[j.val].val := by
                      apply hother fds.val[j.val].val
                      intro p _ hpm hp0 heq
                      exact hseen ⟨p, hpm, heq.symm⟩
                    rw [← hPrevK, hs1J]
                  exact ⟨e1, _, hsJ, hs2J, rfl, rfl⟩
              · rcases hprev m hm (by omega) hm0 with ⟨e0, f0, hs0, hs1m, hdm, hcm⟩
                by_cases hmeq : fds.val[m].val = fds.val[j.val].val
                · have he1Eq : e1.desc = e0.desc := by
                    rw [hmeq] at hs1m
                    rw [hs1m] at hs1J
                    cases hs1J
                    exact hdm
                  exact ⟨e0, { desc := e1.desc, cloexec := false, extraFdFlags := expectedExtraFlagsAfterSetfd s1 e1 },
                    hs0, by rw [hmeq]; exact hs2J, he1Eq, rfl⟩
                · exact ⟨e0, f0, hs0, by rw [hs2Ne _ hmeq]; exact hs1m, hdm, hcm⟩
            · change fds.val.length - z.val < fds.val.length - j.val
              rw [hval]; exact Nat.sub_succ_lt_self fds.val.length j.val hjlt
      · simp only [hnonneg, ↓reduceIte]
        rw [hinc, bind_ok]
        refine okPost_ok _ _ ⟨⟨hRun1, hcfg1, hpg1, hcwd1, hsig1, hdescs1, hwl1,
          by change z.val ≤ fds.val.length; rw [hval]; exact hjlt, fun k hk => ?_, fun m hm hlt' hm0 => ?_⟩, ?_⟩
        · apply hother k
          intro l hl hltl hl0
          exact hk l hl (by change l < z.val; rw [hval]; omega) hl0
        · change m < z.val at hlt'
          rw [hval] at hlt'
          by_cases hmj : m = j.val
          · subst hmj; exact False.elim (hnonneg hm0)
          · exact hprev m hm (by omega) hm0
        · change fds.val.length - z.val < fds.val.length - j.val
          rw [hval]; exact Nat.sub_succ_lt_self fds.val.length j.val hjlt
    · simp only [hlt, ↓reduceIte]
      have hge : fds.val.length ≤ j.val := by
        have hlt' : ¬ j.val < fds.val.length := hlt
        omega
      refine okPost_ok _ _ ⟨hRun1, hcfg1, hpg1, hcwd1, hsig1, hdescs1, hwl1, fun _ => ⟨?_, ?_⟩⟩
      · intro k hk
        apply hother k
        intro l hl _ hl0
        exact hk fds.val[l] (List.getElem_mem hl) hl0
      · intro fd hmem h0
        rcases List.mem_iff_getElem.mp hmem with ⟨m, hm, hmeq⟩
        subst hmeq
        exact hprev m hm (Nat.lt_of_lt_of_le hm hge) h0
  refine okPost_bind hLoop ?_
  intro ⟨s1, err, failed⟩ ⟨hRun1, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1, hok⟩
  by_cases hfail : failed = true
  · simp only [hfail]
    exact okPost_ok _ _ ⟨hRun1, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1, fun h => by cases h⟩
  · have hfalse : failed = false := Bool.eq_false_iff.mpr hfail
    simp only [hfail]
    exact okPost_ok _ _ ⟨hRun1, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1, fun _ => hok hfalse⟩

/-- Arbitrary-oracle safety and trace specification for `postfork.fd_ops.close_unused_slice`. -/
theorem close_unused_slice_safety (s : ChildState) (hRun : s.status = .running) (fds : Slice I32) :
    OkPost (postfork.fd_ops.close_unused_slice s fds) fun s' =>
      s'.status = .running ∧ SameChildConfig s' s ∧
      s'.pgid = s.pgid ∧ s'.cwd = s.cwd ∧ s'.sig = s.sig ∧
      s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
      s'.fds.length ≤ s.fds.length ∧
      (∀ k, Model.sliceContainsNonnegSpec fds.val k = false → s'.getFd k = s.getFd k) ∧
      (oracleHasSeccomp s.oracle = false →
        ∀ k, s'.getFd k = if Model.sliceContainsNonnegSpec fds.val k = true then none else s.getFd k) ∧
      ∃ suf, s'.trace = s.trace ++ suf ∧
        (∀ ev ∈ suf, ∃ fd, ∃ out, ev = Event.mk (.close fd) out) ∧
        (∀ cfd ∈ fds.val, 0#i32 ≤ cfd → ∃ out, Event.mk (.close cfd) out ∈ suf) := by
  unfold postfork.fd_ops.close_unused_slice postfork.fd_ops.close_unused_slice_loop
  let inv : ChildState × Usize → Prop := fun p =>
    p.1.status = .running ∧ SameChildConfig p.1 s ∧
    p.1.pgid = s.pgid ∧ p.1.cwd = s.cwd ∧ p.1.sig = s.sig ∧
    p.1.descs = s.descs ∧ p.1.writeLog = s.writeLog ∧ p.1.fds.length ≤ s.fds.length ∧ p.2 ≤ fds.len ∧
    (∀ k, Model.sliceContainsNonnegSpec (fds.val.take p.2.val) k = false → p.1.getFd k = s.getFd k) ∧
    (oracleHasSeccomp s.oracle = false →
      ∀ k, p.1.getFd k =
        if Model.sliceContainsNonnegSpec (fds.val.take p.2.val) k = true then none else s.getFd k) ∧
    ∃ suf, p.1.trace = s.trace ++ suf ∧
      (∀ ev ∈ suf, ∃ fd, ∃ out, ev = Event.mk (.close fd) out) ∧
      (∀ j (hj : j < fds.val.length), j < p.2.val → 0#i32 ≤ fds.val[j] →
        ∃ out, Event.mk (.close fds.val[j]) out ∈ suf)
  let post : ChildState → Prop := fun s' =>
    s'.status = .running ∧ SameChildConfig s' s ∧
    s'.pgid = s.pgid ∧ s'.cwd = s.cwd ∧ s'.sig = s.sig ∧
    s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
    s'.fds.length ≤ s.fds.length ∧
    (∀ k, Model.sliceContainsNonnegSpec fds.val k = false → s'.getFd k = s.getFd k) ∧
    (oracleHasSeccomp s.oracle = false →
      ∀ k, s'.getFd k = if Model.sliceContainsNonnegSpec fds.val k = true then none else s.getFd k) ∧
    ∃ suf, s'.trace = s.trace ++ suf ∧
      (∀ ev ∈ suf, ∃ fd, ∃ out, ev = Event.mk (.close fd) out) ∧
      (∀ cfd ∈ fds.val, 0#i32 ≤ cfd → ∃ out, Event.mk (.close cfd) out ∈ suf)
  refine okPost_loop_decr_nat (fun p => fds.len.val - p.2.val) inv post
    (fun p => postfork.fd_ops.close_unused_slice_loop.body fds fds.len p.1 p.2) (s, 0#usize) ?_
    ⟨hRun, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, by scalar_tac,
      fun k _ => rfl, fun _ k => by simp [Model.sliceContainsNonnegSpec],
      ⟨[], by simp, fun _ h => by simp at h, fun _ _ h _ => by simp at h⟩⟩
  intro ⟨s1, idx⟩ ⟨hRun1, hcfg1, hpg1, hcwd1, hsig1, hdescs1, hwl1, hlen1, hidxLe, hKeep1, hget1, suf1, htr1, hevs1, hcl1⟩
  dsimp only at hidxLe hKeep1 hget1 hcl1
  unfold postfork.fd_ops.close_unused_slice_loop.body
  by_cases hlt : idx < fds.len
  · rcases slice_idx_succ_local fds hlt with ⟨hjlt, hidx, idx1, hinc, hval⟩
    simp only [hlt, ↓reduceIte]
    rw [hidx, bind_ok]
    have htakeSucc : fds.val.take (idx.val + 1) = fds.val.take idx.val ++ [fds.val[idx.val]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hjlt]; rfl
    have hstep : OkPost
        (if fds.val[idx.val] ≥ 0#i32 then do let (_, s2) ← sys.close s1 fds.val[idx.val]; Result.ok s2
         else Result.ok s1)
        fun s2 =>
          s2.status = .running ∧ SameChildConfig s2 s ∧
          s2.pgid = s.pgid ∧ s2.cwd = s.cwd ∧ s2.sig = s.sig ∧
          s2.descs = s.descs ∧ s2.writeLog = s.writeLog ∧
          s2.fds.length ≤ s.fds.length ∧
          (∀ k, Model.sliceContainsNonnegSpec (fds.val.take (idx.val + 1)) k = false → s2.getFd k = s.getFd k) ∧
          (oracleHasSeccomp s.oracle = false →
            ∀ k, s2.getFd k =
              if Model.sliceContainsNonnegSpec (fds.val.take (idx.val + 1)) k = true then none else s.getFd k) ∧
          ∃ suf2, s2.trace = s.trace ++ suf2 ∧
            (∀ ev ∈ suf2, ∃ fd, ∃ out, ev = Event.mk (.close fd) out) ∧
            (∀ j (hj : j < fds.val.length), j < idx.val + 1 → 0#i32 ≤ fds.val[j] →
              ∃ out, Event.mk (.close fds.val[j]) out ∈ suf2) := by
      by_cases hnonneg : fds.val[idx.val] ≥ 0#i32
      · simp only [hnonneg, ↓reduceIte]
        obtain ⟨r2, s2, h2eq, hcfg2, hpg2, hcwd2, hsig2, hdescs2, hwl2, _, hfds2, _⟩ :=
          sys_close_running s1 hRun1 fds.val[idx.val]
        have hlen2 : s2.fds.length ≤ s.fds.length := by
          have hcl : s2.fds.length ≤ s1.fds.length := by
            cases hf1 : currentFault s1 with
            | seccomp _ => simp [hfds2, hf1]
            | normal | fail _ | partialWrite _ | dentsBatch _ =>
              simp only [hf1] at hfds2
              rw [hfds2]
              exact eraseFdEntries_length_le s1.fds _
          exact Nat.le_trans hcl hlen1
        have hs2Trace : ∃ out, s2.trace = s1.trace ++ [Event.mk (.close fds.val[idx.val]) out] := by
          unfold sys.close LeanSwe.PostFork.Aeneas.Internal.Sys.close runUnitSyscall at h2eq
          rw [hRun1] at h2eq
          cases hf : currentFault s1 with
          | seccomp rawE =>
            simp only [hf, Result.ok.injEq] at h2eq
            have hs2 : s2 = _ := (congrArg Prod.snd h2eq).symm
            rw [hs2]; exact ⟨_, rfl⟩
          | fail rawE =>
            simp only [hf] at h2eq
            by_cases hopen : s1.isOpen fds.val[idx.val].val = true
            · simp only [hopen, ↓reduceIte, Result.ok.injEq] at h2eq
              have hs2 : s2 = _ := (congrArg Prod.snd h2eq).symm
              rw [hs2]; exact ⟨_, rfl⟩
            · simp only [hopen, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at h2eq
              have hs2 : s2 = _ := (congrArg Prod.snd h2eq).symm
              rw [hs2]; exact ⟨_, rfl⟩
          | normal | partialWrite _ | dentsBatch _ =>
            simp only [hf] at h2eq
            by_cases hopen : s1.isOpen fds.val[idx.val].val = true
            · simp only [hopen, ↓reduceIte, Result.ok.injEq] at h2eq
              have hs2 : s2 = _ := (congrArg Prod.snd h2eq).symm
              rw [hs2]; exact ⟨_, rfl⟩
            · simp only [hopen, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at h2eq
              have hs2 : s2 = _ := (congrArg Prod.snd h2eq).symm
              rw [hs2]; exact ⟨_, rfl⟩
        rcases hs2Trace with ⟨out2, htr2⟩
        change OkPost (do let (_, s2') ← sys.close s1 fds.val[idx.val]; Result.ok s2') _
        rw [h2eq, bind_ok]
        refine okPost_ok _ _ ⟨hcfg2.status.trans hRun1, hcfg2.trans hcfg1, hpg2.trans hpg1,
          hcwd2.trans hcwd1, hsig2.trans hsig1, hdescs2.trans hdescs1, hwl2.trans hwl1, hlen2,
          fun k hkFalse => ?_, fun hNoSec k => ?_, suf1 ++ [Event.mk (.close fds.val[idx.val]) out2], ?_, ?_, ?_⟩
        · have hk0 : 0 ≤ fds.val[idx.val].val := by scalar_tac
          have hkNe : k ≠ fds.val[idx.val].val := by
            intro heq
            subst heq
            rw [htakeSucc] at hkFalse
            simp only [Model.sliceContainsNonnegSpec, hk0, decide_true, Bool.true_and,
              List.any_append, List.any_cons, List.any_nil, beq_self_eq_true, Bool.or_false,
              Bool.or_true] at hkFalse
            cases hkFalse
          have hkFalsePrev : Model.sliceContainsNonnegSpec (fds.val.take idx.val) k = false := by
            by_cases hk0' : 0 ≤ k
            · rw [htakeSucc] at hkFalse
              simp only [Model.sliceContainsNonnegSpec, hk0', decide_true, Bool.true_and,
                List.any_append, List.any_cons, List.any_nil, Bool.or_false] at hkFalse ⊢
              exact (Bool.or_eq_false_iff.mp hkFalse).1
            · simp [Model.sliceContainsNonnegSpec, hk0']
          have hGetNe : s2.getFd k = s1.getFd k := by
            cases hf1 : currentFault s1 with
            | seccomp _ => simp [ChildState.getFd, hfds2, hf1]
            | normal | fail _ | partialWrite _ | dentsBatch _ =>
              simp only [hf1] at hfds2
              rw [getFd_eq_of_fds_eq_local hfds2, ChildState.closeSlot, ChildState.getFd,
                find?_eraseFdEntries_ne s1.fds hkNe]
              rfl
          rw [hGetNe, hKeep1 k hkFalsePrev]
        · have hNoSec1 : oracleHasSeccomp s1.oracle = false := hcfg1.oracle.symm ▸ hNoSec
          have hfds2' : s2.fds = (s1.closeSlot fds.val[idx.val].val).fds := by
            cases hf1 : currentFault s1 with
            | seccomp rawE => exact absurd hf1 (fun h => not_seccomp_of_oracleHasSeccomp_false hNoSec1 h)
            | normal | fail _ | partialWrite _ | dentsBatch _ => simp [hfds2, hf1]
          rw [getFd_eq_of_fds_eq_local hfds2', ChildState.closeSlot]
          by_cases hk : k = fds.val[idx.val].val
          · subst hk
            have hk0 : 0 ≤ fds.val[idx.val].val := hnonneg
            rw [ChildState.getFd, find?_eraseFdEntries_self, htakeSucc]
            simp only [Model.sliceContainsNonnegSpec, hk0, decide_true, Bool.true_and,
              List.any_append, List.any_cons, List.any_nil, beq_self_eq_true, Bool.or_false,
              Bool.or_true, ↓reduceIte]
          · rw [ChildState.getFd, find?_eraseFdEntries_ne s1.fds hk]
            change s1.getFd k = _
            rw [hget1 hNoSec k, htakeSucc]
            have hne : (fds.val[idx.val].val == k) = false := beq_false_of_ne (Ne.symm hk)
            simp only [Model.sliceContainsNonnegSpec, List.any_append, List.any_cons,
              List.any_nil, hne, Bool.or_false]
            rfl
        · rw [htr2, htr1, List.append_assoc]
        · intro ev hev
          rcases List.mem_append.mp hev with hev1 | hev2
          · exact hevs1 ev hev1
          · rcases List.mem_singleton.mp hev2 with rfl
            exact ⟨_, out2, rfl⟩
        · intro j hj hltj hj0
          by_cases hje : j = idx.val
          · subst hje; exact ⟨out2, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
          · rcases hcl1 j hj (by omega) hj0 with ⟨o, ho⟩
            exact ⟨o, List.mem_append_left _ ho⟩
      · simp only [hnonneg, ↓reduceIte]
        have hFdsKeep : ∀ k,
            Model.sliceContainsNonnegSpec (fds.val.take (idx.val + 1)) k =
              Model.sliceContainsNonnegSpec (fds.val.take idx.val) k := by
          intro k
          rw [htakeSucc]
          by_cases hk0 : 0 ≤ k
          · have hne : (fds.val[idx.val].val == k) = false := beq_false_of_ne (by
              have : fds.val[idx.val].val < 0 := by scalar_tac
              omega)
            simp only [Model.sliceContainsNonnegSpec, hk0, decide_true, Bool.true_and,
              List.any_append, List.any_cons, List.any_nil, hne, Bool.or_false]
          · simp only [Model.sliceContainsNonnegSpec, hk0, decide_false, Bool.false_and]
        refine okPost_ok _ _ ⟨hRun1, hcfg1, hpg1, hcwd1, hsig1, hdescs1, hwl1, hlen1,
          fun k hk => hKeep1 k (by rw [← hFdsKeep k]; exact hk),
          fun hNoSec k => by rw [hFdsKeep k]; exact hget1 hNoSec k,
          suf1, htr1, hevs1, fun j hj hltj hj0 => ?_⟩
        · by_cases hje : j = idx.val
          · subst hje; exact False.elim (hnonneg hj0)
          · exact hcl1 j hj (by omega) hj0
    refine okPost_bind hstep fun s2 ⟨hRun2, hcfg2, hpg2, hcwd2, hsig2, hdescs2, hwl2, hlen2, hKeep2, hget2, suf2, htr2, hevs2, hcl2⟩ => ?_
    rw [hinc, bind_ok]
    refine okPost_ok _ _ ⟨⟨hRun2, hcfg2, hpg2, hcwd2, hsig2, hdescs2, hwl2, hlen2,
      by change idx1.val ≤ fds.len.val; rw [hval]; exact hjlt,
      fun k hk => by change Model.sliceContainsNonnegSpec (fds.val.take idx1.val) k = false at hk; rw [hval] at hk; exact hKeep2 k hk,
      fun hNoSec k => by change s2.getFd k = if Model.sliceContainsNonnegSpec (fds.val.take idx1.val) k = true then none else s.getFd k; rw [hget2 hNoSec k, hval],
      suf2, htr2, hevs2, fun j hj hltj hj0 => by change j < idx1.val at hltj; rw [hval] at hltj; exact hcl2 j hj hltj hj0⟩, ?_⟩
    change fds.len.val - idx1.val < fds.len.val - idx.val
    rw [hval]; exact Nat.sub_succ_lt_self fds.len.val idx.val hjlt
  · simp only [hlt, ↓reduceIte]
    have hjge : fds.val.length ≤ idx.val := by
      have : ¬ idx.val < fds.val.length := by simpa [Slice.len] using hlt
      omega
    refine okPost_ok _ _ ⟨hRun1, hcfg1, hpg1, hcwd1, hsig1, hdescs1, hwl1, hlen1,
      fun k hk => hKeep1 k (by rw [List.take_of_length_le hjge]; exact hk),
      fun hNoSec k => by rw [hget1 hNoSec k, List.take_of_length_le hjge],
      suf1, htr1, hevs1, fun cfd hmem hc0 => ?_⟩
    · rcases List.mem_iff_getElem.mp hmem with ⟨j, hj, hjeq⟩
      subst hjeq
      exact hcl1 j hj (Nat.lt_of_lt_of_le hj hjge) hc0

end SafetyFdOps

section NotRunningAndExecHelpers

/-- `postfork.fd_ops.slice_contains_nonneg` total evaluation wrapper. -/
theorem slice_contains_nonneg_total (fds : Slice I32) (target : I32) :
    OkPost (postfork.fd_ops.slice_contains_nonneg fds target) (fun _ => True) :=
  okPost_mono (slice_contains_nonneg_spec fds target) (fun _ _ => trivial)

/-- `postfork.fd_ops.slice_has_stdio_slot` total evaluation wrapper. -/
theorem slice_has_stdio_slot_total (fds : Slice I32) :
    OkPost (postfork.fd_ops.slice_has_stdio_slot fds) (fun _ => True) :=
  okPost_mono (slice_has_stdio_slot_spec fds) (fun _ _ => trivial)

/-- `postfork.fd_ops.slices_overlap_nonneg` total evaluation wrapper. -/
theorem slices_overlap_nonneg_total (lhs rhs : Slice I32) :
    OkPost (postfork.fd_ops.slices_overlap_nonneg lhs rhs) (fun _ => True) :=
  okPost_mono (slices_overlap_nonneg_spec lhs rhs) (fun _ _ => trivial)

/-- Executing `sys.sig_dfl` on `SIGPIPE = 13#i32` sets signal `13` to `.default` on success while keeping non-`13` dispositions intact. -/
theorem sig_dfl_13_post (s : ChildState) (hRun : s.status = .running) :
    ∃ r s', sys.sig_dfl s postfork.child.SIGPIPE = Result.ok (r, s') ∧
      s'.status = .running ∧ SameChildConfig s' s ∧
      s'.fds = s.fds ∧ s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
      s'.cwd = s.cwd ∧ s'.pgid = s.pgid ∧
      (r = .Ok () →
        s'.getSig 13 = .default ∧ ∀ g : Int, g ≠ 13 → s'.getSig g = s.getSig g) ∧
      (s.oracle = [] → r = .Ok ()) := by
  obtain ⟨r, s', hEq, hcfg, hfds, hdescs, hwl, hcwd, hpgid, _, _, hsigOk, hOr⟩ :=
    sys_sig_dfl_running s hRun postfork.child.SIGPIPE
  have hInv : isInvalidSigactionSig postfork.child.SIGPIPE = false := by
    rw [child_sigpipe_eq]; decide
  refine ⟨r, s', hEq, hcfg.status.trans hRun, hcfg, hfds, hdescs, hwl, hcwd, hpgid,
    fun hr => ?_, fun hor => (hOr hor).2 hInv⟩
  have hSigEq := hsigOk hr
  have h13 : (postfork.child.SIGPIPE : I32).val = 13 := by rw [child_sigpipe_eq]; decide
  refine ⟨?_, fun g hg => ?_⟩
  · simp only [ChildState.getSig, hSigEq, h13]
    exact getSig_putSig_self s 13 .default
  · simp only [ChildState.getSig, hSigEq, h13]
    exact getSig_putSig_ne s hg .default

/-- Executing `sys.sig_unblock` on `SIGPIPE = 13#i32` removes `13` from `blockedSigs` on success while keeping `sig` intact. -/
theorem sig_unblock_13_post (s : ChildState) (hRun : s.status = .running) :
    ∃ r s', sys.sig_unblock s postfork.child.SIGPIPE = Result.ok (r, s') ∧
      s'.status = .running ∧ SameChildConfig s' s ∧
      s'.fds = s.fds ∧ s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
      s'.cwd = s.cwd ∧ s'.pgid = s.pgid ∧ s'.sig = s.sig ∧
      (r = .Ok () → s'.blockedSigs = s.blockedSigs.filter (· != 13)) ∧
      (s.oracle = [] → r = .Ok ()) := by
  obtain ⟨r, s', hEq, hcfg, hfds, hdescs, hwl, hcwd, hpgid, hsig, _, _, hblkOk, hOr⟩ :=
    sys_sig_unblock_running s hRun postfork.child.SIGPIPE
  have h13 : (postfork.child.SIGPIPE : I32).val = 13 := by rw [child_sigpipe_eq]; decide
  refine ⟨r, s', hEq, hcfg.status.trans hRun, hcfg, hfds, hdescs, hwl, hcwd, hpgid, hsig,
    fun hr => by simpa [h13] using hblkOk hr, fun hor => (hOr hor).2 (by omega) (by omega)⟩

/-- `imageOf` signal postcondition when `sLast.getSig 13 = .default` and all other `g ≠ 13` equal `s.getSig g`. -/
theorem execImageGetSig_of_sigpipe_reset (s sLast : ChildState)
    (path : Bytes) (argv envp : List Bytes)
    (h13 : sLast.getSig 13 = .default)
    (hOther : ∀ g : Int, g ≠ 13 → sLast.getSig g = s.getSig g) :
    execImageGetSig (imageOf sLast path argv envp) 13 = .default ∧
    ∀ g : Int, g ≠ 13 →
      execImageGetSig (imageOf sLast path argv envp) g =
        if s.getSig g == .ignore then .ignore else .default := by
  refine ⟨?_, fun g hg => ?_⟩
  · rw [execImageGetSig_imageOf, h13]
  · rw [execImageGetSig_imageOf, hOther g hg]
    cases s.getSig g <;> rfl

/-- Filtering `13` out of `blockedSigs` ensures `(blockedSigs.filter (· != 13)).contains 13 = false`. -/
theorem blockedSigs_filter13_not_contains13 (xs : List Int) :
    (xs.filter (· != 13)).contains 13 = false := by
  rw [Bool.eq_false_iff]
  intro hMem
  have hM := List.contains_iff_mem.mp hMem
  have hP := (List.mem_filter.mp hM).2
  simp at hP

/-- When every non-negative open FD in `sNow` is `0`, `1`, `2`, `extra`, or already open in `sOrig`,
and `min sNow.fdLimit 2^31 ≥ 6 + sOrig.fds.length`, `findLowestFreeFd sNow 0` always succeeds. -/
theorem findLowestFreeFd_after_setupStdio (sOrig sNow : ChildState) (extra : Int)
    (hLim : min sNow.fdLimit 2147483648 ≥ 6 + Int.ofNat sOrig.fds.length)
    (hOpen : ∀ x : Int, 0 ≤ x → sNow.isOpen x = true →
      x = 0 ∨ x = 1 ∨ x = 2 ∨ x = extra ∨ sOrig.isOpen x = true) :
    ∃ dirfd, findLowestFreeFd sNow 0 = some dirfd := by
  let bound : List Int := [0, 1, 2, extra] ++ sOrig.fds.map Prod.fst
  refine findLowestFreeFd_some_of_card_lt sNow 0 bound (le_refl 0) ?_ ?_
  · simp only [bound, List.length_append, List.length_cons, List.length_nil, List.length_map,
      Int.ofNat_eq_natCast, Nat.cast_add] at *
    omega
  · intro x hx0 hxOpen
    rcases hOpen x hx0 hxOpen with rfl | rfl | rfl | rfl | hOrig
    · exact List.mem_append_left _ (by simp)
    · exact List.mem_append_left _ (by simp)
    · exact List.mem_append_left _ (by simp)
    · exact List.mem_append_left _ (by simp)
    · refine List.mem_append_right _ ?_
      rw [isOpen_iff_isSome, ChildState.getFd] at hOrig
      cases hfind : sOrig.fds.find? (fun p => p.1 == x) with
      | none => rw [hfind] at hOrig; simp at hOrig
      | some p =>
        have hfst : p.1 = x := beq_iff_eq.mp (List.find?_some (p := fun q : Int × FdEntry => q.1 == x) hfind)
        exact hfst ▸ List.mem_map.mpr ⟨p, List.mem_of_find?_eq_some hfind, rfl⟩

/-- `sys.setpgid_self` always terminates on any `ChildState`. -/
theorem sys_setpgid_self_total (s : ChildState) :
    OkPost (sys.setpgid_self s) (fun _ => True) := by
  by_cases hrun : s.status = .running
  · obtain ⟨r, s', h, _⟩ := sys_setpgid_self_running s hrun
    exact ⟨(r, s'), h, trivial⟩
  · unfold sys.setpgid_self LeanSwe.PostFork.Aeneas.Internal.Sys.setpgid_self
    rw [runUnitSyscall_not_running s hrun]
    exact okPost_ok _ _ trivial

/-- `sys.sig_dfl` always terminates on any `ChildState`. -/
theorem sys_sig_dfl_total (s : ChildState) (sig : I32) :
    OkPost (sys.sig_dfl s sig) (fun _ => True) := by
  by_cases hrun : s.status = .running
  · obtain ⟨r, s', h, _⟩ := sys_sig_dfl_running s hrun sig
    exact ⟨(r, s'), h, trivial⟩
  · have hNotRunB : (s.status == Status.running) = false := beq_false_of_ne hrun
    unfold sys.sig_dfl LeanSwe.PostFork.Aeneas.Internal.Sys.sig_dfl
    simp only [hNotRunB, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [runUnitSyscall_not_running s hrun]
    exact okPost_ok _ _ trivial

/-- `sys.sig_unblock` always terminates on any `ChildState`. -/
theorem sys_sig_unblock_total (s : ChildState) (sig : I32) :
    OkPost (sys.sig_unblock s sig) (fun _ => True) := by
  by_cases hrun : s.status = .running
  · obtain ⟨r, s', h, _⟩ := sys_sig_unblock_running s hrun sig
    exact ⟨(r, s'), h, trivial⟩
  · have hNotRunB : (s.status == Status.running) = false := beq_false_of_ne hrun
    unfold sys.sig_unblock LeanSwe.PostFork.Aeneas.Internal.Sys.sig_unblock
    simp only [hNotRunB, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [runUnitSyscall_not_running s hrun]
    exact okPost_ok _ _ trivial

/-- `sys.chdir` always terminates on any `ChildState`. -/
theorem sys_chdir_total (s : ChildState) (path : sys.CStr) :
    OkPost (sys.chdir s path) (fun _ => True) := by
  by_cases hrun : s.status = .running
  · obtain ⟨r, s', h, _⟩ := sys_chdir_running s hrun path
    exact ⟨(r, s'), h, trivial⟩
  · unfold sys.chdir LeanSwe.PostFork.Aeneas.Internal.Sys.chdir
    rw [runUnitSyscall_not_running s hrun]
    exact okPost_ok _ _ trivial

/-- `sys.execve` always terminates on any `ChildState`. -/
theorem sys_execve_total (s : ChildState) (path : sys.CStr) (argv envp : sys.CStrArray) :
    OkPost (sys.execve s path argv envp) (fun _ => True) := by
  by_cases hrun : s.status = .running
  · obtain ⟨r, s', h, _⟩ := sys_execve_running s hrun path argv envp
    exact ⟨(r, s'), h, trivial⟩
  · have h := sys_execve_not_running s hrun path argv envp
    exact ⟨(0#i32, s), h, trivial⟩

/-- `sys.exit` always terminates on any `ChildState`. -/
theorem sys_exit_total (s : ChildState) (code : I32) :
    OkPost (sys.exit s code) (fun _ => True) := by
  unfold sys.exit LeanSwe.PostFork.Aeneas.Internal.Sys.exit
  cases s.status <;> exact okPost_ok _ _ trivial

/-- `report_and_exit` always terminates on any `ChildState`. -/
theorem report_and_exit_total (s : ChildState) (repW : I32) (stage : U8) (errnum fallback : I32) :
    OkPost (postfork.child.report_and_exit s repW stage errnum fallback) (fun _ => True) := by
  by_cases hrun : s.status = .running
  · exact okPost_mono (report_and_exit_status127 s hrun repW stage errnum fallback) (fun _ _ => trivial)
  · exact okPost_mono (report_and_exit_not_running s hrun repW stage errnum fallback) (fun _ _ => trivial)

/-- `read_sync_byte` always terminates on any `ChildState`. -/
theorem read_sync_byte_total (s : ChildState) (fd : I32) :
    OkPost (postfork.child.read_sync_byte s fd) (fun _ => True) :=
  okPost_mono (read_sync_byte_spec s fd) (fun _ _ => trivial)

/-- Combine two `OkPost` guarantees on the same deterministic `Result` computation. -/
theorem okPost_and {α : Type} {m : Result α} {P Q : α → Prop}
    (hP : OkPost m P) (hQ : OkPost m Q) : OkPost m (fun a => P a ∧ Q a) := by
  rcases hP with ⟨a, ha, hp⟩
  rcases hQ with ⟨b, hb, hq⟩
  rw [ha, Result.ok.injEq] at hb
  subst hb
  exact ⟨a, ha, hp, hq⟩

private theorem isOpen_mem_map_fst (s : ChildState) (x : Int) (hx : s.isOpen x = true) :
    x ∈ s.fds.map Prod.fst := by
  unfold ChildState.isOpen ChildState.getFd at hx
  rcases s with ⟨pid, sid, pgid, fds, rest⟩
  dsimp only at hx ⊢
  induction fds with
  | nil => cases hx
  | cons p tl ih =>
    by_cases hp : p.1 == x
    · have hpx : p.1 = x := by simpa using hp
      exact hpx ▸ List.mem_cons_self
    · have hp' : (p.1 == x) = false := by cases h : p.1 == x <;> simp_all
      simp only [List.find?, hp'] at hx
      exact List.mem_cons_of_mem _ (ih hx)

/-- Under `s.oracle = []`, an open non-negative `repW` and `min s.fdLimit 2^31 ≥ 4 + s.fds.length`,
`relocate_rep_above2` succeeds with a valid descriptor `fd ≥ 3` carrying `e.desc`. -/
theorem relocate_rep_ok_of_open (s : ChildState) (hRun : s.status = .running) (hOr : s.oracle = [])
    (repW : I32) (hRepGe : 0#i32 ≤ repW) {e : FdEntry} (hRepFd : s.getFd repW.val = some e)
    (hLim : min s.fdLimit 2147483648 ≥ 4 + Int.ofNat s.fds.length) :
    OkPost (postfork.fd_ops.relocate_rep_above2 s repW) fun p =>
      p.2.status = .running ∧ p.2.oracle = [] ∧ p.2.fds.length ≤ s.fds.length + 1 ∧
      p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
      p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
      SameChildConfig p.2 s ∧
      ∃ fd f, p.1 = .Ok fd ∧ 2 < fd.val ∧ p.2.getFd fd.val = some f ∧
        f.desc = e.desc ∧ f.cloexec = true ∧ (fd = repW ∨ s.getFd fd.val = none) ∧
        (∀ x : I32, repW ≠ x → s.isOpen x.val = true → p.2.isOpen x.val = true) := by
  refine okPost_mono
    (okPost_and (relocate_rep_above2_safety s hRun repW) (relocate_rep_above2_spec s hRun hOr repW)) ?_
  rintro ⟨r, s'⟩ ⟨⟨hsRun, hcfg, hpg, hcw, hsi, hde, hwl, hlen, hSafetyOk⟩, ⟨hReloc, _⟩⟩
  rw [Int.ofNat_eq_natCast] at hLim
  have hNotNeg : ¬ (repW < 0#i32) := by scalar_tac
  have hOr' : s'.oracle = [] := hcfg.oracle.trans hOr
  have hFd : ∃ fd, r = .Ok fd := by
    dsimp only [RelocateRepPost] at hReloc
    simp only [hNotNeg, ↓reduceIte, hRepFd] at hReloc
    by_cases hle : repW.val ≤ 2
    · simp only [hle, ↓reduceIte] at hReloc
      have hLim3 : ¬ (3 ≥ s.fdLimit) := by omega
      simp only [hLim3, ↓reduceIte] at hReloc
      obtain ⟨dst, hdst⟩ := findLowestFreeFd_some_of_card_lt s 3 (s.fds.map Prod.fst) (by omega)
        (by rw [Int.ofNat_eq_natCast, List.length_map]; omega) (fun x _ hx => isOpen_mem_map_fst s x hx)
      rw [hdst] at hReloc
      exact ⟨_, hReloc.1⟩
    · simp only [hle, ↓reduceIte] at hReloc
      exact ⟨repW, hReloc.1⟩
  rcases hFd with ⟨fd, hOk⟩
  rcases hSafetyOk fd hOk with ⟨hgt2, ⟨e', f, he', hf, hdesc, hclo⟩, hLe2, hGt2, hOther⟩
  have heEq : e' = e := by rw [hRepFd] at he'; cases he'; rfl
  have hFdOrFree : fd = repW ∨ s.getFd fd.val = none := by
    by_cases hle : repW.val ≤ 2
    · exact Or.inr (hLe2 hle).2.2
    · exact Or.inl (hGt2 (by omega))
  refine ⟨hsRun, hOr', hlen, hpg, hcw, hsi, hde, hwl, hcfg, fd, f, hOk, hgt2, hf, heEq ▸ hdesc, hclo, hFdOrFree, ?_⟩
  intro x hneq hOpx
  have hOpen1 : ∀ y : Int, y ≠ repW.val → y ≠ fd.val → s'.getFd y = s.getFd y := hOther
  have hxNeRep : x.val ≠ repW.val := fun h => hneq (by scalar_tac)
  have hxNeFd : x.val ≠ fd.val := by
    intro h
    by_cases hle : repW.val ≤ 2
    · have hfree := (hLe2 hle).2.2
      rw [← h] at hfree
      simp [ChildState.isOpen, hfree] at hOpx
    · have hgt : 2 < repW.val := by omega
      rw [hGt2 hgt] at h
      exact hxNeRep h
  simp only [ChildState.isOpen, hOpen1 x.val hxNeRep hxNeFd]
  exact hOpx

end NotRunningAndExecHelpers

section BwrapAndGuestCommon

private theorem sys_fcntl_getfd_trace_eq_local (s : ChildState) (hRun : s.status = .running)
    (fd : I32) :
    ∃ r s' out,
      sys.fcntl_getfd s fd = Result.ok (r, s') ∧
      s'.status = .running ∧
      SameChildConfig s' s ∧
      s'.fds = s.fds ∧
      s'.descs = s.descs ∧
      s'.pgid = s.pgid ∧
      s'.cwd = s.cwd ∧
      s'.sig = s.sig ∧
      s'.writeLog = s.writeLog ∧
      s'.trace = s.trace ++ [Event.mk (.fcntlGetfd fd) out] := by
  obtain ⟨r, s', hEq, hs', hOr', _, hSpec⟩ := sys_fcntl_getfd_running s hRun fd
  have hs'Fields :
      s'.status = .running ∧ SameChildConfig s' s ∧
      s'.fds = s.fds ∧ s'.descs = s.descs ∧
      s'.pgid = s.pgid ∧ s'.cwd = s.cwd ∧
      s'.sig = s.sig ∧ s'.writeLog = s.writeLog := by
    rw [hs']
    exact ⟨hRun,
      (SameChildConfig.refl s).with_trace s'.trace,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hTrace : ∃ out, s'.trace = s.trace ++ [Event.mk (.fcntlGetfd fd) out] := by
    unfold sys.fcntl_getfd LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_getfd runI32Syscall at hEq
    rw [hRun] at hEq
    cases hGet : s.getFd fd.val with
    | none =>
      simp only [hGet] at hEq
      cases hCur : currentFault s <;> (
        simp only [hCur, Result.ok.injEq, Prod.mk.injEq] at hEq
        obtain ⟨_, rfl⟩ := hEq
        exact ⟨_, rfl⟩)
    | some _ =>
      simp only [hGet] at hEq
      cases hCur : currentFault s with
      | seccomp rawE | fail rawE =>
        simp only [hCur, Result.ok.injEq, Prod.mk.injEq] at hEq
        obtain ⟨_, rfl⟩ := hEq
        exact ⟨.err (sanitizeErrno rawE), rfl⟩
      | normal | partialWrite _ | dentsBatch _ =>
        simp only [hCur, Result.ok.injEq, Prod.mk.injEq] at hEq
        obtain ⟨_, rfl⟩ := hEq
        exact ⟨_, rfl⟩
  rcases hTrace with ⟨out, hTr⟩
  exact ⟨r, s', out, hEq, hs'Fields.1, hs'Fields.2.1, hs'Fields.2.2.1, hs'Fields.2.2.2.1,
    hs'Fields.2.2.2.2.1, hs'Fields.2.2.2.2.2.1, hs'Fields.2.2.2.2.2.2.1, hs'Fields.2.2.2.2.2.2.2, hTr⟩

private theorem runUnitSyscall_trace_eq (s : ChildState) (req : Req)
    (forcedErr? : Option I32) (onSuccess : ChildState → ChildState)
    (hOnTr : (onSuccess s).trace = s.trace) (hRun : s.status = .running)
    {r : core.result.Result Unit I32} {s' : ChildState}
    (hEq : runUnitSyscall s req forcedErr? onSuccess = Result.ok (r, s')) :
    ∃ out, s'.trace = s.trace ++ [Event.mk req out] := by
  unfold runUnitSyscall at hEq
  rw [hRun] at hEq
  cases hCur : currentFault s with
  | seccomp rawE =>
    simp only [hCur, Result.ok.injEq, Prod.mk.injEq] at hEq
    obtain ⟨_, rfl⟩ := hEq
    exact ⟨.err (sanitizeErrno rawE), rfl⟩
  | fail rawE =>
    simp only [hCur] at hEq
    cases hFe : forcedErr? with
    | some err =>
      simp only [hFe, Result.ok.injEq, Prod.mk.injEq] at hEq
      obtain ⟨_, rfl⟩ := hEq
      exact ⟨.err err, rfl⟩
    | none =>
      simp only [hFe, Result.ok.injEq, Prod.mk.injEq] at hEq
      obtain ⟨_, rfl⟩ := hEq
      exact ⟨.err (sanitizeErrno rawE), rfl⟩
  | normal | partialWrite _ | dentsBatch _ =>
    simp only [hCur] at hEq
    cases hFe : forcedErr? with
    | some err =>
      simp only [hFe, Result.ok.injEq, Prod.mk.injEq] at hEq
      obtain ⟨_, rfl⟩ := hEq
      exact ⟨.err err, rfl⟩
    | none =>
      simp only [hFe, Result.ok.injEq, Prod.mk.injEq] at hEq
      obtain ⟨_, rfl⟩ := hEq
      exact ⟨.okVal 0, by simp [hOnTr]⟩

/-- `sys.setpgid_self` running step appends a single `.setpgidSelf` event. -/
theorem sys_setpgid_self_trace_eq (s : ChildState) (hRun : s.status = .running)
    {r : core.result.Result Unit I32} {s' : ChildState}
    (hEq : sys.setpgid_self s = Result.ok (r, s')) :
    ∃ out, s'.trace = s.trace ++ [Event.mk .setpgidSelf out] := by
  unfold sys.setpgid_self LeanSwe.PostFork.Aeneas.Internal.Sys.setpgid_self at hEq
  exact runUnitSyscall_trace_eq s .setpgidSelf _ _ rfl hRun hEq

/-- `sys.sig_dfl` running step appends a single `.sigDfl` event for valid userspace signal numbers. -/
theorem sys_sig_dfl_trace_eq (s : ChildState) (hRun : s.status = .running) (sig : I32)
    {r : core.result.Result Unit I32} {s' : ChildState}
    (hEq : sys.sig_dfl s sig = Result.ok (r, s'))
    (hValid : isUserspaceInvalidSigactionSig sig = false := by
      simp [isUserspaceInvalidSigactionSig, postfork.child.SIGPIPE]) :
    ∃ out, s'.trace = s.trace ++ [Event.mk (.sigDfl sig) out] := by
  unfold sys.sig_dfl LeanSwe.PostFork.Aeneas.Internal.Sys.sig_dfl at hEq
  simp only [hRun, beq_self_eq_true, hValid, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hEq
  exact runUnitSyscall_trace_eq s (.sigDfl sig) _ _ rfl hRun hEq

/-- `sys.sig_unblock` running step appends a single `.sigUnblock` event for valid signal numbers `1..64`. -/
theorem sys_sig_unblock_trace_eq (s : ChildState) (hRun : s.status = .running) (sig : I32)
    {r : core.result.Result Unit I32} {s' : ChildState}
    (hEq : sys.sig_unblock s sig = Result.ok (r, s'))
    (hValid : (sig.val < 1 || sig.val > 64) = false := by
      simp [postfork.child.SIGPIPE]) :
    ∃ out, s'.trace = s.trace ++ [Event.mk (.sigUnblock sig) out] := by
  unfold sys.sig_unblock LeanSwe.PostFork.Aeneas.Internal.Sys.sig_unblock at hEq
  simp only [hRun, beq_self_eq_true, hValid, Bool.true_and, Bool.false_eq_true, ↓reduceIte] at hEq
  exact runUnitSyscall_trace_eq s (.sigUnblock sig) _ _ rfl hRun hEq

/-- `sys.fcntl_getfd` running step appends a single `.fcntlGetfd` event. -/
theorem sys_fcntl_getfd_trace_eq (s : ChildState) (hRun : s.status = .running) (fd : I32)
    {r : core.result.Result I32 I32} {s' : ChildState}
    (hEq : sys.fcntl_getfd s fd = Result.ok (r, s')) :
    ∃ out, s'.trace = s.trace ++ [Event.mk (.fcntlGetfd fd) out] := by
  obtain ⟨r0, s0, out, h0, _, _, _, _, _, _, _, _, hTr⟩ :=
    sys_fcntl_getfd_trace_eq_local s hRun fd
  rw [h0, Result.ok.injEq, Prod.mk.injEq] at hEq
  rw [← hEq.2]
  exact ⟨out, hTr⟩

/-- `sys.execve` appends an `.execve` trace event when running and otherwise leaves `s` unchanged. -/
theorem sys_execve_trace_eq (s : ChildState) (path : sys.CStr) (argv envp : sys.CStrArray)
    {e : I32} {s' : ChildState}
    (hEq : sys.execve s path argv envp = Result.ok (e, s')) :
    ∃ suf, s'.trace = s.trace ++ suf := by
  unfold sys.execve LeanSwe.PostFork.Aeneas.Internal.Sys.execve at hEq
  cases hSt : s.status with
  | running =>
    rw [hSt] at hEq
    cases hCur : currentFault s with
    | seccomp rawE =>
      simp only [hCur, Result.ok.injEq, Prod.mk.injEq] at hEq
      obtain ⟨_, rfl⟩ := hEq
      exact ⟨_, rfl⟩
    | fail rawE =>
      simp only [hCur] at hEq
      by_cases hEmpty : path.isEmpty
      · simp only [hEmpty, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at hEq
        obtain ⟨_, rfl⟩ := hEq
        exact ⟨_, rfl⟩
      · simp only [hEmpty, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at hEq
        obtain ⟨_, rfl⟩ := hEq
        exact ⟨_, rfl⟩
    | normal | partialWrite _ | dentsBatch _ =>
      simp only [hCur] at hEq
      by_cases hEmpty : path.isEmpty
      · simp only [hEmpty, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at hEq
        obtain ⟨_, rfl⟩ := hEq
        exact ⟨_, rfl⟩
      · simp only [hEmpty, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at hEq
        obtain ⟨_, rfl⟩ := hEq
        exact ⟨_, rfl⟩
  | exited _ | signaled _ | execd _ =>
    rw [hSt] at hEq
    simp only [Result.ok.injEq, Prod.mk.injEq] at hEq
    obtain ⟨_, rfl⟩ := hEq
    exact ⟨[], by simp⟩

/-- `probe_stdio_open` only emits `.fcntlGetfd` trace events (never `.read1`). -/
theorem probe_stdio_open_noRead (s : ChildState) (hRun : s.status = .running)
    (syncR inFd outFd errFd : I32) :
    OkPost (postfork.fd_ops.probe_stdio_open s inFd outFd errFd) fun p =>
      ∃ suf, p.2.trace = s.trace ++ suf ∧ ∀ ev ∈ suf, ev.req ≠ .read1 syncR := by
  unfold postfork.fd_ops.probe_stdio_open
  split_ifs
  · exact okPost_ok _ _ ⟨[], by simp, fun _ h => by cases h⟩
  · exact okPost_ok _ _ ⟨[], by simp, fun _ h => by cases h⟩
  · exact okPost_ok _ _ ⟨[], by simp, fun _ h => by cases h⟩
  · obtain ⟨r1, s1, out1, h1, hRun1, _, _, _, _, _, _, _, hTr1⟩ :=
      sys_fcntl_getfd_trace_eq_local s hRun inFd
    rw [h1, bind_ok]
    cases r1 with
    | Err e1 =>
      exact okPost_ok _ _ ⟨[Event.mk (.fcntlGetfd inFd) out1], hTr1, by
        intro ev hev hEq
        rcases List.mem_singleton.mp hev with rfl
        cases hEq⟩
    | Ok _ =>
      obtain ⟨r2, s2, out2, h2, hRun2, _, _, _, _, _, _, _, hTr2⟩ :=
        sys_fcntl_getfd_trace_eq_local s1 hRun1 outFd
      change OkPost (do
        let (r1', s2') ← sys.fcntl_getfd s1 outFd
        match r1' with
        | core.result.Result.Ok _ => do
          let (r2', s3) ← sys.fcntl_getfd s2' errFd
          match r2' with
          | core.result.Result.Ok _ => Result.ok (core.result.Result.Ok (), s3)
          | core.result.Result.Err e => Result.ok (core.result.Result.Err e, s3)
        | core.result.Result.Err e => Result.ok (core.result.Result.Err e, s2')) _
      rw [h2, bind_ok]
      cases r2 with
      | Err e2 =>
        exact okPost_ok _ _ ⟨[Event.mk (.fcntlGetfd inFd) out1, Event.mk (.fcntlGetfd outFd) out2],
          by rw [hTr2, hTr1, List.append_assoc]; rfl, by
          intro ev hev hEq
          rcases List.mem_cons.mp hev with rfl | hev2
          · cases hEq
          · rcases List.mem_singleton.mp hev2 with rfl
            cases hEq⟩
      | Ok _ =>
        obtain ⟨r3, s3, out3, h3, _, _, _, _, _, _, _, _, hTr3⟩ :=
          sys_fcntl_getfd_trace_eq_local s2 hRun2 errFd
        change OkPost (do
          let (r2', s3') ← sys.fcntl_getfd s2 errFd
          match r2' with
          | core.result.Result.Ok _ => Result.ok (core.result.Result.Ok (), s3')
          | core.result.Result.Err e => Result.ok (core.result.Result.Err e, s3')) _
        rw [h3, bind_ok]
        have hTrAll : s3.trace = s.trace ++
            [Event.mk (.fcntlGetfd inFd) out1, Event.mk (.fcntlGetfd outFd) out2,
              Event.mk (.fcntlGetfd errFd) out3] := by
          rw [hTr3, hTr2, hTr1, List.append_assoc, List.append_assoc]; rfl
        have hNoRead : ∀ ev ∈ [Event.mk (.fcntlGetfd inFd) out1, Event.mk (.fcntlGetfd outFd) out2,
            Event.mk (.fcntlGetfd errFd) out3], ev.req ≠ .read1 syncR := by
          intro ev hev hEq
          rcases List.mem_cons.mp hev with rfl | hev2
          · cases hEq
          · rcases List.mem_cons.mp hev2 with rfl | hev3
            · cases hEq
            · rcases List.mem_singleton.mp hev3 with rfl
              cases hEq
        cases r3 with
        | Ok _ => exact okPost_ok _ _ ⟨_, hTrAll, hNoRead⟩
        | Err _ => exact okPost_ok _ _ ⟨_, hTrAll, hNoRead⟩

/-- `probe_open_slice` only emits `.fcntlGetfd` trace events (never `.read1`). -/
theorem probe_open_slice_noRead (s : ChildState) (hRun : s.status = .running)
    (syncR : I32) (fds : Slice I32) :
    OkPost (postfork.fd_ops.probe_open_slice s fds) fun p =>
      ∃ suf, p.2.trace = s.trace ++ suf ∧ ∀ ev ∈ suf, ev.req ≠ .read1 syncR := by
  unfold postfork.fd_ops.probe_open_slice postfork.fd_ops.probe_open_slice_loop
  let inv : ChildState × Usize → Prop := fun p =>
    p.2.val ≤ fds.val.length ∧ p.1.status = .running ∧
    ∃ suf, p.1.trace = s.trace ++ suf ∧ ∀ ev ∈ suf, ev.req ≠ .read1 syncR
  let post : ChildState × I32 × Bool → Prop := fun p =>
    ∃ suf, p.1.trace = s.trace ++ suf ∧ ∀ ev ∈ suf, ev.req ≠ .read1 syncR
  have hLoop : OkPost
      (loop (fun (s1, i1) => postfork.fd_ops.probe_open_slice_loop.body fds fds.len s1 i1) (s, 0#usize))
      post := by
    refine okPost_loop_decr_nat (fun p => fds.val.length - p.2.val) inv post _ (s, 0#usize) ?_
      ⟨Nat.zero_le _, hRun, [], by simp, fun _ h => by cases h⟩
    intro ⟨sCur, idx⟩ ⟨hIdxLe, hRunCur, suf1, hTr1, hNo1⟩
    unfold postfork.fd_ops.probe_open_slice_loop.body
    by_cases hlt : idx < fds.len
    · simp only [hlt, ↓reduceIte]
      rcases slice_idx_succ_local fds hlt with ⟨hjlt, hIdx, idx1, hInc, hIdx1Val⟩
      rw [hIdx, bind_ok]
      by_cases hge : 0#i32 ≤ fds.val[idx.val]
      · simp only [hge, ↓reduceIte]
        obtain ⟨r1, s1, out1, hGet1, hRun1, _, _, _, _, _, _, _, hTrStep⟩ :=
          sys_fcntl_getfd_trace_eq_local sCur hRunCur fds.val[idx.val]
        rw [hGet1, bind_ok]
        have hSufStep : ∃ suf', s1.trace = s.trace ++ suf' ∧ ∀ ev ∈ suf', ev.req ≠ .read1 syncR := by
          refine ⟨suf1 ++ [Event.mk (.fcntlGetfd fds.val[idx.val]) out1],
            by rw [hTrStep, hTr1, List.append_assoc], fun ev hev hEq => ?_⟩
          rcases List.mem_append.mp hev with he1 | he2
          · exact hNo1 ev he1 hEq
          · rcases List.mem_singleton.mp he2 with rfl
            cases hEq
        cases r1 with
        | Err e =>
          exact okPost_ok _ _ hSufStep
        | Ok _ =>
          change OkPost (do let i1 ← idx + 1#usize; Result.ok (ControlFlow.cont (s1, i1))) _
          rw [hInc, bind_ok]
          refine okPost_ok _ _ ⟨⟨by change idx1.val ≤ fds.val.length; rw [hIdx1Val]; exact hjlt,
            hRun1, hSufStep⟩, ?_⟩
          change fds.val.length - idx1.val < fds.val.length - idx.val
          rw [hIdx1Val]; exact Nat.sub_succ_lt_self fds.val.length idx.val hjlt
      · simp only [hge, ↓reduceIte]
        rw [hInc, bind_ok]
        refine okPost_ok _ _ ⟨⟨by change idx1.val ≤ fds.val.length; rw [hIdx1Val]; exact hjlt,
          hRunCur, suf1, hTr1, hNo1⟩, ?_⟩
        change fds.val.length - idx1.val < fds.val.length - idx.val
        rw [hIdx1Val]; exact Nat.sub_succ_lt_self fds.val.length idx.val hjlt
    · simp only [hlt, ↓reduceIte]
      exact okPost_ok _ _ ⟨suf1, hTr1, hNo1⟩
  refine okPost_bind hLoop fun ⟨s1, err, failed⟩ hp => ?_
  by_cases hf : failed = true
  · simp [hf]; exact okPost_ok _ _ hp
  · simp [hf]; exact okPost_ok _ _ hp

private theorem clear_cloexec_slice_ok_only (s : ChildState) (hRun : s.status = .running)
    (hOr : s.oracle = []) (fds : Slice I32)
    (hOpen : ∀ fd ∈ fds.val, 0#i32 ≤ fd → s.isOpen fd.val = true) :
    OkPost (postfork.fd_ops.clear_cloexec_slice s fds) fun p =>
      p.1 = .Ok () ∧ p.2.oracle = [] := by
  unfold postfork.fd_ops.clear_cloexec_slice postfork.fd_ops.clear_cloexec_slice_loop
  let inv : ChildState × Usize → Prop := fun p =>
    p.2.val ≤ fds.val.length ∧ p.1.status = .running ∧ p.1.oracle = [] ∧
    ∀ x ∈ fds.val, 0#i32 ≤ x → p.1.isOpen x.val = true
  let post : ChildState × I32 × Bool → Prop := fun p => p.2.2 = false ∧ p.1.oracle = []
  have hLoop : OkPost
      (loop (fun (s1, i1) => postfork.fd_ops.clear_cloexec_slice_loop.body fds fds.len s1 i1) (s, 0#usize))
      post := by
    refine okPost_loop_decr_nat (fun p => fds.val.length - p.2.val) inv post _ (s, 0#usize) ?_
      ⟨Nat.zero_le _, hRun, hOr, hOpen⟩
    intro ⟨sCur, idx⟩ ⟨hIdxLe, hRunCur, hOrCur, hOpCur⟩
    unfold postfork.fd_ops.clear_cloexec_slice_loop.body
    by_cases hlt : idx < fds.len
    · simp only [hlt, ↓reduceIte]
      rcases slice_idx_succ_local fds hlt with ⟨hjlt, hIdx, idx1, hInc, hIdx1Val⟩
      rw [hIdx, bind_ok]
      by_cases hge : 0#i32 ≤ fds.val[idx.val]
      · simp only [hge, ↓reduceIte]
        refine okPost_bind (clear_cloexec_spec sCur hRunCur hOrCur fds.val[idx.val]) fun ⟨r1, s1⟩ hs1 => ?_
        rcases hs1 with ⟨hClo, hcfg1, _, _, _, _, _⟩
        have hOpCurFd : sCur.isOpen fds.val[idx.val].val = true :=
          hOpCur fds.val[idx.val] (List.getElem_mem hjlt) hge
        have ⟨e, heGet⟩ : ∃ e, sCur.getFd fds.val[idx.val].val = some e := by
          cases h : sCur.getFd fds.val[idx.val].val with
          | none => simp [ChildState.isOpen, h] at hOpCurFd
          | some e => exact ⟨e, rfl⟩
        dsimp only [CloexecTogglePost] at hClo
        rw [heGet] at hClo
        rcases hClo with ⟨hr1, hs1Get, hs1Ne⟩
        rw [hr1]
        change OkPost (do let i1 ← idx + 1#usize; Result.ok (ControlFlow.cont (s1, i1))) _
        rw [hInc, bind_ok]
        have hOp1 : ∀ x ∈ fds.val, 0#i32 ≤ x → s1.isOpen x.val = true := by
          intro x hx hx0
          by_cases hxe : x.val = fds.val[idx.val].val
          · simp [ChildState.isOpen, hxe, hs1Get]
          · simpa [ChildState.isOpen, hs1Ne x.val hxe] using hOpCur x hx hx0
        refine okPost_ok _ _ ⟨⟨by change idx1.val ≤ fds.val.length; rw [hIdx1Val]; exact hjlt,
          hcfg1.status.trans hRunCur, hcfg1.oracle.trans hOrCur, hOp1⟩, ?_⟩
        change fds.val.length - idx1.val < fds.val.length - idx.val
        rw [hIdx1Val]; exact Nat.sub_succ_lt_self fds.val.length idx.val hjlt
      · simp only [hge, ↓reduceIte]
        rw [hInc, bind_ok]
        refine okPost_ok _ _ ⟨⟨by change idx1.val ≤ fds.val.length; rw [hIdx1Val]; exact hjlt,
          hRunCur, hOrCur, hOpCur⟩, ?_⟩
        change fds.val.length - idx1.val < fds.val.length - idx.val
        rw [hIdx1Val]; exact Nat.sub_succ_lt_self fds.val.length idx.val hjlt
    · simp only [hlt, ↓reduceIte]
      exact okPost_ok _ _ ⟨rfl, hOrCur⟩
  refine okPost_bind hLoop fun ⟨s1, err, failed⟩ ⟨hf, hO⟩ => ?_
  dsimp only [post] at hf hO
  rw [hf]
  exact okPost_ok _ _ ⟨rfl, hO⟩

/-- Exact fault-free specification for `clear_cloexec_slice` when all non-negative slots in `fds` are open and `s.oracle = []`. -/
theorem clear_cloexec_slice_ok (s : ChildState) (hRun : s.status = .running)
    (hOr : s.oracle = []) (fds : Slice I32)
    (hOpen : ∀ fd ∈ fds.val, 0#i32 ≤ fd → s.isOpen fd.val = true) :
    OkPost (postfork.fd_ops.clear_cloexec_slice s fds) fun p =>
      p.1 = .Ok () ∧ p.2.status = .running ∧ SameChildConfig p.2 s ∧ p.2.oracle = [] ∧
      p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧ p.2.descs = s.descs ∧
      p.2.writeLog = s.writeLog ∧
      (∀ k : Int, (∀ fd ∈ fds.val, 0#i32 ≤ fd → k ≠ fd.val) → p.2.getFd k = s.getFd k) ∧
      (∀ fd ∈ fds.val, 0#i32 ≤ fd →
        ∃ e f, s.getFd fd.val = some e ∧ p.2.getFd fd.val = some f ∧ f.desc = e.desc ∧ f.cloexec = false) := by
  refine okPost_mono
    (okPost_and (clear_cloexec_slice_safety s hRun fds)
      (clear_cloexec_slice_ok_only s hRun hOr fds hOpen))
    fun p ⟨hsafe, hok, hor⟩ => ?_
  rcases hsafe with ⟨hRun1, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1, hOnOk⟩
  rcases hOnOk hok with ⟨hNe, hClo⟩
  exact ⟨hok, hRun1, hcfg1, hor, hpg1, hcw1, hsi1, hde1, hwl1, hNe, hClo⟩

private theorem okPost_to_dspec_common {α : Type} {m : Result α} {P : α → Prop}
    (h : OkPost m P) : WP.dspec m P := by
  rcases h with ⟨v, hv, hp⟩
  rw [hv, WP.dspec_ok]
  exact hp

private theorem usize_add_ok_common (a b : Usize) (h : a.val + b.val ≤ Usize.max) :
    ∃ c : Usize, a + b = Result.ok c ∧ c.val = a.val + b.val := by
  have hc := Aeneas.Std.Usize.add_spec h
  cases hEq : a + b <;> simp_all

private theorem usize_sub_ok_common (a b : Usize) (h : b.val ≤ a.val) :
    ∃ c : Usize, a - b = Result.ok c ∧ c.val = a.val - b.val := by
  have hc := Aeneas.Std.Usize.sub_spec h
  cases hEq : a - b <;> simp_all

private theorem u32_add_ok_common (a b : U32) (h : a.val + b.val ≤ U32.max) :
    ∃ c : U32, a + b = Result.ok c ∧ c.val = a.val + b.val := by
  have hc := Aeneas.Std.U32.add_spec h
  cases hEq : a + b <;> simp_all

private theorem u32_sub_ok_common (a b : U32) (h : b.val ≤ a.val) :
    ∃ c : U32, a - b = Result.ok c ∧ c.val = a.val - b.val := by
  have hc := Aeneas.Std.U32.sub_spec h
  cases hEq : a - b <;> simp_all

private theorem array_index_usize_ok_common {α : Type} {n : Usize} (a : Array α n) (i : Usize)
    (hi : i.val < a.val.length) : ∃ x, Array.index_usize a i = Result.ok x := by
  refine ⟨a.val[i.val], ?_⟩
  simp [Array.index_usize, List.getElem?_eq_getElem hi]

private theorem hcast_u32_ok_common (x : I32) (hx : 0 ≤ x.val) :
    ∃ u : U32, lift (IScalar.hcast .U32 x) = Result.ok u ∧ u.val = x.val :=
  ⟨IScalar.hcast .U32 x, rfl, by scalar_tac⟩

private theorem next_keep_ge_bound_common (extra_keep_fd : I32) (keep_fds : Slice I32) (lo : U32) :
    OkPost (postfork.fd_ops.next_keep_ge extra_keep_fd keep_fds lo) fun o =>
      ∀ k : U32, o = some k → lo.val ≤ k.val ∧ k.val ≤ 2147483647 := by
  unfold postfork.fd_ops.next_keep_ge postfork.fd_ops.next_keep_ge_loop
  refine okPost_bind (P := fun b => ∀ k : U32, b = some k → lo.val ≤ k.val ∧ k.val ≤ 2147483647) ?_ fun best hBest => ?_
  · split
    · rcases hcast_u32_ok_common extra_keep_fd (by scalar_tac) with ⟨u, hu, huVal⟩
      rw [hu, bind_ok]
      split
      · simp only [bind_ok]
        apply okPost_ok
        intro k hk; cases hk; exact ⟨by scalar_tac, by scalar_tac⟩
      · apply okPost_ok
        intro k hk; cases hk
    · apply okPost_ok
      intro k hk; cases hk
  · refine okPost_loop_decr_nat (fun p => keep_fds.len.val - p.2.val)
      (fun p => p.2.val ≤ keep_fds.len.val ∧ ∀ k : U32, p.1 = some k → lo.val ≤ k.val ∧ k.val ≤ 2147483647)
      (fun o => ∀ k : U32, o = some k → lo.val ≤ k.val ∧ k.val ≤ 2147483647)
      _ (best, 0#usize) ?_ ⟨Nat.zero_le _, hBest⟩
    intro ⟨b, j⟩ ⟨hj, hbBound⟩
    dsimp only at hj hbBound
    unfold postfork.fd_ops.next_keep_ge_loop.body
    by_cases hlt : j < keep_fds.len
    · have hjlt : j.val < keep_fds.val.length := hlt
      have hidx : Slice.index_usize keep_fds j = Result.ok keep_fds.val[j.val] := by
        simp [Slice.index_usize, List.getElem?_eq_getElem hjlt]
      have hinc : ∃ z : Usize, j + 1#usize = Result.ok z ∧ z.val = j.val + 1 := by
        have hlen := keep_fds.property
        exact usize_add_ok_common j 1#usize (by change j.val + 1 ≤ Usize.max; omega)
      rcases hinc with ⟨z, hz, hzVal⟩
      simp only [hlt, ↓reduceIte, hidx, bind_ok]
      refine okPost_bind (P := fun b' => ∀ k : U32, b' = some k → lo.val ≤ k.val ∧ k.val ≤ 2147483647) ?_
        fun b' hb' => ?_
      · split
        · rcases hcast_u32_ok_common keep_fds.val[j.val] (by scalar_tac) with ⟨u, hu, huVal⟩
          rw [hu, bind_ok]
          split
          · cases b with
            | none =>
              dsimp only
              simp only [bind_ok]
              apply okPost_ok
              intro k hk; cases hk; exact ⟨by scalar_tac, by scalar_tac⟩
            | some cur =>
              dsimp only
              split
              · simp only [bind_ok]
                apply okPost_ok
                intro k hk; cases hk; exact ⟨by scalar_tac, by scalar_tac⟩
              · simp only [bind_ok]
                apply okPost_ok
                exact hbBound
          · apply okPost_ok
            exact hbBound
        · apply okPost_ok
          exact hbBound
      · rw [hz, bind_ok]
        exact okPost_ok _ _ ⟨⟨by simp [hzVal]; omega, hb'⟩, by
          change keep_fds.len.val - z.val < keep_fds.len.val - j.val
          rw [hzVal]
          exact Nat.sub_succ_lt_self _ _ hjlt⟩
    · simp only [hlt, ↓reduceIte]
      exact okPost_ok _ _ hbBound

/-- `postfork.fd_ops.probe_stdio_open` preserves `blockedSigs`. -/
theorem probe_stdio_open_dspec_blockedSigs (s : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32) :
    WP.dspec (postfork.fd_ops.probe_stdio_open s stdin_fd stdout_fd stderr_fd) fun p =>
      p.2.blockedSigs = s.blockedSigs := by
  unfold postfork.fd_ops.probe_stdio_open
  split
  · exact (WP.dspec_ok _).mpr rfl
  · split
    · exact (WP.dspec_ok _).mpr rfl
    · split
      · exact (WP.dspec_ok _).mpr rfl
      · refine WP.dspec_bind (sys_fcntl_getfd_dspec_blockedSigs s stdin_fd) fun ⟨r, s1⟩ hs1 => ?_
        cases r with
        | Err _ => exact (WP.dspec_ok _).mpr hs1
        | Ok _ =>
          refine WP.dspec_bind (sys_fcntl_getfd_dspec_blockedSigs s1 stdout_fd) fun ⟨r1, s2⟩ hs2 => ?_
          cases r1 with
          | Err _ => exact (WP.dspec_ok _).mpr (hs2.trans hs1)
          | Ok _ =>
            refine WP.dspec_bind (sys_fcntl_getfd_dspec_blockedSigs s2 stderr_fd) fun ⟨r2, s3⟩ hs3 => ?_
            cases r2 <;> exact (WP.dspec_ok _).mpr (hs3.trans (hs2.trans hs1))

/-- `postfork.fd_ops.set_cloexec` preserves `blockedSigs`. -/
theorem set_cloexec_dspec_blockedSigs (s : sys.Sys) (fd : I32) :
    WP.dspec (postfork.fd_ops.set_cloexec s fd) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold postfork.fd_ops.set_cloexec
  refine WP.dspec_bind (sys_fcntl_getfd_dspec_blockedSigs s fd) fun ⟨r, s1⟩ hs1 => ?_
  cases r with
  | Err _ => exact (WP.dspec_ok _).mpr hs1
  | Ok flags =>
    simp only [lift, bind_ok]
    exact WP.dspec_mono (sys_fcntl_setfd_dspec_blockedSigs s1 fd _) fun p hp => hp.trans hs1

/-- `postfork.fd_ops.relocate_rep_above2` preserves `blockedSigs`. -/
theorem relocate_rep_above2_dspec_blockedSigs (s : sys.Sys) (rep_w : I32) :
    WP.dspec (postfork.fd_ops.relocate_rep_above2 s rep_w) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold postfork.fd_ops.relocate_rep_above2
  split
  · exact (WP.dspec_ok _).mpr rfl
  · split
    · refine WP.dspec_bind (sys_fcntl_dupfd_cloexec_dspec_blockedSigs s rep_w 3#i32) fun ⟨r, s1⟩ hs1 => ?_
      cases r with
      | Err _ => exact (WP.dspec_ok _).mpr hs1
      | Ok _ =>
        exact WP.dspec_bind (sys_close_dspec_blockedSigs s1 rep_w) fun ⟨_, s2⟩ hs2 =>
          (WP.dspec_ok _).mpr (hs2.trans hs1)
    · refine WP.dspec_bind (set_cloexec_dspec_blockedSigs s rep_w) fun ⟨r, s1⟩ hs1 => ?_
      cases r <;> exact (WP.dspec_ok _).mpr hs1

/-- `postfork.fd_ops.close_unused_slice` preserves `blockedSigs`. -/
theorem close_unused_slice_dspec_blockedSigs (s : sys.Sys) (fds : Slice I32) :
    WP.dspec (postfork.fd_ops.close_unused_slice s fds) fun (s' : sys.Sys) => s'.blockedSigs = s.blockedSigs := by
  unfold postfork.fd_ops.close_unused_slice postfork.fd_ops.close_unused_slice_loop
  refine loop_dspec _ (fun p => p.2.val ≤ fds.val.length ∧ p.1.blockedSigs = s.blockedSigs)
    (fun (s' : sys.Sys) => s'.blockedSigs = s.blockedSigs) ?_ (s, 0#usize) ⟨Nat.zero_le _, rfl⟩
  intro ⟨s1, i1⟩ ⟨hiLe, hs1⟩
  unfold postfork.fd_ops.close_unused_slice_loop.body
  by_cases hlt : i1 < fds.len
  · simp only [hlt, ↓reduceIte]
    rcases slice_idx_succ_local fds hlt with ⟨hjlt, hIdx, idx1, hInc, hIdx1Val⟩
    rw [hIdx, bind_ok]
    refine WP.dspec_bind (Pₘ := fun s2 => s2.blockedSigs = s.blockedSigs) ?_ fun s2 hs2 => ?_
    · split
      · exact WP.dspec_bind (sys_close_dspec_blockedSigs s1 fds.val[i1.val]) fun ⟨_, s3⟩ hs3 =>
          (WP.dspec_ok _).mpr (hs3.trans hs1)
      · exact (WP.dspec_ok _).mpr hs1
    · rw [hInc, bind_ok]
      exact (WP.dspec_ok _).mpr ⟨by change idx1.val ≤ fds.val.length; rw [hIdx1Val]; exact hjlt, hs2⟩
  · simp only [hlt, ↓reduceIte]
    exact (WP.dspec_ok _).mpr hs1

/-- `postfork.fd_ops.clear_cloexec_slice` preserves `blockedSigs`. -/
theorem clear_cloexec_slice_dspec_blockedSigs (s : sys.Sys) (fds : Slice I32) :
    WP.dspec (postfork.fd_ops.clear_cloexec_slice s fds) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold postfork.fd_ops.clear_cloexec_slice postfork.fd_ops.clear_cloexec_slice_loop
  refine WP.dspec_bind (loop_dspec _ (fun p => p.2.val ≤ fds.val.length ∧ p.1.blockedSigs = s.blockedSigs)
      (fun res => res.1.blockedSigs = s.blockedSigs) ?_ (s, 0#usize) ⟨Nat.zero_le _, rfl⟩)
    fun ⟨s1, err, failed⟩ h => ?_
  · intro ⟨s1, i1⟩ ⟨hiLe, hs1⟩
    unfold postfork.fd_ops.clear_cloexec_slice_loop.body
    by_cases hlt : i1 < fds.len
    · simp only [hlt, ↓reduceIte]
      rcases slice_idx_succ_local fds hlt with ⟨hjlt, hIdx, idx1, hInc, hIdx1Val⟩
      rw [hIdx, bind_ok]
      by_cases hge : 0#i32 ≤ fds.val[i1.val]
      · simp only [hge, ↓reduceIte]
        have hClear : WP.dspec (postfork.fd_ops.clear_cloexec s1 fds.val[i1.val]) fun p =>
            p.2.blockedSigs = s1.blockedSigs := by
          unfold postfork.fd_ops.clear_cloexec
          refine WP.dspec_bind (sys_fcntl_getfd_dspec_blockedSigs s1 _) fun ⟨r, s2⟩ hs2 => ?_
          cases r with
          | Err _ => exact (WP.dspec_ok _).mpr hs2
          | Ok _ =>
            simp only [lift, bind_ok]
            exact WP.dspec_mono (sys_fcntl_setfd_dspec_blockedSigs s2 _ _) fun p hp => hp.trans hs2
        refine WP.dspec_bind hClear fun ⟨r, s2⟩ hs2 => ?_
        cases r with
        | Err _ => exact (WP.dspec_ok _).mpr (hs2.trans hs1)
        | Ok _ =>
          rw [hInc]
          simp only [bind_ok]
          exact (WP.dspec_ok _).mpr ⟨by change idx1.val ≤ fds.val.length; rw [hIdx1Val]; exact hjlt, hs2.trans hs1⟩
      · simp only [hge, ↓reduceIte]
        rw [hInc, bind_ok]
        exact (WP.dspec_ok _).mpr ⟨by change idx1.val ≤ fds.val.length; rw [hIdx1Val]; exact hjlt, hs1⟩
    · simp only [hlt, ↓reduceIte]
      exact (WP.dspec_ok _).mpr hs1
  · cases failed <;> exact (WP.dspec_ok _).mpr h

/-- `postfork.fd_ops.probe_open_slice` preserves `blockedSigs`. -/
theorem probe_open_slice_dspec_blockedSigs (s : sys.Sys) (fds : Slice I32) :
    WP.dspec (postfork.fd_ops.probe_open_slice s fds) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold postfork.fd_ops.probe_open_slice postfork.fd_ops.probe_open_slice_loop
  refine WP.dspec_bind (loop_dspec _ (fun p => p.2.val ≤ fds.val.length ∧ p.1.blockedSigs = s.blockedSigs)
      (fun res => res.1.blockedSigs = s.blockedSigs) ?_ (s, 0#usize) ⟨Nat.zero_le _, rfl⟩)
    fun ⟨s1, err, failed⟩ h => ?_
  · intro ⟨s1, i1⟩ ⟨hiLe, hs1⟩
    unfold postfork.fd_ops.probe_open_slice_loop.body
    by_cases hlt : i1 < fds.len
    · simp only [hlt, ↓reduceIte]
      rcases slice_idx_succ_local fds hlt with ⟨hjlt, hIdx, idx1, hInc, hIdx1Val⟩
      rw [hIdx, bind_ok]
      by_cases hge : 0#i32 ≤ fds.val[i1.val]
      · simp only [hge, ↓reduceIte]
        refine WP.dspec_bind (sys_fcntl_getfd_dspec_blockedSigs s1 fds.val[i1.val]) fun ⟨r, s2⟩ hs2 => ?_
        cases r with
        | Err _ => exact (WP.dspec_ok _).mpr (hs2.trans hs1)
        | Ok _ =>
          rw [hInc]
          simp only [bind_ok]
          exact (WP.dspec_ok _).mpr ⟨by change idx1.val ≤ fds.val.length; rw [hIdx1Val]; exact hjlt, hs2.trans hs1⟩
      · simp only [hge, ↓reduceIte]
        rw [hInc, bind_ok]
        exact (WP.dspec_ok _).mpr ⟨by change idx1.val ≤ fds.val.length; rw [hIdx1Val]; exact hjlt, hs1⟩
    · simp only [hlt, ↓reduceIte]
      exact (WP.dspec_ok _).mpr hs1
  · cases failed <;> exact (WP.dspec_ok _).mpr h

/-- `postfork.child.read_sync_byte` preserves `blockedSigs`. -/
theorem read_sync_byte_dspec_blockedSigs (s : sys.Sys) (sync_r : I32) :
    WP.dspec (postfork.child.read_sync_byte s sync_r) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold postfork.child.read_sync_byte
  split
  · exact (WP.dspec_ok _).mpr rfl
  · unfold postfork.child.read_sync_byte_loop
    refine WP.dspec_bind (loop_dspec _ (fun s1 => s1.blockedSigs = s.blockedSigs)
        (fun p => p.1.blockedSigs = s.blockedSigs) ?_ s rfl)
      fun ⟨s1, got⟩ hs1 => ?_
    · intro s1 hs1
      unfold postfork.child.read_sync_byte_loop.body
      refine WP.dspec_bind (sys_read1_dspec_blockedSigs s1 sync_r (Array.repeat 1#usize 0#u8))
        fun ⟨r, s2, _⟩ hs2 => ?_
      cases r with
      | Ok i =>
        change WP.dspec (match i.val with
          | 1 => Result.ok (ControlFlow.done (s2, true))
          | _ => Result.ok (ControlFlow.done (s2, false))) _
        cases hni : i.val with
        | zero => exact (WP.dspec_ok _).mpr (hs2.trans hs1)
        | succ k => cases k <;> exact (WP.dspec_ok _).mpr (hs2.trans hs1)
      | Err e =>
        change WP.dspec (if (e != postfork.fd_ops.EINTR) = true then Result.ok (ControlFlow.done (s2, false))
          else Result.ok (ControlFlow.cont s2)) _
        by_cases hne : (e != postfork.fd_ops.EINTR) = true
        · simp only [hne, ↓reduceIte]; exact (WP.dspec_ok _).mpr (hs2.trans hs1)
        · simp only [hne, Bool.false_eq_true, ↓reduceIte]; exact (WP.dspec_ok _).mpr (hs2.trans hs1)
    · exact WP.dspec_bind (sys_close_dspec_blockedSigs s1 sync_r) fun ⟨_, s2⟩ hs2 =>
        (WP.dspec_ok _).mpr (hs2.trans hs1)

private theorem close_dirent_batch_dspec_blockedSigs (s : sys.Sys) (buf : Array U8 256#usize)
    (n : Usize) (dirfd extra_keep_fd : I32) (keep_fds : Slice I32) :
    WP.dspec (postfork.fd_ops.close_dirent_batch s buf n dirfd extra_keep_fd keep_fds)
      fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold postfork.fd_ops.close_dirent_batch
  by_cases hn : n > 256#usize
  · simp only [hn, ↓reduceIte]
    exact (WP.dspec_ok _).mpr rfl
  · have hnLe : n.val ≤ 256 := by scalar_tac
    simp only [hn, ↓reduceIte]
    unfold postfork.fd_ops.close_dirent_batch_loop
    refine WP.dspec_bind (loop_dspec _ (fun p => p.2.val ≤ 256 ∧ p.1.blockedSigs = s.blockedSigs)
        (fun res => res.1.blockedSigs = s.blockedSigs) ?_ (s, 0#usize) ⟨by simp, rfl⟩)
      fun ⟨s1, _, bad⟩ h => ?_
    · intro ⟨s1, pos⟩ ⟨hPosLe, hs1⟩
      unfold postfork.fd_ops.close_dirent_batch_loop.body
      by_cases hlt : pos < n
      · have hposLtN : pos.val < n.val := hlt
        rcases usize_sub_ok_common n pos (by omega) with ⟨diff, hdiff, hdiffVal⟩
        simp only [hlt, ↓reduceIte, hdiff, bind_ok]
        by_cases hdiffLt : diff < 20#usize
        · simp only [hdiffLt, ↓reduceIte]
          exact (WP.dspec_ok _).mpr hs1
        · simp only [hdiffLt, ↓reduceIte]
          by_cases hPosGt : pos > 236#usize
          · simp only [hPosGt, ↓reduceIte]
            exact (WP.dspec_ok _).mpr hs1
          · simp only [hPosGt, ↓reduceIte]
            have hPos236 : pos.val ≤ 236 := by scalar_tac
            have hmax : 4294967295 ≤ Usize.max := by
              have h1 := Usize.cMax_bound.1
              have h2 : UScalar.cMax UScalarTy.Usize = 4294967295 := by decide
              omega
            have hblen : buf.val.length = 256 := buf.property
            rcases usize_add_ok_common pos 16#usize (by change pos.val + 16 ≤ Usize.max; omega) with ⟨u1, hu1, hu1Val⟩
            rcases array_index_usize_ok_common buf u1 (by rw [hu1Val, hblen]; scalar_tac) with ⟨loByte, hloByte⟩
            rcases usize_add_ok_common pos 17#usize (by change pos.val + 17 ≤ Usize.max; omega) with ⟨u3, hu3, hu3Val⟩
            rcases array_index_usize_ok_common buf u3 (by rw [hu3Val, hblen]; scalar_tac) with ⟨hiByte, hhiByte⟩
            have hloCast : ∃ loU : Usize, lift (UScalar.cast .Usize loByte) = Result.ok loU :=
              ⟨UScalar.cast .Usize loByte, rfl⟩
            have hhiCast : ∃ hiU : Usize, lift (UScalar.cast .Usize hiByte) = Result.ok hiU :=
              ⟨UScalar.cast .Usize hiByte, rfl⟩
            rcases hloCast with ⟨loU, hloU⟩
            rcases hhiCast with ⟨hiU, hhiU⟩
            have hshl : ∃ sh : Usize, hiU <<< 8#i32 = Result.ok sh := by
              change ∃ sh, UScalar.shiftLeft_IScalar hiU 8#i32 = Result.ok sh
              unfold UScalar.shiftLeft_IScalar
              have hge : (8#i32 : I32).val ≥ 0 := by decide
              have hbits : 32 ≤ System.Platform.numBits := by
                cases System.Platform.numBits_eq with | inl h => simp [h] | inr h => simp [h]
              have hltb : (8#i32 : I32).toNat < UScalarTy.Usize.numBits := by
                have : (8#i32 : I32).toNat = 8 := by decide
                change (8#i32 : I32).toNat < System.Platform.numBits; omega
              simp only [hge, ↓reduceIte, UScalar.shiftLeft, hltb]
              exact ⟨_, rfl⟩
            rcases hshl with ⟨sh, hsh⟩
            rw [hu1, bind_ok, hloByte, bind_ok, hloU, bind_ok, hu3, bind_ok, hhiByte, bind_ok,
              hhiU, bind_ok, hsh, bind_ok]
            refine WP.dspec_bind (okPost_to_dspec_common (okPost_lift _ _ rfl)) fun reclen _ => ?_
            by_cases hrLt : reclen < 20#usize
            · simp only [hrLt, ↓reduceIte]
              exact (WP.dspec_ok _).mpr hs1
            · simp only [hrLt, ↓reduceIte]
              by_cases hrGt : reclen > diff
              · simp only [hrGt, ↓reduceIte]
                exact (WP.dspec_ok _).mpr hs1
              · simp only [hrGt, ↓reduceIte]
                have hrLe : reclen.val ≤ diff.val := by scalar_tac
                rcases usize_add_ok_common pos 19#usize (by change pos.val + 19 ≤ Usize.max; omega) with ⟨u6, hu6, hu6Val⟩
                rcases usize_add_ok_common pos reclen (by omega) with ⟨u7, hu7, hu7Val⟩
                rw [hu6, bind_ok, hu7, bind_ok, parse_dirent_name_eq_expected buf u6 u7, bind_ok]
                set parsed := expectedDirentParse buf u6 u7
                by_cases hpMal : parsed = postfork.fd_ops.DIRENT_MALFORMED
                · simp only [hpMal, ↓reduceIte]
                  exact (WP.dspec_ok _).mpr hs1
                · simp only [hpMal, ↓reduceIte]
                  have hu7Le : u7.val ≤ 256 := by rw [hu7Val]; omega
                  by_cases h1 : parsed > 2#i32
                  · simp only [h1, ↓reduceIte]
                    by_cases h2 : (parsed != dirfd) = true
                    · simp only [h2, ↓reduceIte]
                      by_cases h3 : (parsed != extra_keep_fd) = true
                      · simp only [h3, ↓reduceIte]
                        refine WP.dspec_bind (okPost_to_dspec_common (slice_contains_nonneg_total keep_fds parsed))
                          fun b _ => ?_
                        cases b with
                        | true => exact (WP.dspec_ok _).mpr ⟨hu7Le, hs1⟩
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          refine WP.dspec_bind (sys_close_dspec_blockedSigs s1 parsed) fun ⟨r, s2⟩ hs2 => ?_
                          cases r with
                          | Ok _ => exact (WP.dspec_ok _).mpr ⟨hu7Le, hs2.trans hs1⟩
                          | Err _ => exact (WP.dspec_ok _).mpr (hs2.trans hs1)
                      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
                        exact (WP.dspec_ok _).mpr ⟨hu7Le, hs1⟩
                    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
                      exact (WP.dspec_ok _).mpr ⟨hu7Le, hs1⟩
                  · simp only [h1, ↓reduceIte]
                    exact (WP.dspec_ok _).mpr ⟨hu7Le, hs1⟩
      · simp only [hlt, ↓reduceIte]
        exact (WP.dspec_ok _).mpr hs1
    · cases bad <;> exact (WP.dspec_ok _).mpr h

private theorem close_via_proc_self_fd_dspec_blockedSigs (s : sys.Sys) (extra_keep_fd : I32)
    (keep_fds : Slice I32) :
    WP.dspec (postfork.fd_ops.close_via_proc_self_fd s extra_keep_fd keep_fds) fun p =>
      p.2.blockedSigs = s.blockedSigs := by
  unfold postfork.fd_ops.close_via_proc_self_fd
  refine WP.dspec_bind (sys_open_proc_self_fd_dspec_blockedSigs s) fun ⟨r1, s1⟩ hs1 => ?_
  dsimp only at hs1 ⊢
  cases r1 with
  | Err _ => exact (WP.dspec_ok _).mpr hs1
  | Ok dirfd =>
    unfold postfork.fd_ops.close_via_proc_self_fd_loop
    refine WP.dspec_bind (loop_dspec _ (fun p => p.blockedSigs = s.blockedSigs)
        (fun res => res.1.blockedSigs = s.blockedSigs) ?_ s1 hs1)
      fun ⟨s2, err, failed⟩ hs2 => ?_
    · intro sCur hsCur
      unfold postfork.fd_ops.close_via_proc_self_fd_loop.body
      refine WP.dspec_bind (sys_getdents64_dspec_blockedSigs sCur dirfd (Array.repeat 256#usize 0#u8))
        fun ⟨rGd, sGd, bufGd⟩ hsGd => ?_
      dsimp only at hsGd ⊢
      cases rGd with
      | Err e =>
        change WP.dspec (if (e != postfork.fd_ops.EINTR) = true then Result.ok (ControlFlow.done (sGd, e, true))
          else Result.ok (ControlFlow.cont sGd)) _
        by_cases hne : (e != postfork.fd_ops.EINTR) = true
        · simp only [hne, ↓reduceIte]; exact (WP.dspec_ok _).mpr (hsGd.trans hsCur)
        · simp only [hne, Bool.false_eq_true, ↓reduceIte]; exact (WP.dspec_ok _).mpr (hsGd.trans hsCur)
      | Ok n =>
        change WP.dspec (match n.val with
          | 0 => Result.ok (ControlFlow.done (sGd, 0#i32, false))
          | _ => do
            let (r1, s2) ← postfork.fd_ops.close_dirent_batch sGd bufGd n dirfd extra_keep_fd keep_fds
            match r1 with
            | core.result.Result.Ok _ => Result.ok (ControlFlow.cont s2)
            | core.result.Result.Err e => Result.ok (ControlFlow.done (s2, e, true))) _
        cases hn : n.val with
        | zero => exact (WP.dspec_ok _).mpr (hsGd.trans hsCur)
        | succ k =>
          refine WP.dspec_bind (close_dirent_batch_dspec_blockedSigs sGd bufGd n dirfd extra_keep_fd keep_fds)
            fun ⟨rBat, sBat⟩ hsBat => ?_
          cases rBat <;> exact (WP.dspec_ok _).mpr (hsBat.trans (hsGd.trans hsCur))
    · refine WP.dspec_bind (sys_close_dspec_blockedSigs s2 dirfd) fun ⟨rCl, s3⟩ hs3 => ?_
      dsimp only at hs3 ⊢
      have hs3Eq : s3.blockedSigs = s.blockedSigs := hs3.trans hs2
      cases rCl with
      | Ok _ =>
        change WP.dspec (do
          let (s4, err1, failed1) ← Result.ok (s3, err, failed)
          if failed1 = true then Result.ok (core.result.Result.Err err1, s4)
          else Result.ok (core.result.Result.Ok (), s4)) _
        rw [bind_ok]
        cases failed <;> exact (WP.dspec_ok _).mpr hs3Eq
      | Err ce =>
        change WP.dspec (do
          let (s4, err1, failed1) ← (do
            let (i, b) ← if failed = true then Result.ok (err, failed) else Result.ok (ce, true)
            Result.ok (s3, i, b))
          if failed1 = true then Result.ok (core.result.Result.Err err1, s4)
          else Result.ok (core.result.Result.Ok (), s4)) _
        cases failed <;> simp only [↓reduceIte, Bool.false_eq_true, bind_ok] <;>
          (erw [bind_ok]; exact (WP.dspec_ok _).mpr hs3Eq)

private theorem try_close_range_except_dspec_blockedSigs (s : sys.Sys) (extra_keep_fd : I32)
    (keep_fds : Slice I32) :
    WP.dspec (postfork.fd_ops.try_close_range_except s extra_keep_fd keep_fds) fun p =>
      p.2.blockedSigs = s.blockedSigs := by
  unfold postfork.fd_ops.try_close_range_except postfork.fd_ops.try_close_range_except_loop
  refine WP.dspec_bind (loop_dspec _ (fun p => p.2.blockedSigs = s.blockedSigs)
      (fun res => res.1.blockedSigs = s.blockedSigs) ?_ (3#u32, s) rfl)
    fun ⟨s1, err, failed⟩ hs1 => ?_
  · intro ⟨lo, s1⟩ hs1
    unfold postfork.fd_ops.try_close_range_except_loop.body
    refine WP.dspec_bind (okPost_to_dspec_common (next_keep_ge_bound_common extra_keep_fd keep_fds lo))
      fun o hoBound => ?_
    cases o with
    | none =>
      refine WP.dspec_bind (sys_close_range_dspec_blockedSigs s1 lo core.num.U32.MAX 0#u32)
        fun ⟨r, s2⟩ hs2 => ?_
      cases r <;> exact (WP.dspec_ok _).mpr (hs2.trans hs1)
    | some k =>
      rcases hoBound k rfl with ⟨hLoLe, hkMax⟩
      have hU32Max : 2147483648 ≤ U32.max := by scalar_tac
      rcases u32_add_ok_common k 1#u32 (by change k.val + 1 ≤ U32.max; omega) with ⟨lo1, hlo1, _⟩
      by_cases hkGt : k > lo
      · simp only [hkGt, ↓reduceIte]
        have hkPos : 1 ≤ k.val := by scalar_tac
        rcases u32_sub_ok_common k 1#u32 (by change 1 ≤ k.val; omega) with ⟨i, hi, _⟩
        rw [hi, bind_ok]
        refine WP.dspec_bind (sys_close_range_dspec_blockedSigs s1 lo i 0#u32) fun ⟨r, s2⟩ hs2 => ?_
        cases r with
        | Err _ => exact (WP.dspec_ok _).mpr (hs2.trans hs1)
        | Ok _ =>
          rw [hlo1]
          simp only [bind_ok]
          exact (WP.dspec_ok _).mpr (hs2.trans hs1)
      · simp only [hkGt, ↓reduceIte]
        rw [hlo1, bind_ok]
        exact (WP.dspec_ok _).mpr hs1
  · cases failed <;> exact (WP.dspec_ok _).mpr hs1

/-- `postfork.fd_ops.close_fds_above2_except` preserves `blockedSigs`. -/
theorem close_fds_above2_except_dspec_blockedSigs (s : sys.Sys) (extra_keep_fd : I32)
    (keep_fds : Slice I32) :
    WP.dspec (postfork.fd_ops.close_fds_above2_except s extra_keep_fd keep_fds) fun p =>
      p.2.blockedSigs = s.blockedSigs := by
  unfold postfork.fd_ops.close_fds_above2_except
  refine WP.dspec_bind (try_close_range_except_dspec_blockedSigs s extra_keep_fd keep_fds)
    fun ⟨rOut, s1⟩ hs1 => ?_
  cases rOut with
  | Ok _ => exact (WP.dspec_ok _).mpr hs1
  | Err _ =>
    exact WP.dspec_mono (close_via_proc_self_fd_dspec_blockedSigs s1 extra_keep_fd keep_fds)
      fun p hp => hp.trans hs1

end BwrapAndGuestCommon

end LeanSwe.PostFork.Proofs
