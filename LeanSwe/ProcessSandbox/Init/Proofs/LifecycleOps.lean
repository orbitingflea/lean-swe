import LeanSwe.ProcessSandbox.Init.Proofs.OracleOps

/-!
# ProcessSandbox Init Waitpid, Fork, and Guest Lifecycle Proofs

Machine-checked coverage of post-`READY` `psandbox_init::ops` lifecycle paths driven by
explicit `InitState` syscall oracles:
- `waitpid_blocking` in `ops.wait_direct_child`, `ops.kill_and_reap_descendants`, and
  `ops.supervise_child` (`PS_STATUS_EXITED` for `0..255` and `PS_STATUS_SIGNALED` for `1..126`),
- `fork_proc` branches (`.child`, `.parent pid`, `.err e`),
- `ops.run_guest_child` (`execvp` failure vs `chdir` failure reporting),
- `ops.run_init` dispatch across `go_fd` EOF skip, child branch (`127`), parent branch (`0`),
  and `fork` error (`1`).
-/

namespace LeanSwe.ProcessSandbox.Init.Proofs

open _root_.Aeneas _root_.Aeneas.Std Result ControlFlow
open psandbox_init
open LeanSwe.ProcessSandbox.Init.World

private theorem bind_pair_ok {α β γ : Type} {m : Result (α × β)} {a : α} {b : β}
    {k : α → β → Result γ} (hm : m = Result.ok (a, b)) :
    (do let (x, y) ← m; k x y) = k a b := by
  rw [hm]; simp

/-- `ops.wait_direct_child` retries `EINTR` (`4`) and returns the oracle-supplied `wstatus`. -/
theorem wait_direct_child_eintr_retry (s : init_sys.Sys) (child_pid rpid wst : I32)
    (rest : List WaitpidOutcome) :
    ops.wait_direct_child
        { s with waitpidOracle := .err 4#i32 :: .reaped rpid wst :: rest } child_pid =
      Result.ok (wst,
        { s with
          waitpidOracle := rest
          reapedPids := s.reapedPids ++ [(rpid, wst)] }) := by
  have hStep1 :
      ops.wait_direct_child_loop.body child_pid
          { s with waitpidOracle := .err 4#i32 :: .reaped rpid wst :: rest } =
        Result.ok (cont { s with waitpidOracle := .reaped rpid wst :: rest }) := by
    unfold ops.wait_direct_child_loop.body init_sys.waitpid_blocking ops.EINTR
    simp [sanitizeErrno_eq_of_bounds 4#i32 (by decide) (by decide)]
  have hStep2 :
      ops.wait_direct_child_loop.body child_pid
          { s with waitpidOracle := .reaped rpid wst :: rest } =
        Result.ok (done (wst,
          { s with waitpidOracle := rest, reapedPids := s.reapedPids ++ [(rpid, wst)] })) := by
    unfold ops.wait_direct_child_loop.body init_sys.waitpid_blocking
    simp
  unfold ops.wait_direct_child ops.wait_direct_child_loop
  rw [loop_cont _ _ _ hStep1, loop_done _ _ _ hStep2]

/-- `ops.kill_and_reap_descendants` drains queued descendants across `EINTR` retry until `ECHILD`. -/
theorem kill_and_reap_descendants_reaps_queue (s : init_sys.Sys) :
    ops.kill_and_reap_descendants
        { s with
          waitpidOracle := [.reaped 3#i32 9#i32, .err 4#i32, .reaped 4#i32 15#i32] } =
      Result.ok
        { s with
          waitpidOracle := []
          reapedPids := s.reapedPids ++ [(3#i32, 9#i32), (4#i32, 15#i32)] } := by
  let s1 : init_sys.Sys :=
    { s with
      waitpidOracle := [.err 4#i32, .reaped 4#i32 15#i32]
      reapedPids := s.reapedPids ++ [(3#i32, 9#i32)] }
  let s2 : init_sys.Sys :=
    { s with
      waitpidOracle := [.reaped 4#i32 15#i32]
      reapedPids := s.reapedPids ++ [(3#i32, 9#i32)] }
  let s3 : init_sys.Sys :=
    { s with
      waitpidOracle := []
      reapedPids := s.reapedPids ++ [(3#i32, 9#i32), (4#i32, 15#i32)] }
  have h1 :
      ops.kill_and_reap_descendants_loop.body
          { s with waitpidOracle := [.reaped 3#i32 9#i32, .err 4#i32, .reaped 4#i32 15#i32] } =
        Result.ok (cont s1) := by
    unfold ops.kill_and_reap_descendants_loop.body init_sys.waitpid_blocking
    simp [s1]
  have h2 : ops.kill_and_reap_descendants_loop.body s1 = Result.ok (cont s2) := by
    unfold ops.kill_and_reap_descendants_loop.body init_sys.waitpid_blocking ops.EINTR
    simp [s1, s2, sanitizeErrno_eq_of_bounds 4#i32 (by decide) (by decide)]
  have h3 : ops.kill_and_reap_descendants_loop.body s2 = Result.ok (cont s3) := by
    unfold ops.kill_and_reap_descendants_loop.body init_sys.waitpid_blocking
    simp [s2, s3, List.append_assoc]
  have h4 : ops.kill_and_reap_descendants_loop.body s3 = Result.ok (done s3) := by
    unfold ops.kill_and_reap_descendants_loop.body init_sys.waitpid_blocking
      ops.EINTR ops.ECHILD ECHILD
    simp [s3]
  unfold ops.kill_and_reap_descendants init_sys.kill_all_sigkill ops.kill_and_reap_descendants_loop
  rw [bind_ok, loop_cont _ _ _ h1, loop_cont _ _ _ h2, loop_cont _ _ _ h3, loop_done _ _ _ h4]

private theorem supervise_child_of_status (s : init_sys.Sys)
    (child_pid err_r err_w status_fd wstatus : I32)
    (kind flag : U8) (val : I32)
    (hEr : 0 ≤ err_r.val) (hEw : 0 ≤ err_w.val) (hSt : 0 ≤ status_fd.val)
    (hClass : ops.classify_wait_status wstatus = Result.ok (kind, flag, val)) :
    ∃ msg : Array U8 8#usize,
      ops.encode_status_msg kind flag val = Result.ok msg ∧
      ops.supervise_child { s with waitpidOracle := [.reaped child_pid wstatus] }
          child_pid err_r err_w status_fd =
        Result.ok (0#i32,
          { s with
            waitpidOracle := []
            reapedPids := s.reapedPids ++ [(child_pid, wstatus)]
            writes := s.writes ++ [(status_fd, msg.val)]
            closedFds := s.closedFds ++ [err_w, 0#i32, 1#i32, 2#i32, err_r, status_fd] }) := by
  let s0 : init_sys.Sys := { s with waitpidOracle := [.reaped child_pid wstatus] }
  let s1 : init_sys.Sys := { s0 with closedFds := s.closedFds ++ [err_w] }
  let s2 : init_sys.Sys := { s0 with closedFds := s.closedFds ++ [err_w, 0#i32] }
  let s3 : init_sys.Sys := { s0 with closedFds := s.closedFds ++ [err_w, 0#i32, 1#i32] }
  let s4 : init_sys.Sys := { s0 with closedFds := s.closedFds ++ [err_w, 0#i32, 1#i32, 2#i32] }
  let s5 : init_sys.Sys :=
    { s0 with closedFds := s.closedFds ++ [err_w, 0#i32, 1#i32, 2#i32, err_r] }
  let s6 : init_sys.Sys :=
    { s5 with waitpidOracle := [], reapedPids := s.reapedPids ++ [(child_pid, wstatus)] }
  have hRead :
      ops.read_exec_err_frame s4 err_r =
        Result.ok ((Array.repeat 8#usize 0#u8, 0#usize), s5) := by
    have hErN : ¬ (err_r.val < 0) := by omega
    have hStep :
        ops.read_exec_err_frame_loop.body err_r s4 (Array.repeat 8#usize 0#u8) 0#usize =
          Result.ok (done (s4, Array.repeat 8#usize 0#u8, 0#usize)) := by
      unfold ops.read_exec_err_frame_loop.body init_sys.read_status_tail; simp [hErN]
    unfold ops.read_exec_err_frame ops.read_exec_err_frame_loop
    extract_lets buf
    rw [bind_triple_ok (loop_done _ _ _ hStep)]
    unfold init_sys.close_fd; simp [hErN, s4, s5, List.append_assoc]
  have hWait : ops.wait_direct_child s5 child_pid = Result.ok (wstatus, s6) := by
    unfold ops.wait_direct_child ops.wait_direct_child_loop
    apply loop_done
    unfold ops.wait_direct_child_loop.body init_sys.waitpid_blocking
    simp [s5, s6, s0]
  have hKill : ops.kill_and_reap_descendants s6 = Result.ok s6 := by
    unfold ops.kill_and_reap_descendants init_sys.kill_all_sigkill
      ops.kill_and_reap_descendants_loop
    rw [bind_ok]; apply loop_done
    unfold ops.kill_and_reap_descendants_loop.body init_sys.waitpid_blocking
      ops.EINTR ops.ECHILD ECHILD
    simp [s6]
  obtain ⟨msg, hEnc, hSend⟩ := send_status_ok s6 status_fd kind flag val hSt
  refine ⟨msg, hEnc, ?_⟩
  have hC1 : init_sys.close_fd s0 err_w = Result.ok (.Ok (), s1) := by
    unfold init_sys.close_fd; rw [if_false_eq (by omega)]
  have hC2 : init_sys.close_fd s1 0#i32 = Result.ok (.Ok (), s2) := by
    unfold init_sys.close_fd; simp [s1, s2, List.append_assoc]
  have hC3 : init_sys.close_fd s2 1#i32 = Result.ok (.Ok (), s3) := by
    unfold init_sys.close_fd; simp [s2, s3, List.append_assoc]
  have hC4 : init_sys.close_fd s3 2#i32 = Result.ok (.Ok (), s4) := by
    unfold init_sys.close_fd; simp [s3, s4, List.append_assoc]
  have hCSt :
      init_sys.close_fd { s6 with writes := s6.writes ++ [(status_fd, msg.val)] } status_fd =
        Result.ok (.Ok (),
          { s with
            waitpidOracle := []
            reapedPids := s.reapedPids ++ [(child_pid, wstatus)]
            writes := s.writes ++ [(status_fd, msg.val)]
            closedFds := s.closedFds ++ [err_w, 0#i32, 1#i32, 2#i32, err_r, status_fd] }) := by
    unfold init_sys.close_fd; rw [if_false_eq (by omega)]
    simp [s6, s5, s0, List.append_assoc]
  unfold ops.supervise_child
  refine eq_ok_of_bind hC1 (eq_ok_of_bind hC2 (eq_ok_of_bind hC3 (eq_ok_of_bind hC4
    (eq_ok_of_bind hRead ?_))))
  exact eq_ok_of_bind hWait (eq_ok_of_bind hKill (eq_ok_of_bind hClass
    (eq_ok_of_bind hSend (eq_ok_of_bind hCSt rfl))))

/-- `ops.supervise_child` reaps a normal exit `code * 256` (`0..255`) and emits `PS_STATUS_EXITED`. -/
theorem supervise_child_exited_writes_status (s : init_sys.Sys)
    (child_pid err_r err_w status_fd : I32) (code : Nat) (hCode : code < 256)
    (hEr : 0 ≤ err_r.val) (hEw : 0 ≤ err_w.val) (hSt : 0 ≤ status_fd.val) :
    ∃ msg : Array U8 8#usize,
      ops.encode_status_msg 4#u8 0#u8 ⟨BitVec.ofNat 32 code⟩ = Result.ok msg ∧
      ops.supervise_child
          { s with waitpidOracle := [.reaped child_pid ⟨BitVec.ofNat 32 (code * 256)⟩] }
          child_pid err_r err_w status_fd =
        Result.ok (0#i32,
          { s with
            waitpidOracle := []
            reapedPids := s.reapedPids ++ [(child_pid, ⟨BitVec.ofNat 32 (code * 256)⟩)]
            writes := s.writes ++ [(status_fd, msg.val)]
            closedFds := s.closedFds ++ [err_w, 0#i32, 1#i32, 2#i32, err_r, status_fd] }) :=
  supervise_child_of_status s child_pid err_r err_w status_fd
    ⟨BitVec.ofNat 32 (code * 256)⟩ 4#u8 0#u8 ⟨BitVec.ofNat 32 code⟩
    hEr hEw hSt (classify_wait_status_exited code hCode)

/-- `ops.supervise_child` reaps a fatal signal (`1..126`) and emits `PS_STATUS_SIGNALED`. -/
theorem supervise_child_signaled_writes_status (s : init_sys.Sys)
    (child_pid err_r err_w status_fd : I32) (sig : Nat) (hLo : 1 ≤ sig) (hHi : sig ≤ 126)
    (hEr : 0 ≤ err_r.val) (hEw : 0 ≤ err_w.val) (hSt : 0 ≤ status_fd.val) :
    ∃ msg : Array U8 8#usize,
      ops.encode_status_msg 5#u8 0#u8 ⟨BitVec.ofNat 32 sig⟩ = Result.ok msg ∧
      ops.supervise_child
          { s with waitpidOracle := [.reaped child_pid ⟨BitVec.ofNat 32 sig⟩] }
          child_pid err_r err_w status_fd =
        Result.ok (0#i32,
          { s with
            waitpidOracle := []
            reapedPids := s.reapedPids ++ [(child_pid, ⟨BitVec.ofNat 32 sig⟩)]
            writes := s.writes ++ [(status_fd, msg.val)]
            closedFds := s.closedFds ++ [err_w, 0#i32, 1#i32, 2#i32, err_r, status_fd] }) :=
  supervise_child_of_status s child_pid err_r err_w status_fd
    ⟨BitVec.ofNat 32 sig⟩ 5#u8 0#u8 ⟨BitVec.ofNat 32 sig⟩
    hEr hEw hSt (classify_wait_status_signaled sig hLo hHi)

/-- `init_sys.fork_proc` returns `Ok 0` (child), `Ok pid` (parent with `pid > 0`), or `Err e` (`1..4095`). -/
theorem fork_proc_branches_spec (s : init_sys.Sys) (pid e : I32)
    (hPid : 0 < pid.val) (hLo : 1 ≤ e.val) (hHi : e.val ≤ 4095) :
    init_sys.fork_proc { s with forkOutcome := .child } =
      Result.ok (.Ok 0#i32, { s with forkOutcome := .child }) ∧
    init_sys.fork_proc { s with forkOutcome := .parent pid } =
      Result.ok (.Ok pid, { s with forkOutcome := .parent pid }) ∧
    init_sys.fork_proc { s with forkOutcome := .err e } =
      Result.ok (.Err e, { s with forkOutcome := .err e }) := by
  unfold init_sys.fork_proc
  refine ⟨rfl, ?_, ?_⟩
  · simp [hPid]
  · simp [sanitizeErrno_eq_of_bounds e hLo hHi]

private theorem close_guest_extra_fds_15 (s : init_sys.Sys) :
    ops.close_guest_extra_fds s 15#i32 = Result.ok s := by
  unfold ops.close_guest_extra_fds
  have hMax : U32.max = 4294967295 := by
    rw [U32.max_def, U32.numBits_def, UScalarTy.U32_numBits_eq]; decide
  rw [if_false_eq (by decide : ¬ (15#i32 ≤ 2#i32))]
  dsimp only [lift]
  rw [bind_ok, show (IScalar.hcast .U32 15#i32 : U32) = 15#u32 from by decide,
    if_true_eq (by decide : 15#u32 > 3#u32),
    u32_sub_ok_eq 15#u32 1#u32 14#u32 (by decide) rfl, bind_ok]
  have hCr1 : init_sys.close_range s 3#u32 14#u32 = Result.ok (.Ok (), s) := by
    unfold init_sys.close_range; rw [if_false_eq (by decide)]
  have hCr2 : init_sys.close_range s 16#u32 core.num.U32.MAX = Result.ok (.Ok (), s) := by
    unfold init_sys.close_range core.num.U32.MAX; rw [if_false_eq (by decide)]
  rw [bind_pair_ok hCr1]
  simp only [core.result.Result.is_ok, bind_ok]
  change (do
    let i ← 15#u32 + 1#u32
    let (r, s2) ← init_sys.close_range s i core.num.U32.MAX
    let ok2 ← core.result.Result.is_ok r
    if true = true then
      if ok2 = true then ok s2
      else do
        let (r1, s3) ← ops.close_via_proc_self_fd s2 15#i32
        let b ← core.result.Result.is_ok r1
        if b = true then ok s3 else ops.close_guest_extra_fds_loop1 s3 15#i32 3#i32
    else do
      let (r1, s3) ← ops.close_via_proc_self_fd s2 15#i32
      let b ← core.result.Result.is_ok r1
      if b = true then ok s3 else ops.close_guest_extra_fds_loop2 s3 15#i32 3#i32) = Result.ok s
  rw [u32_add_ok_eq 15#u32 1#u32 16#u32 (by change 15 + 1 ≤ U32.max; omega) rfl, bind_ok,
    bind_pair_ok hCr2]
  simp [core.result.Result.is_ok]

private theorem install_guest_env_zero (s : init_sys.Sys) (tbl : init_sys.ExecTable) :
    ops.install_guest_env s tbl 0#u32 = Result.ok (.Ok (), s) := by
  have hDone : ops.install_guest_env_loop.body tbl 0#u32 ops.EIO s 0#u32 =
      Result.ok (done (s, ops.EIO, false)) := by
    unfold ops.install_guest_env_loop.body; simp
  have hLoop : ops.install_guest_env_loop s tbl 0#u32 0#u32 ops.EIO =
      Result.ok (s, ops.EIO, false) := loop_done _ _ _ hDone
  unfold ops.install_guest_env
  exact eq_ok_of_bind (show init_sys.clearenv_guest s = Result.ok (.Ok (), s) from rfl)
    (eq_ok_of_bind (show core.result.Result.Insts.CoreOpsTry.branch (.Ok ()) =
        Result.ok (core.ops.control_flow.ControlFlow.Continue ()) from rfl)
      (eq_ok_of_bind hLoop rfl))

/-- `ops.run_guest_child` writes `(PS_STATUS_EXEC_ERR, 0, ENOENT)` and exits `127` on `execvp` failure. -/
theorem run_guest_child_exec_err_spec (s : init_sys.Sys) (err_r status_fd : I32)
    (tbl : init_sys.ExecTable) (hEr : 0 ≤ err_r.val) (hSt : 0 ≤ status_fd.val)
    (hCwd : tbl.cwd.isEmpty = false) :
    ∃ msg : Array U8 8#usize,
      ops.encode_status_msg 3#u8 0#u8 2#i32 = Result.ok msg ∧
      ops.run_guest_child s err_r 15#i32 status_fd tbl 0#u32 =
        Result.ok
          { s with
            closedFds := s.closedFds ++ [err_r, status_fd]
            writes := s.writes ++ [(15#i32, msg.val)]
            exitCode? := some 127#i32 } := by
  let s1 : init_sys.Sys := { s with closedFds := s.closedFds ++ [err_r] }
  let s2 : init_sys.Sys := { s with closedFds := s.closedFds ++ [err_r, status_fd] }
  obtain ⟨msg, hEnc, hSend⟩ := send_status_ok s2 15#i32 3#u8 0#u8 2#i32 (by decide)
  refine ⟨msg, hEnc, ?_⟩
  have hC1 : init_sys.close_fd s err_r = Result.ok (.Ok (), s1) := by
    unfold init_sys.close_fd; rw [if_false_eq (by omega)]
  have hC2 : init_sys.close_fd s1 status_fd = Result.ok (.Ok (), s2) := by
    unfold init_sys.close_fd; rw [if_false_eq (by omega)]; simp [s1, s2, List.append_assoc]
  have hChdir : init_sys.chdir_guest s2 tbl = Result.ok (.Ok (), s2) := by
    unfold init_sys.chdir_guest; simp [hCwd]
  unfold ops.run_guest_child
  rw [bind_pair_ok hC1, bind_pair_ok hC2, bind_val_ok (close_guest_extra_fds_15 s2),
    bind_val_ok (show init_sys.reset_sigpipe_dfl s2 = Result.ok s2 from rfl),
    bind_pair_ok (install_guest_env_zero s2 tbl)]
  dsimp only
  rw [bind_pair_ok hChdir]
  dsimp only
  rw [bind_pair_ok (show init_sys.execvp_guest s2 tbl = Result.ok (2#i32, s2) from rfl)]
  unfold ops.PS_STATUS_EXEC_ERR
  rw [bind_val_ok hSend]
  rfl

/-- `ops.run_guest_child` writes `(PS_STATUS_EXEC_ERR, 1, ENOENT)` (`isCwd = 1`) on `chdir` failure. -/
theorem run_guest_child_chdir_err_spec (s : init_sys.Sys) (err_r status_fd : I32)
    (tbl : init_sys.ExecTable) (hEr : 0 ≤ err_r.val) (hSt : 0 ≤ status_fd.val)
    (hCwd : tbl.cwd = []) :
    ∃ msg : Array U8 8#usize,
      ops.encode_status_msg 3#u8 1#u8 2#i32 = Result.ok msg ∧
      ops.run_guest_child s err_r 15#i32 status_fd tbl 0#u32 =
        Result.ok
          { s with
            closedFds := s.closedFds ++ [err_r, status_fd]
            writes := s.writes ++ [(15#i32, msg.val)]
            exitCode? := some 127#i32 } := by
  let s1 : init_sys.Sys := { s with closedFds := s.closedFds ++ [err_r] }
  let s2 : init_sys.Sys := { s with closedFds := s.closedFds ++ [err_r, status_fd] }
  obtain ⟨msg, hEnc, hSend⟩ := send_status_ok s2 15#i32 3#u8 1#u8 2#i32 (by decide)
  refine ⟨msg, hEnc, ?_⟩
  have hC1 : init_sys.close_fd s err_r = Result.ok (.Ok (), s1) := by
    unfold init_sys.close_fd; rw [if_false_eq (by omega)]
  have hC2 : init_sys.close_fd s1 status_fd = Result.ok (.Ok (), s2) := by
    unfold init_sys.close_fd; rw [if_false_eq (by omega)]; simp [s1, s2, List.append_assoc]
  have hChdir : init_sys.chdir_guest s2 tbl = Result.ok (.Err 2#i32, s2) := by
    unfold init_sys.chdir_guest; simp [hCwd]
  unfold ops.run_guest_child
  rw [bind_pair_ok hC1, bind_pair_ok hC2, bind_val_ok (close_guest_extra_fds_15 s2),
    bind_val_ok (show init_sys.reset_sigpipe_dfl s2 = Result.ok s2 from rfl),
    bind_pair_ok (install_guest_env_zero s2 tbl)]
  dsimp only
  rw [bind_pair_ok hChdir]
  dsimp only
  unfold ops.PS_STATUS_EXEC_ERR
  rw [bind_val_ok hSend]
  rfl

private theorem set_cloexec_noop (s : init_sys.Sys) (fd : I32) :
    ops.set_cloexec_if_valid s fd = Result.ok s := by
  unfold ops.set_cloexec_if_valid
  by_cases h : fd ≥ 0#i32
  · have hNotNeg : ¬ (fd.val < 0) := by
      have hGe : (0#i32).val ≤ fd.val := by simpa using h
      change ¬ (fd.val < 0)
      have h0 : (0#i32).val = 0 := rfl
      omega
    have hGet : init_sys.fcntl_getfd s fd = Result.ok (.Ok 0#i32, s) := by
      unfold init_sys.fcntl_getfd; rw [if_false_eq hNotNeg]
    have hSet : ∀ fl : I32, init_sys.fcntl_setfd s fd fl = Result.ok (.Ok (), s) := by
      intro fl; unfold init_sys.fcntl_setfd; rw [if_false_eq hNotNeg]
    rw [if_true_eq h]
    exact eq_ok_of_bind hGet (eq_ok_of_bind (show lift (0#i32 ||| ops.FD_CLOEXEC) =
      Result.ok (0#i32 ||| ops.FD_CLOEXEC) from rfl) (eq_ok_of_bind (hSet _) rfl))
  · simp [h]

private theorem sys_with_read1_self (s : init_sys.Sys) (o : List Read1Outcome)
    (h : s.read1Oracle = o) : { s with read1Oracle := o } = s := by
  cases s; simp only at h; subst h; rfl

private theorem sys_with_waitpid_self (s : init_sys.Sys) (o : List WaitpidOutcome)
    (h : s.waitpidOracle = o) : { s with waitpidOracle := o } = s := by
  cases s; simp only at h; subst h; rfl

private theorem eq_of_bind_ok {α β : Type} {m : Result α} {v : α} {k : α → Result β} {rhs : Result β}
    (hm : m = Result.ok v) (hk : k v = rhs) : (m >>= k) = rhs := by
  rw [hm]; simpa using hk

private theorem run_init_ready_tail
    (s0 s1 s6 s8 : init_sys.Sys) (argc : Usize) (f : cli.CliFds) (b : init_sys.PlanBuf)
    (exec_tbl : init_sys.ExecTable) (envc : U32) (ctrlOut : I32)
    (hPlanFd : 0 ≤ f.plan_fd.val) (hStatusFd : 0 ≤ f.status_fd.val) (hGoFd : 0 ≤ f.go_fd.val)
    (hParse : cli.parse_cli s0 argc = Result.ok (.Run f, s1))
    (hRead : ops.read_plan_fd s1 f.plan_fd = Result.ok (.Ok b, s6))
    (hSetup : ops.setup_sandbox_from_plan
      { s6 with closedFds := s6.closedFds ++ [f.plan_fd] } b f.ctrl_fd =
      Result.ok (.Ok (exec_tbl, envc), s8, ctrlOut)) :
    ∃ msgReady : Array U8 8#usize,
      ops.encode_status_msg 1#u8 0#u8 0#i32 = Result.ok msgReady ∧
      ops.run_init s0 argc =
        (let s10 : init_sys.Sys := { s8 with writes := s8.writes ++ [(f.status_fd, msgReady.val)] }
         do
          let (b1, s11) ← ops.wait_for_go_byte s10 f.go_fd
          if b1 then
            let (r3, s12) ← init_sys.pipe2_cloexec s11
            match r3 with
            | core.result.Result.Ok p =>
              let (err_r, err_w) := p
              let (r4, s13) ← init_sys.fork_proc s12
              match r4 with
              | core.result.Result.Ok child_pid =>
                match child_pid with
                | 0#iscalar =>
                  let s14 ← ops.run_guest_child s13 err_r err_w f.status_fd exec_tbl envc
                  Result.ok (127#i32, s14)
                | _ => ops.supervise_child s13 child_pid err_r err_w f.status_fd
              | core.result.Result.Err e =>
                let (_, s14) ← init_sys.close_fd s13 err_r
                let (_, s15) ← init_sys.close_fd s14 err_w
                let s16 ← ops.send_status s15 f.status_fd ops.PS_STATUS_INIT_ERR 0#u8 e
                Result.ok (1#i32, s16)
            | core.result.Result.Err e =>
              let s13 ← ops.send_status s12 f.status_fd ops.PS_STATUS_INIT_ERR 0#u8 e
              Result.ok (1#i32, s13)
          else
            let (_, s12) ← init_sys.close_fd s11 f.status_fd
            Result.ok (0#i32, s12)) := by
  obtain ⟨msgReady, hEnc, hSend⟩ := send_status_ok s8 f.status_fd 1#u8 0#u8 0#i32 hStatusFd
  refine ⟨msgReady, hEnc, ?_⟩
  have hVal : cli.validate_cli_fds f = Result.ok (.Ok f) := by
    unfold cli.validate_cli_fds
    have hp : ¬ (f.plan_fd < 0#i32) := by change ¬ (f.plan_fd.val < 0); omega
    have hs : ¬ (f.status_fd < 0#i32) := by change ¬ (f.status_fd.val < 0); omega
    have hg : ¬ (f.go_fd < 0#i32) := by change ¬ (f.go_fd.val < 0); omega
    simp [hp, hs, hg]
  have hClosePlan : init_sys.close_fd s6 f.plan_fd =
      Result.ok (.Ok (), { s6 with closedFds := s6.closedFds ++ [f.plan_fd] }) := by
    unfold init_sys.close_fd; rw [if_false_eq (by omega)]
  have hSendR : ops.send_status s8 f.status_fd ops.PS_STATUS_READY 0#u8 0#i32 =
      Result.ok { s8 with writes := s8.writes ++ [(f.status_fd, msgReady.val)] } := by
    unfold ops.PS_STATUS_READY; exact hSend
  unfold ops.run_init
  exact eq_of_bind_ok hParse (eq_of_bind_ok (set_cloexec_noop _ _)
    (eq_of_bind_ok (set_cloexec_noop _ _)
      (eq_of_bind_ok (set_cloexec_noop _ _)
        (eq_of_bind_ok (set_cloexec_noop _ _)
          (eq_of_bind_ok hVal (eq_of_bind_ok hRead (eq_of_bind_ok hClosePlan
            (eq_of_bind_ok hSetup
              (eq_of_bind_ok (show init_sys.plan_buf_free s8 b = Result.ok s8 from rfl)
                (eq_of_bind_ok hSendR rfl))))))))))

/-- `ops.run_init` emits `READY`, closes `go_fd` and `status_fd`, and exits `0` without calling `fork` on EOF. -/
theorem run_init_go_eof_skips_fork
    (s0 s1 s6 s8 : init_sys.Sys) (argc : Usize) (f : cli.CliFds) (b : init_sys.PlanBuf)
    (exec_tbl : init_sys.ExecTable) (envc : U32) (ctrlOut : I32)
    (hPlanFd : 0 ≤ f.plan_fd.val) (hStatusFd : 0 ≤ f.status_fd.val) (hGoFd : 0 ≤ f.go_fd.val)
    (hParse : cli.parse_cli s0 argc = Result.ok (.Run f, s1))
    (hRead : ops.read_plan_fd s1 f.plan_fd = Result.ok (.Ok b, s6))
    (hSetup : ops.setup_sandbox_from_plan
      { s6 with closedFds := s6.closedFds ++ [f.plan_fd] } b f.ctrl_fd =
      Result.ok (.Ok (exec_tbl, envc), s8, ctrlOut))
    (hEof : s8.read1Oracle = []) :
    ∃ msgReady : Array U8 8#usize,
      ops.encode_status_msg 1#u8 0#u8 0#i32 = Result.ok msgReady ∧
      ops.run_init s0 argc =
        Result.ok (0#i32,
          { s8 with
            writes := s8.writes ++ [(f.status_fd, msgReady.val)]
            closedFds := s8.closedFds ++ [f.go_fd, f.status_fd] }) := by
  obtain ⟨msgReady, hEnc, hTail⟩ := run_init_ready_tail s0 s1 s6 s8 argc f b exec_tbl envc ctrlOut
    hPlanFd hStatusFd hGoFd hParse hRead hSetup
  refine ⟨msgReady, hEnc, ?_⟩
  let s10 : init_sys.Sys := { s8 with writes := s8.writes ++ [(f.status_fd, msgReady.val)] }
  have hGo : ops.wait_for_go_byte s10 f.go_fd =
      Result.ok (false, { s10 with closedFds := s10.closedFds ++ [f.go_fd] }) := by
    have hW := wait_for_go_byte_eof s10 f.go_fd hGoFd
    rw [sys_with_read1_self s10 [] (by simpa [s10] using hEof)] at hW
    simpa [s10, hEof] using hW
  have hClose :
      init_sys.close_fd { s10 with closedFds := s10.closedFds ++ [f.go_fd] } f.status_fd =
        Result.ok (.Ok (),
          { s8 with
            writes := s8.writes ++ [(f.status_fd, msgReady.val)]
            closedFds := s8.closedFds ++ [f.go_fd, f.status_fd] }) := by
    unfold init_sys.close_fd; rw [if_false_eq (by omega)]; simp [s10, List.append_assoc]
  rw [hTail, bind_pair_ok hGo, if_false_eq (by decide : ¬ (false = true)), bind_pair_ok hClose]

/-- `ops.run_init` runs `run_guest_child` (`127`, `exitCode? = some 127`) when `forkOutcome = .child`. -/
theorem run_init_fork_child_branch
    (s0 s1 s6 s8 : init_sys.Sys) (argc : Usize) (f : cli.CliFds) (b : init_sys.PlanBuf)
    (exec_tbl : init_sys.ExecTable) (ctrlOut : I32) (goByte : U8) (restRead : List Read1Outcome)
    (hPlanFd : 0 ≤ f.plan_fd.val) (hStatusFd : 0 ≤ f.status_fd.val) (hGoFd : 0 ≤ f.go_fd.val)
    (hParse : cli.parse_cli s0 argc = Result.ok (.Run f, s1))
    (hRead : ops.read_plan_fd s1 f.plan_fd = Result.ok (.Ok b, s6))
    (hSetup : ops.setup_sandbox_from_plan
      { s6 with closedFds := s6.closedFds ++ [f.plan_fd] } b f.ctrl_fd =
      Result.ok (.Ok (exec_tbl, 0#u32), s8, ctrlOut))
    (hGo : s8.read1Oracle = .byte goByte :: restRead)
    (hFork : s8.forkOutcome = .child) (hCwd : exec_tbl.cwd.isEmpty = false) :
    ∃ msgReady msgErr : Array U8 8#usize,
      ops.encode_status_msg 1#u8 0#u8 0#i32 = Result.ok msgReady ∧
      ops.encode_status_msg 3#u8 0#u8 2#i32 = Result.ok msgErr ∧
      ops.run_init s0 argc =
        Result.ok (127#i32,
          { s8 with
            read1Oracle := restRead
            writes := s8.writes ++ [(f.status_fd, msgReady.val), (15#i32, msgErr.val)]
            closedFds := s8.closedFds ++ [f.go_fd, 14#i32, f.status_fd]
            exitCode? := some 127#i32 }) := by
  obtain ⟨msgReady, hEncR, hTail⟩ := run_init_ready_tail s0 s1 s6 s8 argc f b exec_tbl 0#u32 ctrlOut
    hPlanFd hStatusFd hGoFd hParse hRead hSetup
  let s10 : init_sys.Sys := { s8 with writes := s8.writes ++ [(f.status_fd, msgReady.val)] }
  let s11 : init_sys.Sys :=
    { s10 with read1Oracle := restRead, closedFds := s10.closedFds ++ [f.go_fd] }
  obtain ⟨msgErr, hEncE, hChild⟩ :=
    run_guest_child_exec_err_spec s11 14#i32 f.status_fd exec_tbl (by decide) hStatusFd hCwd
  refine ⟨msgReady, msgErr, hEncR, hEncE, ?_⟩
  have hGoRes : ops.wait_for_go_byte s10 f.go_fd = Result.ok (true, s11) := by
    have hW := wait_for_go_byte_released s10 f.go_fd goByte restRead hGoFd
    rw [sys_with_read1_self s10 (.byte goByte :: restRead) (by simpa [s10] using hGo)] at hW
    exact hW
  have hForkRes : init_sys.fork_proc s11 = Result.ok (.Ok 0#i32, s11) := by
    unfold init_sys.fork_proc; simp [s11, s10, hFork]
  rw [hTail]
  exact eq_ok_of_bind hGoRes (eq_ok_of_bind
    (show init_sys.pipe2_cloexec s11 = Result.ok (.Ok (14#i32, 15#i32), s11) from rfl)
    (eq_ok_of_bind hForkRes (eq_ok_of_bind hChild (by simp [s11, s10, List.append_assoc]))))

/-- `ops.run_init` runs `supervise_child` (`0`, writing `PS_STATUS_EXITED`) when `forkOutcome = .parent childPid`. -/
theorem run_init_fork_parent_branch
    (s0 s1 s6 s8 : init_sys.Sys) (argc : Usize) (f : cli.CliFds) (b : init_sys.PlanBuf)
    (exec_tbl : init_sys.ExecTable) (envc : U32) (ctrlOut childPid : I32)
    (goByte : U8) (restRead : List Read1Outcome) (code : Nat) (hCode : code < 256)
    (hPid : 0 < childPid.val)
    (hPlanFd : 0 ≤ f.plan_fd.val) (hStatusFd : 0 ≤ f.status_fd.val) (hGoFd : 0 ≤ f.go_fd.val)
    (hParse : cli.parse_cli s0 argc = Result.ok (.Run f, s1))
    (hRead : ops.read_plan_fd s1 f.plan_fd = Result.ok (.Ok b, s6))
    (hSetup : ops.setup_sandbox_from_plan
      { s6 with closedFds := s6.closedFds ++ [f.plan_fd] } b f.ctrl_fd =
      Result.ok (.Ok (exec_tbl, envc), s8, ctrlOut))
    (hGo : s8.read1Oracle = .byte goByte :: restRead)
    (hFork : s8.forkOutcome = .parent childPid)
    (hWait : s8.waitpidOracle = [.reaped childPid ⟨BitVec.ofNat 32 (code * 256)⟩]) :
    ∃ msgReady msgExit : Array U8 8#usize,
      ops.encode_status_msg 1#u8 0#u8 0#i32 = Result.ok msgReady ∧
      ops.encode_status_msg 4#u8 0#u8 ⟨BitVec.ofNat 32 code⟩ = Result.ok msgExit ∧
      ops.run_init s0 argc =
        Result.ok (0#i32,
          { s8 with
            read1Oracle := restRead
            waitpidOracle := []
            reapedPids := s8.reapedPids ++ [(childPid, ⟨BitVec.ofNat 32 (code * 256)⟩)]
            writes := s8.writes ++ [(f.status_fd, msgReady.val), (f.status_fd, msgExit.val)]
            closedFds := s8.closedFds ++
              [f.go_fd, 15#i32, 0#i32, 1#i32, 2#i32, 14#i32, f.status_fd] }) := by
  obtain ⟨msgReady, hEncR, hTail⟩ := run_init_ready_tail s0 s1 s6 s8 argc f b exec_tbl envc ctrlOut
    hPlanFd hStatusFd hGoFd hParse hRead hSetup
  let s10 : init_sys.Sys := { s8 with writes := s8.writes ++ [(f.status_fd, msgReady.val)] }
  let s11 : init_sys.Sys :=
    { s10 with read1Oracle := restRead, closedFds := s10.closedFds ++ [f.go_fd] }
  obtain ⟨msgExit, hEncX, hSup⟩ :=
    supervise_child_exited_writes_status s11 childPid 14#i32 15#i32 f.status_fd
      code hCode (by decide) (by decide) hStatusFd
  refine ⟨msgReady, msgExit, hEncR, hEncX, ?_⟩
  have hGoRes : ops.wait_for_go_byte s10 f.go_fd = Result.ok (true, s11) := by
    have hW := wait_for_go_byte_released s10 f.go_fd goByte restRead hGoFd
    rw [sys_with_read1_self s10 (.byte goByte :: restRead) (by simpa [s10] using hGo)] at hW
    exact hW
  have hForkRes : init_sys.fork_proc s11 = Result.ok (.Ok childPid, s11) := by
    unfold init_sys.fork_proc; simp [s11, s10, hFork, hPid]
  have hSupEq :
      ops.supervise_child s11 childPid 14#i32 15#i32 f.status_fd =
        Result.ok (0#i32,
          { s8 with
            read1Oracle := restRead
            waitpidOracle := []
            reapedPids := s8.reapedPids ++ [(childPid, ⟨BitVec.ofNat 32 (code * 256)⟩)]
            writes := s8.writes ++ [(f.status_fd, msgReady.val), (f.status_fd, msgExit.val)]
            closedFds := s8.closedFds ++
              [f.go_fd, 15#i32, 0#i32, 1#i32, 2#i32, 14#i32, f.status_fd] }) := by
    rw [sys_with_waitpid_self s11 [.reaped childPid ⟨BitVec.ofNat 32 (code * 256)⟩]
      (by simpa [s11, s10] using hWait)] at hSup
    simpa [s11, s10, List.append_assoc] using hSup
  have hNe0 : childPid ≠ 0#i32 := by
    intro hEq; have : childPid.val = 0 := by rw [hEq]; rfl
    omega
  rw [hTail]
  refine eq_ok_of_bind hGoRes (eq_ok_of_bind
    (show init_sys.pipe2_cloexec s11 = Result.ok (.Ok (14#i32, 15#i32), s11) from rfl)
    (eq_ok_of_bind hForkRes ?_))
  refine Eq.trans ?_ hSupEq
  change (match childPid with
    | 0#iscalar => do
      let s14 ← ops.run_guest_child s11 14#i32 15#i32 f.status_fd exec_tbl envc
      ok (127#i32, s14)
    | _ => ops.supervise_child s11 childPid 14#i32 15#i32 f.status_fd) = _
  split
  · exact absurd rfl hNe0
  · rfl

/-- `ops.run_init` closes `exec_err_pipe`, emits `PS_STATUS_INIT_ERR(e)`, and exits `1` on `fork_proc` error. -/
theorem run_init_fork_err_branch
    (s0 s1 s6 s8 : init_sys.Sys) (argc : Usize) (f : cli.CliFds) (b : init_sys.PlanBuf)
    (exec_tbl : init_sys.ExecTable) (envc : U32) (ctrlOut e : I32)
    (goByte : U8) (restRead : List Read1Outcome) (hLo : 1 ≤ e.val) (hHi : e.val ≤ 4095)
    (hPlanFd : 0 ≤ f.plan_fd.val) (hStatusFd : 0 ≤ f.status_fd.val) (hGoFd : 0 ≤ f.go_fd.val)
    (hParse : cli.parse_cli s0 argc = Result.ok (.Run f, s1))
    (hRead : ops.read_plan_fd s1 f.plan_fd = Result.ok (.Ok b, s6))
    (hSetup : ops.setup_sandbox_from_plan
      { s6 with closedFds := s6.closedFds ++ [f.plan_fd] } b f.ctrl_fd =
      Result.ok (.Ok (exec_tbl, envc), s8, ctrlOut))
    (hGo : s8.read1Oracle = .byte goByte :: restRead)
    (hFork : s8.forkOutcome = .err e) :
    ∃ msgReady msgErr : Array U8 8#usize,
      ops.encode_status_msg 1#u8 0#u8 0#i32 = Result.ok msgReady ∧
      ops.encode_status_msg 2#u8 0#u8 e = Result.ok msgErr ∧
      ops.run_init s0 argc =
        Result.ok (1#i32,
          { s8 with
            read1Oracle := restRead
            writes := s8.writes ++ [(f.status_fd, msgReady.val), (f.status_fd, msgErr.val)]
            closedFds := s8.closedFds ++ [f.go_fd, 14#i32, 15#i32] }) := by
  obtain ⟨msgReady, hEncR, hTail⟩ := run_init_ready_tail s0 s1 s6 s8 argc f b exec_tbl envc ctrlOut
    hPlanFd hStatusFd hGoFd hParse hRead hSetup
  let s10 : init_sys.Sys := { s8 with writes := s8.writes ++ [(f.status_fd, msgReady.val)] }
  let s11 : init_sys.Sys :=
    { s10 with read1Oracle := restRead, closedFds := s10.closedFds ++ [f.go_fd] }
  let s14 : init_sys.Sys := { s11 with closedFds := s11.closedFds ++ [14#i32] }
  let s15 : init_sys.Sys := { s11 with closedFds := s11.closedFds ++ [14#i32, 15#i32] }
  obtain ⟨msgErr, hEncE, hSendE⟩ := send_status_ok s15 f.status_fd 2#u8 0#u8 e hStatusFd
  refine ⟨msgReady, msgErr, hEncR, hEncE, ?_⟩
  have hGoRes : ops.wait_for_go_byte s10 f.go_fd = Result.ok (true, s11) := by
    have hW := wait_for_go_byte_released s10 f.go_fd goByte restRead hGoFd
    rw [sys_with_read1_self s10 (.byte goByte :: restRead) (by simpa [s10] using hGo)] at hW
    exact hW
  have hForkRes : init_sys.fork_proc s11 = Result.ok (.Err e, s11) := by
    unfold init_sys.fork_proc
    simp [s11, s10, hFork, sanitizeErrno_eq_of_bounds e hLo hHi]
  have hC1 : init_sys.close_fd s11 14#i32 = Result.ok (.Ok (), s14) := by
    unfold init_sys.close_fd; rw [if_false_eq (by decide)]
  have hC2 : init_sys.close_fd s14 15#i32 = Result.ok (.Ok (), s15) := by
    unfold init_sys.close_fd; rw [if_false_eq (by decide)]; simp [s14, s15, List.append_assoc]
  have hSendInit : ops.send_status s15 f.status_fd ops.PS_STATUS_INIT_ERR 0#u8 e =
      Result.ok { s15 with writes := s15.writes ++ [(f.status_fd, msgErr.val)] } := by
    unfold ops.PS_STATUS_INIT_ERR; exact hSendE
  rw [hTail]
  exact eq_ok_of_bind hGoRes (eq_ok_of_bind
    (show init_sys.pipe2_cloexec s11 = Result.ok (.Ok (14#i32, 15#i32), s11) from rfl)
    (eq_ok_of_bind hForkRes (eq_ok_of_bind hC1 (eq_ok_of_bind hC2
      (eq_ok_of_bind hSendInit (by simp [s15, s11, s10, List.append_assoc]))))))

end LeanSwe.ProcessSandbox.Init.Proofs
