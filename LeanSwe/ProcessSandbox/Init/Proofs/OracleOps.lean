import LeanSwe.ProcessSandbox.Init.Proofs.StatusAndOps

/-!
# ProcessSandbox Init Syscall-Oracle Branch Proofs

Machine-checked coverage of non-trivial `psandbox_init::ops` branches driven by
explicit `InitState` syscall oracles:
- `fd_is_dir` in `ops.add_ll_path` (directory vs regular file masking vs dir-only skip vs `fstat` error),
- `read1` in `ops.wait_for_go_byte` (`EOF`, release byte, `EINTR` retry, non-`EINTR` error),
- `sendmsg_scm_batch` in `ops.send_fds_scm` (`34`-FD split `32 + 2`, `EINTR` retry, `Ok 0 -> EIO`, error),
- `seccomp_set_mode_filter` in `ops.install_seccomp` (direct `SYS_seccomp`, `ENOSYS` fallback to `prctl`, error).
-/

namespace LeanSwe.ProcessSandbox.Init.Proofs

open _root_.Aeneas _root_.Aeneas.Std Result ControlFlow
open psandbox_init
open LeanSwe.ProcessSandbox.Init.World

/-- Checked `U32` subtraction equality helper. -/
theorem u32_sub_ok_eq (a b c : U32) (h : b.val ≤ a.val) (hc : c.val = a.val - b.val) :
    (a - b : Result U32) = Result.ok c := by
  obtain ⟨r, hr, hrVal⟩ := (okPost_iff_wp_spec _ _).mpr (U32.sub_spec (x := a) (y := b) h)
  have hEq : r = c := UScalar.eq_of_val_eq (by omega)
  simpa [hEq] using hr

/-- Checked `U32` addition equality helper. -/
theorem u32_add_ok_eq (a b c : U32) (h : a.val + b.val ≤ U32.max)
    (hc : c.val = a.val + b.val) :
    (a + b : Result U32) = Result.ok c := by
  obtain ⟨r, hr, hrVal⟩ := u32_add_ok a b h
  have hEq : r = c := UScalar.eq_of_val_eq (by omega)
  simpa [hEq] using hr

/-- Full-range slice indexing `[0..buf.len]` returns `buf` unchanged. -/
theorem slice_full_range (buf : Slice U8) :
    core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) buf
      { start := 0#usize, «end» := Slice.len buf } = Result.ok buf := by
  change core.slice.index.SliceIndexRangeUsizeSlice.index
    { start := 0#usize, «end» := Slice.len buf } buf = Result.ok buf
  rw [core.slice.index.SliceIndexRangeUsizeSlice.index]
  have hBound :
      ({ start := 0#usize, «end» := Slice.len buf } : core.ops.range.Range Usize).start ≤
        ({ start := 0#usize, «end» := Slice.len buf } : core.ops.range.Range Usize).end ∧
      ({ start := 0#usize, «end» := Slice.len buf } : core.ops.range.Range Usize).end.val ≤
        buf.length := ⟨by change (0#usize).val ≤ (Slice.len buf).val; simp, by simp⟩
  rw [if_true_eq hBound]
  congr 1
  apply Slice.ext
  simp [List.slice]

/-- `ops.write_all` writes a non-empty `Slice U8` to `fd ≥ 0` in one step under the full-write model. -/
theorem write_all_slice_ok (s : init_sys.Sys) (fd : I32) (buf : Slice U8)
    (hFd : 0 ≤ fd.val) (hPos : 0 < buf.val.length) :
    ops.write_all s fd buf =
      Result.ok (.Ok (), { s with writes := s.writes ++ [(fd, buf.val)] }) := by
  unfold ops.write_all
  have hNotNeg : ¬ (fd < 0#i32) := by
    change ¬ (fd.val < (0#i32).val); have h0 : (0#i32).val = 0 := rfl; omega
  rw [if_false_eq hNotNeg]
  dsimp only
  set len := Slice.len buf
  set s' : init_sys.Sys := { s with writes := s.writes ++ [(fd, buf.val)] }
  have hLenVal : len.val = buf.val.length := by simp [len]
  have h0Lt : (0#usize : Usize) < len := by
    change (0#usize).val < len.val; have h0 : (0#usize).val = 0 := rfl; omega
  have hWrite : init_sys.write_fd s fd buf = Result.ok (.Ok len, s') := by
    unfold init_sys.write_fd
    rw [if_false_eq (by omega : ¬ (fd.val < 0))]
  have hSub : (len - 0#usize : Result Usize) = Result.ok len := by
    obtain ⟨r, hr, hrVal⟩ := usize_sub_ok len 0#usize (by
      have h0 : (0#usize).val = 0 := rfl; omega)
    have : r = len := UScalar.eq_of_val_eq (by have h0 : (0#usize).val = 0 := rfl; omega)
    simpa [this] using hr
  have hAdd : (0#usize + len : Result Usize) = Result.ok len := by
    obtain ⟨r, hr, hrVal⟩ := usize_add_ok 0#usize len (by
      have h0 : (0#usize).val = 0 := rfl
      have hM : len.val ≤ Usize.max := by rw [hLenVal]; exact buf.property
      omega)
    have : r = len := UScalar.eq_of_val_eq (by have h0 : (0#usize).val = 0 := rfl; omega)
    simpa [this] using hr
  have hStep1 :
      ops.write_all_loop.body fd buf len ops.EIO s 0#usize = Result.ok (cont (s', len)) := by
    unfold ops.write_all_loop.body
    rw [if_true_eq h0Lt, slice_full_range buf, bind_ok, hWrite]
    simp only [bind_ok]
    have hNe : len.val ≠ 0 := by omega
    cases hEq : len.val with
    | zero => exact absurd hEq hNe
    | succ k => simp [hSub, hAdd]
  have hStep2 :
      ops.write_all_loop.body fd buf len ops.EIO s' len =
        Result.ok (done (s', ops.EIO, false)) := by
    unfold ops.write_all_loop.body
    rw [if_false_eq (by change ¬ (len.val < len.val); exact Nat.lt_irrefl _)]
  unfold ops.write_all_loop
  rw [loop_cont _ _ _ hStep1, loop_done _ _ _ hStep2, bind_ok]
  simp [s']

/-- `ops.send_status` encodes an 8-byte `InitStatusMsg` and appends it to `s.writes` for `fd ≥ 0`. -/
theorem send_status_ok (s : init_sys.Sys) (fd : I32) (kind flag : U8) (value : I32)
    (hFd : 0 ≤ fd.val) :
    ∃ msg : Array U8 8#usize,
      ops.encode_status_msg kind flag value = Result.ok msg ∧
      ops.send_status s fd kind flag value =
        Result.ok { s with writes := s.writes ++ [(fd, msg.val)] } := by
  obtain ⟨msg, hEnc, hVal⟩ := encode_status_msg_spec kind flag value
  refine ⟨msg, hEnc, ?_⟩
  unfold ops.send_status
  have hGe : fd ≥ 0#i32 := by have h0 : (0#i32).val = 0 := rfl; simpa [h0] using hFd
  rw [if_true_eq hGe, hEnc, bind_ok]
  dsimp only [lift]
  rw [bind_ok, write_all_slice_ok s fd (Array.to_slice msg) hFd (by simp [hVal]), bind_ok]
  simp

/-- `ops.add_ll_path` keeps full requested access bits on a directory (`fd_is_dir = .dir`). -/
theorem add_ll_path_dir_spec (s : init_sys.Sys) (rs : I32) (path : Slice U8) (access : U64)
    (rest : List FdIsDirOutcome) (hRs : 0 ≤ rs.val) (hPath : path.val.length < 4096)
    (hAcc : access ≠ 0#u64) :
    ops.add_ll_path { s with fdIsDirOracle := .dir :: rest } rs path access =
      Result.ok (.Ok (),
        { s with
          fdIsDirOracle := rest
          landlockPathRules := s.landlockPathRules ++ [(rs, 12#i32, access)]
          closedFds := s.closedFds ++ [12#i32] }) := by
  have hLen : ¬ (path.val.length ≥ 4096) := by omega
  have hNe0 : access.val ≠ 0 := fun hv => hAcc (UScalar.eq_of_val_eq hv)
  have hRsN : ¬ (rs.val < 0) := by omega
  unfold ops.add_ll_path init_sys.open_path_cloexec init_sys.fd_is_dir
    init_sys.landlock_add_path_rule init_sys.close_fd
  simp [hLen, core.result.Result.Insts.CoreOpsTry.branch,
    landlock_effective_fs_access_spec access true, hNe0, hRsN]

/-- `ops.add_ll_path` strips directory-only Landlock bits on a regular file (`fd_is_dir = .regular`). -/
theorem add_ll_path_regular_masks_dir_bits (s : init_sys.Sys) (rs : I32) (path : Slice U8)
    (access : U64) (rest : List FdIsDirOutcome) (hRs : 0 ≤ rs.val)
    (hPath : path.val.length < 4096) (hEff : access &&& 16391#u64 ≠ 0#u64) :
    ops.add_ll_path { s with fdIsDirOracle := .regular :: rest } rs path access =
      Result.ok (.Ok (),
        { s with
          fdIsDirOracle := rest
          landlockPathRules := s.landlockPathRules ++ [(rs, 12#i32, access &&& 16391#u64)]
          closedFds := s.closedFds ++ [12#i32] }) := by
  have hLen : ¬ (path.val.length ≥ 4096) := by omega
  have hNe0 : (access &&& 16391#u64).val ≠ 0 := fun hv => hEff (UScalar.eq_of_val_eq hv)
  have hRsN : ¬ (rs.val < 0) := by omega
  unfold ops.add_ll_path init_sys.open_path_cloexec init_sys.fd_is_dir
    init_sys.landlock_add_path_rule init_sys.close_fd
  simp [hLen, core.result.Result.Insts.CoreOpsTry.branch,
    landlock_effective_fs_access_spec access false, hRsN]
  simpa using hNe0

/-- `ops.add_ll_path` skips adding a rule (while closing `fd`) when `READ_DIR`-only access masks to `0` on a regular file. -/
theorem add_ll_path_regular_dir_only_skips_rule (s : init_sys.Sys) (rs : I32) (path : Slice U8)
    (rest : List FdIsDirOutcome) (hPath : path.val.length < 4096) :
    ops.add_ll_path { s with fdIsDirOracle := .regular :: rest } rs path 8#u64 =
      Result.ok (.Ok (), { s with fdIsDirOracle := rest, closedFds := s.closedFds ++ [12#i32] }) := by
  have hLen : ¬ (path.val.length ≥ 4096) := by omega
  have hZero : (8#u64 &&& 16391#u64) = 0#u64 := by decide
  unfold ops.add_ll_path init_sys.open_path_cloexec init_sys.fd_is_dir init_sys.close_fd
  simp [hLen, core.result.Result.Insts.CoreOpsTry.branch,
    landlock_effective_fs_access_spec 8#u64 false, hZero]

/-- `ops.add_ll_path` closes descriptor `12` and propagates `e` when `fd_is_dir` fails. -/
theorem add_ll_path_fd_is_dir_err_closes_fd (s : init_sys.Sys) (rs : I32) (path : Slice U8)
    (e : I32) (rest : List FdIsDirOutcome) (hPath : path.val.length < 4096)
    (hLo : 1 ≤ e.val) (hHi : e.val ≤ 4095) :
    ops.add_ll_path { s with fdIsDirOracle := .err e :: rest } rs path 13#u64 =
      Result.ok (.Err e, { s with fdIsDirOracle := rest, closedFds := s.closedFds ++ [12#i32] }) := by
  have hOpen :
      init_sys.open_path_cloexec { s with fdIsDirOracle := .err e :: rest } path =
        Result.ok (.Ok 12#i32, { s with fdIsDirOracle := .err e :: rest }) := by
    unfold init_sys.open_path_cloexec; rw [if_false_eq (by omega)]
  unfold ops.add_ll_path
  rw [hOpen]
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  unfold init_sys.fd_is_dir init_sys.close_fd
  simp [sanitizeErrno_eq_of_bounds e hLo hHi]

/-- `ops.wait_for_go_byte` returns `false` and closes `go_fd` on immediate EOF (`read1Oracle = []`). -/
theorem wait_for_go_byte_eof (s : init_sys.Sys) (go_fd : I32) (hFd : 0 ≤ go_fd.val) :
    ops.wait_for_go_byte { s with read1Oracle := [] } go_fd =
      Result.ok (false, { s with read1Oracle := [], closedFds := s.closedFds ++ [go_fd] }) := by
  have hNotNeg : ¬ (go_fd.val < 0) := by omega
  have hStep :
      ops.wait_for_go_byte_loop.body go_fd { s with read1Oracle := [] } =
        Result.ok (done ({ s with read1Oracle := [] }, false)) := by
    unfold ops.wait_for_go_byte_loop.body init_sys.read1; simp [hNotNeg]
  unfold ops.wait_for_go_byte ops.wait_for_go_byte_loop
  rw [loop_done _ _ _ hStep, bind_ok]
  unfold init_sys.close_fd; simp [hNotNeg]

/-- `ops.wait_for_go_byte` returns `true` and closes `go_fd` when `read1` yields a release byte. -/
theorem wait_for_go_byte_released (s : init_sys.Sys) (go_fd : I32) (b : U8)
    (rest : List Read1Outcome) (hFd : 0 ≤ go_fd.val) :
    ops.wait_for_go_byte { s with read1Oracle := .byte b :: rest } go_fd =
      Result.ok (true, { s with read1Oracle := rest, closedFds := s.closedFds ++ [go_fd] }) := by
  have hNotNeg : ¬ (go_fd.val < 0) := by omega
  have hStep :
      ops.wait_for_go_byte_loop.body go_fd { s with read1Oracle := .byte b :: rest } =
        Result.ok (done ({ s with read1Oracle := rest }, true)) := by
    unfold ops.wait_for_go_byte_loop.body init_sys.read1; simp [hNotNeg]
  unfold ops.wait_for_go_byte ops.wait_for_go_byte_loop
  rw [loop_done _ _ _ hStep, bind_ok]
  unfold init_sys.close_fd; simp [hNotNeg]

/-- `ops.wait_for_go_byte` retries `EINTR` (`4`) and returns `true` on the subsequent release byte. -/
theorem wait_for_go_byte_eintr_retry_released (s : init_sys.Sys) (go_fd : I32) (b : U8)
    (rest : List Read1Outcome) (hFd : 0 ≤ go_fd.val) :
    ops.wait_for_go_byte { s with read1Oracle := .err 4#i32 :: .byte b :: rest } go_fd =
      Result.ok (true, { s with read1Oracle := rest, closedFds := s.closedFds ++ [go_fd] }) := by
  have hNotNeg : ¬ (go_fd.val < 0) := by omega
  have hStep1 :
      ops.wait_for_go_byte_loop.body go_fd
          { s with read1Oracle := .err 4#i32 :: .byte b :: rest } =
        Result.ok (cont { s with read1Oracle := .byte b :: rest }) := by
    unfold ops.wait_for_go_byte_loop.body init_sys.read1 ops.EINTR
    simp [hNotNeg, sanitizeErrno_eq_of_bounds 4#i32 (by decide) (by decide)]
  have hStep2 :
      ops.wait_for_go_byte_loop.body go_fd { s with read1Oracle := .byte b :: rest } =
        Result.ok (done ({ s with read1Oracle := rest }, true)) := by
    unfold ops.wait_for_go_byte_loop.body init_sys.read1; simp [hNotNeg]
  unfold ops.wait_for_go_byte ops.wait_for_go_byte_loop
  rw [loop_cont _ _ _ hStep1, loop_done _ _ _ hStep2, bind_ok]
  unfold init_sys.close_fd; simp [hNotNeg]

/-- `ops.wait_for_go_byte` returns `false` and closes `go_fd` on a non-`EINTR` `read1` error. -/
theorem wait_for_go_byte_err_closes_fd (s : init_sys.Sys) (go_fd e : I32)
    (rest : List Read1Outcome) (hFd : 0 ≤ go_fd.val)
    (hLo : 1 ≤ e.val) (hHi : e.val ≤ 4095) (hNe : e ≠ 4#i32) :
    ops.wait_for_go_byte { s with read1Oracle := .err e :: rest } go_fd =
      Result.ok (false, { s with read1Oracle := rest, closedFds := s.closedFds ++ [go_fd] }) := by
  have hNotNeg : ¬ (go_fd.val < 0) := by omega
  have hNeVal : e.val ≠ 4 := fun hv => hNe (IScalar.eq_of_val_eq hv)
  have hStep :
      ops.wait_for_go_byte_loop.body go_fd { s with read1Oracle := .err e :: rest } =
        Result.ok (done ({ s with read1Oracle := rest }, false)) := by
    unfold ops.wait_for_go_byte_loop.body init_sys.read1 ops.EINTR
    simp [hNotNeg, sanitizeErrno_eq_of_bounds e hLo hHi, hNeVal]
  unfold ops.wait_for_go_byte ops.wait_for_go_byte_loop
  rw [loop_done _ _ _ hStep, bind_ok]
  unfold init_sys.close_fd; simp [hNotNeg]

private theorem u32_max_ge_1024 : 1024 ≤ U32.max := by
  rw [U32.max_def, U32.numBits_def, UScalarTy.U32_numBits_eq]
  decide

/-- `ops.send_fds_scm` sends a 34-FD vector in two `SCM_RIGHTS` batches (`32` then `2`). -/
theorem send_fds_scm_ok_34 (s : init_sys.Sys) (ctrl_fd : I32) (fds : Array I32 1024#usize)
    (hFd : 0 ≤ ctrl_fd.val) :
    ops.send_fds_scm { s with scmSendOracle := [] } ctrl_fd fds 34#u32 =
      Result.ok (.Ok (),
        { s with
          scmSendOracle := []
          scmSentBatches :=
            s.scmSentBatches ++ [(ctrl_fd, 0#usize, 32#usize), (ctrl_fd, 32#usize, 2#usize)] }) := by
  have hNotNeg : ¬ (ctrl_fd.val < 0) := by omega
  have hCast0 : (UScalar.cast .Usize 0#u32 : Usize) = 0#usize := UScalar.eq_of_val_eq (by simp)
  have hCast2 : (UScalar.cast .Usize 2#u32 : Usize) = 2#usize := UScalar.eq_of_val_eq (by simp)
  have hCast32 : (UScalar.cast .Usize 32#u32 : Usize) = 32#usize := UScalar.eq_of_val_eq (by simp)
  let s0 : init_sys.Sys := { s with scmSendOracle := [] }
  let s1 : init_sys.Sys :=
    { s0 with scmSentBatches := s.scmSentBatches ++ [(ctrl_fd, 0#usize, 32#usize)] }
  let s2 : init_sys.Sys :=
    { s0 with
      scmSentBatches :=
        s.scmSentBatches ++ [(ctrl_fd, 0#usize, 32#usize), (ctrl_fd, 32#usize, 2#usize)] }
  have hBatch1 : init_sys.sendmsg_scm_batch s0 ctrl_fd fds 0#usize 32#usize =
      Result.ok (.Ok 1#usize, s1) := by
    unfold init_sys.sendmsg_scm_batch
    dsimp [s0, s1]
    simp [hNotNeg]
  have hBatch2 : init_sys.sendmsg_scm_batch s1 ctrl_fd fds 32#usize 2#usize =
      Result.ok (.Ok 1#usize, s2) := by
    unfold init_sys.sendmsg_scm_batch
    dsimp [s1, s2, s0]
    simp [hNotNeg, List.append_assoc]
  have hIn1 :
      ops.send_fds_scm_loop0_loop0 s0 ctrl_fd fds 0#u32 ops.EIO 32#u32 =
        Result.ok (s1, ops.EIO, true) := by
    unfold ops.send_fds_scm_loop0_loop0
    apply loop_done
    unfold ops.send_fds_scm_loop0_loop0.body
    dsimp only [lift]
    rw [hCast0, hCast32, bind_ok, bind_ok, hBatch1, bind_ok]
    simp
  have hIn2 :
      ops.send_fds_scm_loop0_loop0 s1 ctrl_fd fds 32#u32 ops.EIO 2#u32 =
        Result.ok (s2, ops.EIO, true) := by
    unfold ops.send_fds_scm_loop0_loop0
    apply loop_done
    unfold ops.send_fds_scm_loop0_loop0.body
    dsimp only [lift]
    rw [hCast32, hCast2, bind_ok, bind_ok, hBatch2, bind_ok]
    simp
  have hM := u32_max_ge_1024
  have hOut1 :
      ops.send_fds_scm_loop0.body ctrl_fd fds 34#u32 s0 0#u32 ops.EIO =
        Result.ok (cont (s1, 32#u32, ops.EIO)) := by
    unfold ops.send_fds_scm_loop0.body
    rw [if_true_eq (by decide : 0#u32 < 34#u32),
      u32_sub_ok_eq 34#u32 0#u32 34#u32 (by decide) (by decide), bind_ok,
      scm_batch_len_34_split.1, bind_ok, hIn1, bind_ok]
    simp [u32_add_ok_eq 0#u32 32#u32 32#u32 (by change 0 + 32 ≤ U32.max; omega) rfl]
  have hOut2 :
      ops.send_fds_scm_loop0.body ctrl_fd fds 34#u32 s1 32#u32 ops.EIO =
        Result.ok (cont (s2, 34#u32, ops.EIO)) := by
    unfold ops.send_fds_scm_loop0.body
    rw [if_true_eq (by decide : 32#u32 < 34#u32),
      u32_sub_ok_eq 34#u32 32#u32 2#u32 (by decide) (by decide), bind_ok,
      scm_batch_len_34_split.2, bind_ok, hIn2, bind_ok]
    simp [u32_add_ok_eq 32#u32 2#u32 34#u32 (by change 32 + 2 ≤ U32.max; omega) rfl]
  have hOut3 :
      ops.send_fds_scm_loop0.body ctrl_fd fds 34#u32 s2 34#u32 ops.EIO =
        Result.ok (done (s2, ops.EIO, false)) := by
    unfold ops.send_fds_scm_loop0.body
    rw [if_false_eq (by decide : ¬ (34#u32 < 34#u32))]
  unfold ops.send_fds_scm ops.send_fds_scm_loop0
  rw [loop_cont _ _ _ hOut1, loop_cont _ _ _ hOut2, loop_done _ _ _ hOut3, bind_ok]
  simp [s2, s0]

/-- `ops.send_fds_scm` retries `EINTR` (`4`) and succeeds on the next `Ok 1` send. -/
theorem send_fds_scm_eintr_retry_ok (s : init_sys.Sys) (ctrl_fd : I32)
    (fds : Array I32 1024#usize) (rest : List ScmSendOutcome) (hFd : 0 ≤ ctrl_fd.val) :
    ops.send_fds_scm
        { s with scmSendOracle := .err 4#i32 :: .ok 1#usize :: rest } ctrl_fd fds 2#u32 =
      Result.ok (.Ok (),
        { s with
          scmSendOracle := rest
          scmSentBatches := s.scmSentBatches ++ [(ctrl_fd, 0#usize, 2#usize)] }) := by
  have hNotNeg : ¬ (ctrl_fd.val < 0) := by omega
  have hCast0 : (UScalar.cast .Usize 0#u32 : Usize) = 0#usize := UScalar.eq_of_val_eq (by simp)
  have hCast2 : (UScalar.cast .Usize 2#u32 : Usize) = 2#usize := UScalar.eq_of_val_eq (by simp)
  let s0 : init_sys.Sys := { s with scmSendOracle := .err 4#i32 :: .ok 1#usize :: rest }
  let s1 : init_sys.Sys := { s with scmSendOracle := .ok 1#usize :: rest }
  let s2 : init_sys.Sys :=
    { s with scmSendOracle := rest, scmSentBatches := s.scmSentBatches ++ [(ctrl_fd, 0#usize, 2#usize)] }
  have hCall1 : init_sys.sendmsg_scm_batch s0 ctrl_fd fds 0#usize 2#usize =
      Result.ok (.Err 4#i32, s1) := by
    unfold init_sys.sendmsg_scm_batch
    rw [if_false_eq hNotNeg, if_false_eq (by simp)]
    simp [s0, s1, sanitizeErrno_eq_of_bounds 4#i32 (by decide) (by decide)]
  have hCall2 : init_sys.sendmsg_scm_batch s1 ctrl_fd fds 0#usize 2#usize =
      Result.ok (.Ok 1#usize, s2) := by
    unfold init_sys.sendmsg_scm_batch
    rw [if_false_eq hNotNeg, if_false_eq (by simp)]
    simp [s1, s2]
  have hIn1 :
      ops.send_fds_scm_loop0_loop0.body ctrl_fd fds 0#u32 ops.EIO 2#u32 s0 =
        Result.ok (cont s1) := by
    unfold ops.send_fds_scm_loop0_loop0.body
    dsimp only [lift]
    rw [hCast0, hCast2, bind_ok, bind_ok, hCall1, bind_ok]
    unfold ops.EINTR; simp
  have hIn2 :
      ops.send_fds_scm_loop0_loop0.body ctrl_fd fds 0#u32 ops.EIO 2#u32 s1 =
        Result.ok (done (s2, ops.EIO, true)) := by
    unfold ops.send_fds_scm_loop0_loop0.body
    dsimp only [lift]
    rw [hCast0, hCast2, bind_ok, bind_ok, hCall2, bind_ok]
    simp
  have hIn :
      ops.send_fds_scm_loop0_loop0 s0 ctrl_fd fds 0#u32 ops.EIO 2#u32 =
        Result.ok (s2, ops.EIO, true) := by
    unfold ops.send_fds_scm_loop0_loop0
    rw [loop_cont _ _ _ hIn1, loop_done _ _ _ hIn2]
  have hM := u32_max_ge_1024
  have hOut1 :
      ops.send_fds_scm_loop0.body ctrl_fd fds 2#u32 s0 0#u32 ops.EIO =
        Result.ok (cont (s2, 2#u32, ops.EIO)) := by
    unfold ops.send_fds_scm_loop0.body
    rw [if_true_eq (by decide : 0#u32 < 2#u32),
      u32_sub_ok_eq 2#u32 0#u32 2#u32 (by decide) (by decide), bind_ok,
      scm_batch_len_34_split.2, bind_ok, hIn, bind_ok]
    simp [u32_add_ok_eq 0#u32 2#u32 2#u32 (by change 0 + 2 ≤ U32.max; omega) rfl]
  have hOut2 :
      ops.send_fds_scm_loop0.body ctrl_fd fds 2#u32 s2 2#u32 ops.EIO =
        Result.ok (done (s2, ops.EIO, false)) := by
    unfold ops.send_fds_scm_loop0.body
    rw [if_false_eq (by decide : ¬ (2#u32 < 2#u32))]
  unfold ops.send_fds_scm ops.send_fds_scm_loop0
  rw [loop_cont _ _ _ hOut1, loop_done _ _ _ hOut2, bind_ok]
  simp [s2]

/-- `ops.send_fds_scm` returns `Err e` on non-`EINTR` `sendmsg_scm_batch` error without logging a batch. -/
theorem send_fds_scm_err (s : init_sys.Sys) (ctrl_fd e : I32) (fds : Array I32 1024#usize)
    (count : U32) (rest : List ScmSendOutcome)
    (hFd : 0 ≤ ctrl_fd.val) (hPos : 0 < count.val) (hLe : count.val ≤ 32)
    (hLo : 1 ≤ e.val) (hHi : e.val ≤ 4095) (hNe : e ≠ 4#i32) :
    ops.send_fds_scm { s with scmSendOracle := .err e :: rest } ctrl_fd fds count =
      Result.ok (.Err e, { s with scmSendOracle := rest }) := by
  have h0Le : (0#u32).val ≤ count.val := by change 0 ≤ count.val; omega
  have hLt : 0#u32 < count := by change 0 < count.val; omega
  have hSub : (count - 0#u32 : Result U32) = Result.ok count :=
    u32_sub_ok_eq count 0#u32 count h0Le (by change count.val = count.val - 0; omega)
  have hBatch : ops.scm_batch_len count = Result.ok count := by
    unfold ops.scm_batch_len ops.MAX_SCM_BATCH
    rw [if_false_eq (by change ¬ (32 < count.val); omega)]
  have hCall :
      init_sys.sendmsg_scm_batch { s with scmSendOracle := .err e :: rest }
        ctrl_fd fds (UScalar.cast .Usize 0#u32) (UScalar.cast .Usize count) =
        Result.ok (.Err e, { s with scmSendOracle := rest }) := by
    unfold init_sys.sendmsg_scm_batch
    rw [if_false_eq (by omega : ¬ (ctrl_fd.val < 0))]
    simp [sanitizeErrno_eq_of_bounds e hLo hHi]
    exact ⟨by omega, hLe, by omega⟩
  have hNeVal : e.val ≠ 4 := fun hv => hNe (IScalar.eq_of_val_eq hv)
  have hIn :
      ops.send_fds_scm_loop0_loop0 { s with scmSendOracle := .err e :: rest }
          ctrl_fd fds 0#u32 ops.EIO count =
        Result.ok ({ s with scmSendOracle := rest }, e, false) := by
    unfold ops.send_fds_scm_loop0_loop0
    apply loop_done
    unfold ops.send_fds_scm_loop0_loop0.body ops.EINTR
    dsimp only [lift]
    rw [bind_ok, bind_ok, hCall, bind_ok]
    simp [hNeVal]
  have hOut :
      ops.send_fds_scm_loop0.body ctrl_fd fds count
          { s with scmSendOracle := .err e :: rest } 0#u32 ops.EIO =
        Result.ok (done ({ s with scmSendOracle := rest }, e, true)) := by
    unfold ops.send_fds_scm_loop0.body
    rw [if_true_eq hLt, hSub, bind_ok, hBatch, bind_ok, hIn, bind_ok]
    simp
  unfold ops.send_fds_scm ops.send_fds_scm_loop0
  rw [loop_done _ _ _ hOut, bind_ok]
  simp

/-- `ops.send_fds_scm` maps a `0`-byte `sendmsg_scm_batch` return (`Ok 0`) to `Err EIO` (`5`). -/
theorem send_fds_scm_zero_sent_eio (s : init_sys.Sys) (ctrl_fd : I32)
    (fds : Array I32 1024#usize) (count : U32) (rest : List ScmSendOutcome)
    (hFd : 0 ≤ ctrl_fd.val) (hPos : 0 < count.val) (hLe : count.val ≤ 32) :
    ops.send_fds_scm { s with scmSendOracle := .ok 0#usize :: rest } ctrl_fd fds count =
      Result.ok (.Err 5#i32, { s with scmSendOracle := rest }) := by
  have h0Le : (0#u32).val ≤ count.val := by change 0 ≤ count.val; omega
  have hLt : 0#u32 < count := by change 0 < count.val; omega
  have hSub : (count - 0#u32 : Result U32) = Result.ok count :=
    u32_sub_ok_eq count 0#u32 count h0Le (by change count.val = count.val - 0; omega)
  have hBatch : ops.scm_batch_len count = Result.ok count := by
    unfold ops.scm_batch_len ops.MAX_SCM_BATCH
    rw [if_false_eq (by change ¬ (32 < count.val); omega)]
  have hCall :
      init_sys.sendmsg_scm_batch { s with scmSendOracle := .ok 0#usize :: rest }
        ctrl_fd fds (UScalar.cast .Usize 0#u32) (UScalar.cast .Usize count) =
        Result.ok (.Ok 0#usize, { s with scmSendOracle := rest }) := by
    unfold init_sys.sendmsg_scm_batch
    rw [if_false_eq (by omega : ¬ (ctrl_fd.val < 0))]
    simp
    exact ⟨by omega, hLe, by omega⟩
  have hIn :
      ops.send_fds_scm_loop0_loop0 { s with scmSendOracle := .ok 0#usize :: rest }
          ctrl_fd fds 0#u32 ops.EIO count =
        Result.ok ({ s with scmSendOracle := rest }, ops.EIO, false) := by
    unfold ops.send_fds_scm_loop0_loop0
    apply loop_done
    unfold ops.send_fds_scm_loop0_loop0.body
    dsimp only [lift]
    rw [bind_ok, bind_ok, hCall, bind_ok]
    simp
  have hOut :
      ops.send_fds_scm_loop0.body ctrl_fd fds count
          { s with scmSendOracle := .ok 0#usize :: rest } 0#u32 ops.EIO =
        Result.ok (done ({ s with scmSendOracle := rest }, ops.EIO, true)) := by
    unfold ops.send_fds_scm_loop0.body
    rw [if_true_eq hLt, hSub, bind_ok, hBatch, bind_ok, hIn, bind_ok]
    simp
  unfold ops.send_fds_scm ops.send_fds_scm_loop0
  rw [loop_done _ _ _ hOut, bind_ok]
  simp [ops.EIO]

/-- `ops.install_seccomp` uses `SYS_seccomp`, falls back to `prctl` on `ENOSYS` (`38`), and propagates other errors. -/
theorem install_seccomp_fallback_spec (s : init_sys.Sys) (data : Slice U8)
    (view : plan.PlanView) (hNPos : 0 < view.seccomp_n.val) (hNLe : view.seccomp_n.val ≤ 160)
    (hPos : view.seccomp_pos.val + view.seccomp_n.val * 8 ≤ data.val.length) :
    ops.install_seccomp { s with seccompErr? := none } data view =
      Result.ok (.Ok (),
        { s with
          seccompErr? := none
          seccompInstalled := s.seccompInstalled ++ [(.syscall, view.seccomp_n)] }) ∧
    ops.install_seccomp { s with seccompErr? := some 38#i32 } data view =
      Result.ok (.Ok (),
        { s with
          seccompErr? := some 38#i32
          seccompInstalled := s.seccompInstalled ++ [(.prctl, view.seccomp_n)] }) ∧
    ops.install_seccomp { s with seccompErr? := some 22#i32 } data view =
      Result.ok (.Err 22#i32, { s with seccompErr? := some 22#i32 }) := by
  have hMax : data.val.length ≤ Usize.max := data.property
  have hCastN : (UScalar.cast .Usize view.seccomp_n : Usize).val = view.seccomp_n.val := by simp
  obtain ⟨byteLen, hMul, hMulVal⟩ :=
    usize_mul_ok (UScalar.cast .Usize view.seccomp_n) 8#usize (by
      have h8 : (8#usize).val = 8 := rfl; rw [hCastN, h8]; omega)
  have hByteLen : byteLen.val = view.seccomp_n.val * 8 := by
    have h8 : (8#usize).val = 8 := rfl; rw [hMulVal, hCastN, h8]
  have hDataLen : (Slice.len data).val = data.val.length := by simp
  have hNotGtPos : ¬ (view.seccomp_pos > Slice.len data) := by
    change ¬ ((Slice.len data).val < view.seccomp_pos.val); omega
  obtain ⟨rem, hRem, hRemVal⟩ := usize_sub_ok (Slice.len data) view.seccomp_pos (by omega)
  have hNotGtLen : ¬ (byteLen > rem) := by
    change ¬ (rem.val < byteLen.val); omega
  obtain ⟨endPos, hEnd, hEndVal⟩ := usize_add_ok view.seccomp_pos byteLen (by omega)
  have hSlice :
      ∃ sl : Slice U8,
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice U8) data
          { start := view.seccomp_pos, «end» := endPos } = Result.ok sl ∧
        sl.val.length = view.seccomp_n.val * 8 := by
    change ∃ sl : Slice U8,
      core.slice.index.SliceIndexRangeUsizeSlice.index
        { start := view.seccomp_pos, «end» := endPos } data = Result.ok sl ∧ _
    rw [core.slice.index.SliceIndexRangeUsizeSlice.index]
    have hBound :
        ({ start := view.seccomp_pos, «end» := endPos } : core.ops.range.Range Usize).start ≤
          ({ start := view.seccomp_pos, «end» := endPos } : core.ops.range.Range Usize).end ∧
        ({ start := view.seccomp_pos, «end» := endPos } : core.ops.range.Range Usize).end.val ≤
          data.length :=
      ⟨by change view.seccomp_pos.val ≤ endPos.val; omega,
       by change endPos.val ≤ data.val.length; omega⟩
    rw [if_true_eq hBound]
    refine ⟨_, rfl, ?_⟩
    simp [List.slice]
    omega
  obtain ⟨sl, hSl, hSlLen⟩ := hSlice
  have hInvalidFalse : (view.seccomp_n.val == 0 || view.seccomp_n.val > 160 ||
      sl.val.length != view.seccomp_n.val * 8) = false := by
    rw [hSlLen]; simp; omega
  have hStep : ∀ err? : Option I32,
      ops.install_seccomp { s with seccompErr? := err? } data view =
        (do
          let (r, s1) ←
            init_sys.seccomp_set_mode_filter { s with seccompErr? := err? } sl view.seccomp_n
          match r with
          | core.result.Result.Ok _ => Result.ok (core.result.Result.Ok (), s1)
          | core.result.Result.Err e =>
            if e = ops.ENOSYS then init_sys.prctl_set_seccomp_filter s1 sl view.seccomp_n
            else Result.ok (r, s1)) := by
    intro err?
    unfold ops.install_seccomp
    dsimp only [lift]
    rw [bind_ok, hMul, bind_ok, if_false_eq hNotGtPos, hRem, bind_ok,
      if_false_eq hNotGtLen, hEnd, bind_ok, hSl, bind_ok]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hStep none]
    unfold init_sys.seccomp_set_mode_filter
    simp [hInvalidFalse]
  · rw [hStep (some 38#i32)]
    unfold init_sys.seccomp_set_mode_filter init_sys.prctl_set_seccomp_filter ops.ENOSYS
    simp [hInvalidFalse, sanitizeErrno_eq_of_bounds 38#i32 (by decide) (by decide)]
  · rw [hStep (some 22#i32)]
    unfold init_sys.seccomp_set_mode_filter ops.ENOSYS
    simp [hInvalidFalse, sanitizeErrno_eq_of_bounds 22#i32 (by decide) (by decide)]

end LeanSwe.ProcessSandbox.Init.Proofs
