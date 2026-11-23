import LeanSwe.PostFork.SpecTests
import LeanSwe.PostFork.Proofs.RunChildPre

/-!
# Unified `run_child` Post-Sync & Entrypoint Proofs

Kernel proofs for `postfork.child.prepare_rep_w`, `postfork.child.apply_redir_stdio`,
`postfork.child.apply_close_unkept`, `postfork.child.run_child_post_sync`, and
`postfork.child.run_child` (`RunChildSafetyPost`, `RunChildExecPost`, validation stages,
sync-barrier EOF `_exit(125)`, and `/proc/self/fd` fallback), discharging both
`RunChild` promises in `SpecTests.lean`.
-/

namespace LeanSwe.PostFork.Proofs

open _root_.Aeneas _root_.Aeneas.Std Result
open LeanSwe.PostFork
open LeanSwe.PostFork.World
open LeanSwe.PostFork.Aeneas
open LeanSwe.PostFork.Aeneas.Model

section TraceHelpers

private theorem okPost_to_dspec_rc {α : Type} {m : Result α} {P : α → Prop}
    (h : OkPost m P) : WP.dspec m P := by
  rcases h with ⟨v, hv, hp⟩
  rw [hv, WP.dspec_ok]
  exact hp

private theorem okPost_add_dspec_rc {α : Type} {m : Result α} {P Q : α → Prop}
    (hm : OkPost m P) (hd : WP.dspec m Q) : OkPost m (fun v => P v ∧ Q v) := by
  rcases hm with ⟨v, hv, hp⟩
  rw [hv, WP.dspec_ok] at hd
  exact ⟨v, hv, hp, hd⟩

private theorem dspec_loop_rel_rc {α β : Type} (inv : α → Prop) (post : α → β → Prop)
    (body : α → Result (ControlFlow α β))
    (hBody : ∀ a, inv a → WP.dspec (body a) fun r =>
      match r with
      | .done y => post a y
      | .cont a' => inv a' ∧ ∀ y, post a' y → post a y)
    (a : α) (ha : inv a) : WP.dspec (loop body a) (post a) := by
  suffices h : ∀ x : Subtype inv, WP.dspec (loop body x.1) (post x.1) from h ⟨a, ha⟩
  dspec_induction loop
  · intro _ ih ⟨x, hx⟩
    refine WP.dspec_bind (hBody x hx) fun r hr => ?_
    cases r with
    | done y => exact (WP.dspec_ok y).mpr hr
    | cont x' => exact WP.dspec_mono (ih ⟨x', hr.1⟩) (fun y hy => hr.2 y hy)

private theorem usize_add_ok_rc (a b : Usize) (h : a.val + b.val ≤ Usize.max) :
    ∃ z : Usize, a + b = Result.ok z ∧ z.val = a.val + b.val := by
  obtain ⟨z, hz, hval⟩ := (okPost_iff_wp_spec _ _).mpr (Usize.add_spec h)
  exact ⟨z, hz, by simpa using hval⟩

private theorem usize_sub_ok_rc (a b : Usize) (h : b.val ≤ a.val) :
    ∃ z : Usize, a - b = Result.ok z ∧ z.val = a.val - b.val := by
  obtain ⟨z, hz, hval⟩ := (okPost_iff_wp_spec _ _).mpr (Usize.sub_spec h)
  exact ⟨z, hz, by simpa using hval.1⟩

private theorem u32_add_ok_rc (a b : U32) (h : a.val + b.val ≤ U32.max) :
    ∃ z : U32, a + b = Result.ok z ∧ z.val = a.val + b.val := by
  obtain ⟨z, hz, hval⟩ := (okPost_iff_wp_spec _ _).mpr (U32.add_spec h)
  exact ⟨z, hz, by simpa using hval⟩

private theorem u32_sub_ok_rc (a b : U32) (h : b.val ≤ a.val) :
    ∃ z : U32, a - b = Result.ok z ∧ z.val = a.val - b.val := by
  obtain ⟨z, hz, hval⟩ := (okPost_iff_wp_spec _ _).mpr (U32.sub_spec h)
  exact ⟨z, hz, by simpa using hval.1⟩

private theorem array_index_usize_ok_rc {α : Type} {n : Usize} (a : Array α n) (i : Usize)
    (hi : i.val < a.val.length) :
    ∃ x, Array.index_usize a i = Result.ok x := by
  obtain ⟨x, hx, _⟩ := (okPost_iff_wp_spec _ _).mpr (Array.index_usize_spec a i hi)
  exact ⟨x, hx⟩

private theorem hcast_u32_ok_rc (x : I32) (hx : 0 ≤ x.val) :
    ∃ u : U32, lift (IScalar.hcast .U32 x) = Result.ok u ∧ u.val = x.val :=
  ⟨IScalar.hcast .U32 x, rfl, by scalar_tac⟩

private theorem runUnitSyscall_trace_rc (s : ChildState) (req : Req) (forcedErr? : Option I32)
    (onOk onErr : ChildState → ChildState)
    (hOkTr : (onOk s).trace = s.trace) (hErrTr : (onErr s).trace = s.trace) :
    OkPost (runUnitSyscall s req forcedErr? onOk onErr) fun p => TraceExtends s p.2 := by
  by_cases hs : s.status = Status.running
  · obtain ⟨r, s', hEq, hSpec⟩ := runUnitSyscall_running s hs req forcedErr? onOk onErr
    rw [hEq]
    cases hf : currentFault s with
    | seccomp rawE =>
      simp only [hf] at hSpec; rcases hSpec with ⟨_, rfl⟩
      exact okPost_ok _ _ ⟨_, rfl⟩
    | fail rawE =>
      simp only [hf] at hSpec
      cases forcedErr? <;>
        (simp only at hSpec; rcases hSpec with ⟨_, rfl⟩; exact okPost_ok _ _ ⟨_, congrArg (· ++ _) hErrTr⟩)
    | normal | partialWrite _ | dentsBatch _ =>
      simp only [hf] at hSpec
      cases forcedErr? with
      | some e =>
        simp only at hSpec; rcases hSpec with ⟨_, rfl⟩
        exact okPost_ok _ _ ⟨_, congrArg (· ++ _) hErrTr⟩
      | none =>
        simp only at hSpec; rcases hSpec with ⟨_, rfl⟩
        exact okPost_ok _ _ ⟨_, congrArg (· ++ _) hOkTr⟩
  · rw [runUnitSyscall_not_running s hs]; exact okPost_ok _ _ (traceExtends_refl s)

private theorem runI32Syscall_trace_rc (s : ChildState) (req : Req) (forcedErr? : Option I32)
    (onOk : ChildState → I32 × ChildState) (hOkTr : (onOk s).2.trace = s.trace) :
    OkPost (runI32Syscall s req forcedErr? onOk) fun p => TraceExtends s p.2 := by
  by_cases hs : s.status = Status.running
  · obtain ⟨r, s', hEq, hSpec⟩ := runI32Syscall_running s hs req forcedErr? onOk
    rw [hEq]
    cases hf : currentFault s with
    | seccomp rawE =>
      simp only [hf] at hSpec; rcases hSpec with ⟨_, rfl⟩
      exact okPost_ok _ _ ⟨_, rfl⟩
    | fail rawE =>
      simp only [hf] at hSpec
      cases forcedErr? <;> (simp only at hSpec; rcases hSpec with ⟨_, rfl⟩; exact okPost_ok _ _ ⟨_, rfl⟩)
    | normal | partialWrite _ | dentsBatch _ =>
      simp only [hf] at hSpec
      cases forcedErr? with
      | some e => simp only at hSpec; rcases hSpec with ⟨_, rfl⟩; exact okPost_ok _ _ ⟨_, rfl⟩
      | none =>
        simp only at hSpec; rcases hSpec with ⟨_, rfl⟩
        exact okPost_ok _ _ ⟨_, congrArg (· ++ _) hOkTr⟩
  · rw [runI32Syscall_not_running s hs]; exact okPost_ok _ _ (traceExtends_refl s)

private theorem sys_fcntl_setfd_trace_rc (s : ChildState) (fd flags : I32) :
    OkPost (sys.fcntl_setfd s fd flags) fun p => TraceExtends s p.2 := by
  unfold sys.fcntl_setfd
  apply runUnitSyscall_trace_rc
  · cases s.getFd ↑fd <;> simp [ChildState.putSlot]
  · rfl

private theorem set_cloexec_trace_rc (s : ChildState) (fd : I32) :
    OkPost (postfork.fd_ops.set_cloexec s fd) fun p => TraceExtends s p.2 := by
  unfold postfork.fd_ops.set_cloexec
  refine okPost_bind (sys_fcntl_getfd_trace s fd) fun p1 h1 => ?_
  rcases p1 with ⟨r1, s1⟩
  dsimp only at h1
  cases r1 with
  | Err _ => exact okPost_ok _ _ h1
  | Ok _ =>
    refine okPost_bind (okPost_lift _ (fun _ => True) trivial) fun newFl _ =>
      okPost_mono (sys_fcntl_setfd_trace_rc s1 fd newFl) (fun _ h2 => traceExtends_trans h1 h2)

private theorem relocate_rep_above2_trace_rc (s : ChildState) (repW : I32) :
    OkPost (postfork.fd_ops.relocate_rep_above2 s repW) fun p => TraceExtends s p.2 := by
  unfold postfork.fd_ops.relocate_rep_above2
  by_cases hneg : repW < 0#i32
  · simp only [hneg, ↓reduceIte]
    exact okPost_ok _ _ (traceExtends_refl s)
  · simp only [hneg, ↓reduceIte]
    by_cases hle : repW ≤ 2#i32
    · simp only [hle, ↓reduceIte]
      refine okPost_bind (sys_fcntl_dupfd_cloexec_trace s repW 3#i32) fun p1 h1 => ?_
      rcases p1 with ⟨r, s1⟩
      dsimp only at h1
      cases r with
      | Err _ => exact okPost_ok _ _ h1
      | Ok _ =>
        refine okPost_bind (sys_close_trace s1 repW) fun p2 h2 => ?_
        exact okPost_ok _ _ (traceExtends_trans h1 h2)
    · simp only [hle, ↓reduceIte]
      refine okPost_bind (set_cloexec_trace_rc s repW) fun p1 h1 => ?_
      rcases p1 with ⟨r, s1⟩
      dsimp only at h1
      cases r <;> exact okPost_ok _ _ h1

private theorem prepare_rep_w_trace (s : ChildState) (redir : Bool) (repW : I32) :
    OkPost (postfork.child.prepare_rep_w s redir repW) fun p => TraceExtends s p.2 := by
  unfold postfork.child.prepare_rep_w
  cases redir
  · refine okPost_bind (set_cloexec_trace_rc s repW) fun p1 h1 => ?_
    rcases p1 with ⟨r, s1⟩
    dsimp only at h1
    cases r <;> exact okPost_ok _ _ h1
  · exact relocate_rep_above2_trace_rc s repW

private theorem apply_redir_stdio_trace (s : ChildState) (redir : Bool)
    (inFd outFd errFd : I32) (closeSrcs : Bool) :
    OkPost (postfork.child.apply_redir_stdio s redir inFd outFd errFd closeSrcs) fun p =>
      TraceExtends s p.2 := by
  unfold postfork.child.apply_redir_stdio
  cases redir
  · exact okPost_ok _ _ (traceExtends_refl s)
  · exact setup_stdio_trace s inFd outFd errFd closeSrcs

private theorem clear_cloexec_slice_trace_rc (s : ChildState) (hRun : s.status = .running) (fds : Slice I32) :
    OkPost (postfork.fd_ops.clear_cloexec_slice s fds) fun p => TraceExtends s p.2 := by
  refine okPost_mono (okPost_add_dspec_rc (clear_cloexec_slice_safety s hRun fds) ?_) (fun _ h => h.2)
  unfold postfork.fd_ops.clear_cloexec_slice postfork.fd_ops.clear_cloexec_slice_loop
  refine WP.dspec_bind (dspec_loop_rel_rc (fun p => p.2.val ≤ fds.val.length)
      (fun a res => TraceExtends a.1 res.1) _ ?_ (s, 0#usize) (Nat.zero_le _)) fun res hres => ?_
  · intro ⟨s1, j⟩ hjLe
    dsimp only at hjLe
    unfold postfork.fd_ops.clear_cloexec_slice_loop.body
    by_cases hlt : j < fds.len
    · have hjlt : j.val < fds.val.length := hlt
      have hidx : Slice.index_usize fds j = Result.ok fds.val[j.val] := by
        simp [Slice.index_usize, List.getElem?_eq_getElem hjlt]
      have hinc : ∃ z : Usize, j + 1#usize = Result.ok z ∧ z.val = j.val + 1 := by
        have hlen := fds.property
        exact usize_add_ok_rc j 1#usize (by change j.val + 1 ≤ Usize.max; omega)
      rcases hinc with ⟨z, hz, hzVal⟩
      simp only [hlt, ↓reduceIte, hidx, bind_ok]
      by_cases hnonneg : fds.val[j.val] ≥ 0#i32
      · simp only [hnonneg, ↓reduceIte]
        refine WP.dspec_bind (okPost_to_dspec_rc (clear_cloexec_trace s1 fds.val[j.val])) fun p2 hp2 => ?_
        rcases p2 with ⟨r, s2⟩
        dsimp only at hp2
        cases r with
        | Err _ => exact (WP.dspec_ok _).mpr hp2
        | Ok _ =>
          simp only [hz, bind_ok]
          exact (WP.dspec_ok _).mpr ⟨by simp [hzVal]; omega, fun res hres => traceExtends_trans hp2 hres⟩
      · simp only [hnonneg, ↓reduceIte]
        rw [hz, bind_ok]
        exact (WP.dspec_ok _).mpr ⟨by simp [hzVal]; omega, fun res hres => hres⟩
    · simp only [hlt, ↓reduceIte]
      exact (WP.dspec_ok _).mpr (traceExtends_refl s1)
  · rcases res with ⟨s1, _, failed⟩
    cases failed <;> exact (WP.dspec_ok _).mpr hres

private theorem sys_close_range_trace_rc (s : ChildState) (first last flags : U32) :
    OkPost (sys.close_range s first last flags) fun p => TraceExtends s p.2 := by
  unfold sys.close_range
  exact runUnitSyscall_trace_rc s _ _ _ _ (by split <;> rfl) rfl

private theorem sys_open_proc_self_fd_trace_rc (s : ChildState) :
    OkPost (sys.open_proc_self_fd s) fun p => TraceExtends s p.2 := by
  unfold sys.open_proc_self_fd
  cases findLowestFreeFd s 0 with
  | none => exact runI32Syscall_trace_rc s _ _ _ rfl
  | some dirfd =>
    dsimp only
    by_cases hAv : (!s.procSelfFdAvailable) = true
    · simp only [hAv, ↓reduceIte]
      exact runI32Syscall_trace_rc s _ _ _ rfl
    · simp only [hAv, Bool.false_eq_true, ↓reduceIte]
      apply runI32Syscall_trace_rc
      simp [ChildState.putDesc, ChildState.putSlot]

private theorem sys_getdents64_trace_rc (s : ChildState) (dirfd : I32) (buf : Array U8 256#usize) :
    OkPost (sys.getdents64 s dirfd buf) fun p => TraceExtends s p.2.1 := by
  unfold sys.getdents64
  cases hs : s.status with
  | running =>
    dsimp only
    cases hcf : currentFault s with
    | seccomp _ => exact okPost_ok _ _ ⟨_, rfl⟩
    | fail _ =>
      dsimp only
      cases s.getFd dirfd.val with
      | none => exact okPost_ok _ _ ⟨_, rfl⟩
      | some e =>
        dsimp only
        cases s.getDesc e.desc with
        | stream _ _ _ _ | directory _ => exact okPost_ok _ _ ⟨_, rfl⟩
        | procSelfFd _ => dsimp only; exact okPost_ok _ _ ⟨_, rfl⟩
    | normal | partialWrite _ | dentsBatch _ =>
      dsimp only
      cases s.getFd dirfd.val with
      | none => exact okPost_ok _ _ ⟨_, rfl⟩
      | some e =>
        dsimp only
        cases s.getDesc e.desc with
        | stream _ _ _ _ => exact okPost_ok _ _ ⟨_, rfl⟩
        | directory _ => dsimp only; split <;> exact okPost_ok _ _ ⟨_, rfl⟩
        | procSelfFd _ => dsimp only; split <;> exact okPost_ok _ _ ⟨_, rfl⟩
  | exited _ | signaled _ | execd _ =>
    exact okPost_ok _ _ (traceExtends_refl s)

private theorem next_keep_ge_bound_rc (extra_keep_fd : I32) (keep_fds : Slice I32) (lo : U32) :
    OkPost (postfork.fd_ops.next_keep_ge extra_keep_fd keep_fds lo) fun o =>
      ∀ k : U32, o = some k → lo.val ≤ k.val ∧ k.val ≤ 2147483647 := by
  unfold postfork.fd_ops.next_keep_ge postfork.fd_ops.next_keep_ge_loop
  refine okPost_bind (P := fun b => ∀ k : U32, b = some k → lo.val ≤ k.val ∧ k.val ≤ 2147483647) ?_ fun best hBest => ?_
  · split
    · rcases hcast_u32_ok_rc extra_keep_fd (by scalar_tac) with ⟨u, hu, _⟩
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
        exact usize_add_ok_rc j 1#usize (by change j.val + 1 ≤ Usize.max; omega)
      rcases hinc with ⟨z, hz, hzVal⟩
      simp only [hlt, ↓reduceIte, hidx, bind_ok]
      refine okPost_bind (P := fun b' => ∀ k : U32, b' = some k → lo.val ≤ k.val ∧ k.val ≤ 2147483647) ?_
        fun b' hb' => ?_
      · split
        · rcases hcast_u32_ok_rc keep_fds.val[j.val] (by scalar_tac) with ⟨u, hu, _⟩
          rw [hu, bind_ok]
          split
          · cases b with
            | none =>
              dsimp only; simp only [bind_ok]
              apply okPost_ok; intro k hk; cases hk; exact ⟨by scalar_tac, by scalar_tac⟩
            | some cur =>
              dsimp only
              split
              · simp only [bind_ok]
                apply okPost_ok; intro k hk; cases hk; exact ⟨by scalar_tac, by scalar_tac⟩
              · simp only [bind_ok]; apply okPost_ok; exact hbBound
          · apply okPost_ok; exact hbBound
        · apply okPost_ok; exact hbBound
      · rw [hz, bind_ok]
        exact okPost_ok _ _ ⟨⟨by simp [hzVal]; omega, hb'⟩, by
          change keep_fds.len.val - z.val < keep_fds.len.val - j.val
          rw [hzVal]; exact Nat.sub_succ_lt_self _ _ hjlt⟩
    · simp only [hlt, ↓reduceIte]
      exact okPost_ok _ _ hbBound

private theorem close_dirent_batch_trace_rc (s : ChildState) (buf : Array U8 256#usize)
    (n : Usize) (dirfd extra_keep_fd : I32) (keep_fds : Slice I32) :
    WP.dspec (postfork.fd_ops.close_dirent_batch s buf n dirfd extra_keep_fd keep_fds)
      fun p => TraceExtends s p.2 := by
  unfold postfork.fd_ops.close_dirent_batch
  by_cases hn : n > 256#usize
  · simp only [hn, ↓reduceIte]
    exact (WP.dspec_ok _).mpr (traceExtends_refl s)
  · have hnLe : n.val ≤ 256 := by scalar_tac
    simp only [hn, ↓reduceIte]
    unfold postfork.fd_ops.close_dirent_batch_loop
    refine WP.dspec_bind (dspec_loop_rel_rc (fun p => p.2.val ≤ 256)
        (fun a res => TraceExtends a.1 res.1) _ ?_ (s, 0#usize) (Nat.zero_le _))
      fun res hres => ?_
    · intro ⟨s1, pos⟩ hPosLe
      dsimp only at hPosLe
      unfold postfork.fd_ops.close_dirent_batch_loop.body
      by_cases hlt : pos < n
      · have hposLtN : pos.val < n.val := hlt
        rcases usize_sub_ok_rc n pos (by omega) with ⟨diff, hdiff, _⟩
        simp only [hlt, ↓reduceIte, hdiff, bind_ok]
        by_cases hdiffLt : diff < 20#usize
        · simp only [hdiffLt, ↓reduceIte]
          exact (WP.dspec_ok _).mpr (traceExtends_refl s1)
        · simp only [hdiffLt, ↓reduceIte]
          by_cases hPosGt : pos > 236#usize
          · simp only [hPosGt, ↓reduceIte]
            exact (WP.dspec_ok _).mpr (traceExtends_refl s1)
          · simp only [hPosGt, ↓reduceIte]
            have hPos236 : pos.val ≤ 236 := by scalar_tac
            have hmax : 4294967295 ≤ Usize.max := by
              have h1 := Usize.cMax_bound.1
              have h2 : UScalar.cMax UScalarTy.Usize = 4294967295 := by decide
              omega
            have hblen : buf.val.length = 256 := buf.property
            rcases usize_add_ok_rc pos 16#usize (by change pos.val + 16 ≤ Usize.max; omega) with ⟨u1, hu1, hu1Val⟩
            rcases array_index_usize_ok_rc buf u1 (by rw [hu1Val, hblen]; scalar_tac) with ⟨loByte, hloByte⟩
            rcases usize_add_ok_rc pos 17#usize (by change pos.val + 17 ≤ Usize.max; omega) with ⟨u3, hu3, hu3Val⟩
            rcases array_index_usize_ok_rc buf u3 (by rw [hu3Val, hblen]; scalar_tac) with ⟨hiByte, hhiByte⟩
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
            refine WP.dspec_bind (okPost_to_dspec_rc (okPost_lift _ _ rfl)) fun reclen _ => ?_
            by_cases hrLt : reclen < 20#usize
            · simp only [hrLt, ↓reduceIte]
              exact (WP.dspec_ok _).mpr (traceExtends_refl s1)
            · simp only [hrLt, ↓reduceIte]
              by_cases hrGt : reclen > diff
              · simp only [hrGt, ↓reduceIte]
                exact (WP.dspec_ok _).mpr (traceExtends_refl s1)
              · simp only [hrGt, ↓reduceIte]
                have hrLe : reclen.val ≤ diff.val := by scalar_tac
                rcases usize_add_ok_rc pos 19#usize (by change pos.val + 19 ≤ Usize.max; omega) with ⟨u6, hu6, _⟩
                rcases usize_add_ok_rc pos reclen (by omega) with ⟨u7, hu7, hu7Val⟩
                rw [hu6, bind_ok, hu7, bind_ok, parse_dirent_name_eq_expected buf u6 u7, bind_ok]
                set parsed := expectedDirentParse buf u6 u7
                by_cases hpMal : parsed = postfork.fd_ops.DIRENT_MALFORMED
                · simp only [hpMal, ↓reduceIte]
                  exact (WP.dspec_ok _).mpr (traceExtends_refl s1)
                · simp only [hpMal, ↓reduceIte]
                  have hu7Le : u7.val ≤ 256 := by rw [hu7Val]; omega
                  by_cases h1 : parsed > 2#i32
                  · simp only [h1, ↓reduceIte]
                    by_cases h2 : (parsed != dirfd) = true
                    · simp only [h2, ↓reduceIte]
                      by_cases h3 : (parsed != extra_keep_fd) = true
                      · simp only [h3, ↓reduceIte]
                        refine WP.dspec_bind (okPost_to_dspec_rc (slice_contains_nonneg_total keep_fds parsed))
                          fun b _ => ?_
                        cases b with
                        | true =>
                          simp only [↓reduceIte]
                          exact (WP.dspec_ok _).mpr ⟨hu7Le, fun res hres => hres⟩
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          refine WP.dspec_bind (okPost_to_dspec_rc (sys_close_trace s1 parsed)) fun q hq => ?_
                          rcases q with ⟨rClose, s2⟩
                          dsimp only at hq
                          cases rClose with
                          | Ok _ => exact (WP.dspec_ok _).mpr ⟨hu7Le, fun res hres => traceExtends_trans hq hres⟩
                          | Err _ => exact (WP.dspec_ok _).mpr hq
                      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
                        exact (WP.dspec_ok _).mpr ⟨hu7Le, fun res hres => hres⟩
                    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
                      exact (WP.dspec_ok _).mpr ⟨hu7Le, fun res hres => hres⟩
                  · simp only [h1, ↓reduceIte]
                    exact (WP.dspec_ok _).mpr ⟨hu7Le, fun res hres => hres⟩
      · simp only [hlt, ↓reduceIte]
        exact (WP.dspec_ok _).mpr (traceExtends_refl s1)
    · rcases res with ⟨s1, err, bad⟩
      cases bad with
      | true => exact (WP.dspec_ok _).mpr hres
      | false => exact (WP.dspec_ok _).mpr hres

private theorem close_via_proc_self_fd_trace_rc (s : ChildState) (extra_keep_fd : I32) (keep_fds : Slice I32) :
    WP.dspec (postfork.fd_ops.close_via_proc_self_fd s extra_keep_fd keep_fds) fun p => TraceExtends s p.2 := by
  unfold postfork.fd_ops.close_via_proc_self_fd
  refine WP.dspec_bind (okPost_to_dspec_rc (sys_open_proc_self_fd_trace_rc s)) fun p1 h1 => ?_
  rcases p1 with ⟨r1, s1⟩
  dsimp only at h1
  cases r1 with
  | Err _ => exact (WP.dspec_ok _).mpr h1
  | Ok dirfd =>
    unfold postfork.fd_ops.close_via_proc_self_fd_loop
    refine WP.dspec_bind (dspec_loop_rel_rc (fun _ => True) (fun a res => TraceExtends a res.1) _ ?_ s1 trivial)
      fun pLoop hLoop => ?_
    · intro sCur _
      unfold postfork.fd_ops.close_via_proc_self_fd_loop.body
      refine WP.dspec_bind (okPost_to_dspec_rc (sys_getdents64_trace_rc sCur dirfd (Array.repeat 256#usize 0#u8)))
        fun pGd hGd => ?_
      rcases pGd with ⟨rGd, sGd, bufGd⟩
      have hsGd : TraceExtends sCur sGd := hGd
      cases rGd with
      | Err e =>
        change WP.dspec (if (e != postfork.fd_ops.EINTR) = true then ok (ControlFlow.done (sGd, e, true))
          else ok (ControlFlow.cont sGd)) _
        by_cases hne : (e != postfork.fd_ops.EINTR) = true
        · simp only [hne, ↓reduceIte]
          exact (WP.dspec_ok _).mpr hsGd
        · simp only [hne]
          exact (WP.dspec_ok _).mpr ⟨trivial, fun res hres => traceExtends_trans hsGd hres⟩
      | Ok n =>
        change WP.dspec (match n.val with
          | 0 => ok (ControlFlow.done (sGd, 0#i32, false))
          | _ => do
            let (r1, s2) ← postfork.fd_ops.close_dirent_batch sGd bufGd n dirfd extra_keep_fd keep_fds
            match r1 with
            | core.result.Result.Ok _ => ok (ControlFlow.cont s2)
            | core.result.Result.Err e => ok (ControlFlow.done (s2, e, true))) _
        cases hnVal : n.val with
        | zero => exact (WP.dspec_ok _).mpr hsGd
        | succ _ =>
          refine WP.dspec_bind (close_dirent_batch_trace_rc sGd bufGd n dirfd extra_keep_fd keep_fds)
            fun pBat hBat => ?_
          rcases pBat with ⟨rBat, _⟩
          dsimp only at hBat
          cases rBat with
          | Err _ => exact (WP.dspec_ok _).mpr (traceExtends_trans hsGd hBat)
          | Ok _ => exact (WP.dspec_ok _).mpr ⟨trivial, fun res hres => traceExtends_trans (traceExtends_trans hsGd hBat) hres⟩
    · rcases pLoop with ⟨s2, err, failed⟩
      refine WP.dspec_bind (okPost_to_dspec_rc (sys_close_trace s2 dirfd)) fun pCl hCl => ?_
      rcases pCl with ⟨rCl, s3⟩
      dsimp only at hCl
      have hTr : TraceExtends s s3 := traceExtends_trans h1 (traceExtends_trans hLoop hCl)
      cases rCl with
      | Ok _ =>
        change WP.dspec (do
          let (s4, err1, failed1) ← Result.ok (s3, err, failed)
          if failed1 = true then Result.ok (core.result.Result.Err err1, s4)
          else Result.ok (core.result.Result.Ok (), s4)) _
        rw [bind_ok]
        cases failed <;> exact (WP.dspec_ok _).mpr hTr
      | Err ce =>
        change WP.dspec (do
          let (s4, err1, failed1) ← (do
            let (i, b) ← if failed = true then Result.ok (err, failed) else Result.ok (ce, true)
            Result.ok (s3, i, b))
          if failed1 = true then Result.ok (core.result.Result.Err err1, s4)
          else Result.ok (core.result.Result.Ok (), s4)) _
        cases failed <;> simp only [↓reduceIte, Bool.false_eq_true, bind_ok] <;>
          (erw [bind_ok]; exact (WP.dspec_ok _).mpr hTr)

private theorem close_fds_above2_except_trace_rc (s : ChildState) (extra_keep_fd : I32)
    (keep_fds : Slice I32) (hRun : s.status = .running) :
    OkPost (postfork.fd_ops.close_fds_above2_except s extra_keep_fd keep_fds) fun p => TraceExtends s p.2 := by
  refine okPost_mono (okPost_add_dspec_rc (close_fds_above2_except_safety s extra_keep_fd keep_fds hRun) ?_)
    (fun _ h => h.2)
  have hTry : WP.dspec (postfork.fd_ops.try_close_range_except s extra_keep_fd keep_fds)
      fun p1 => TraceExtends s p1.2 := by
    unfold postfork.fd_ops.try_close_range_except postfork.fd_ops.try_close_range_except_loop
    refine WP.dspec_bind (dspec_loop_rel_rc (fun _ => True) (fun a res => TraceExtends a.2 res.1) _ ?_
        (3#u32, s) trivial) fun res1 hres1 => ?_
    · intro ⟨lo, s1⟩ _
      dsimp only
      unfold postfork.fd_ops.try_close_range_except_loop.body
      refine WP.dspec_bind (okPost_to_dspec_rc (next_keep_ge_bound_rc extra_keep_fd keep_fds lo))
        fun o hoBound => ?_
      cases o with
      | none =>
        refine WP.dspec_bind (okPost_to_dspec_rc (sys_close_range_trace_rc s1 lo core.num.U32.MAX 0#u32))
          fun p2 hp2 => ?_
        rcases p2 with ⟨r, _⟩
        dsimp only at hp2
        cases r <;> exact (WP.dspec_ok _).mpr hp2
      | some k =>
        rcases hoBound k rfl with ⟨hLoLe, hkMax⟩
        have hkAdd : ∃ lo1 : U32, k + 1#u32 = Result.ok lo1 := by
          have : k.val + 1 ≤ U32.max := by scalar_tac
          obtain ⟨lo1, hlo1, _⟩ := u32_add_ok_rc k 1#u32 (by change k.val + 1 ≤ U32.max; omega)
          exact ⟨lo1, hlo1⟩
        rcases hkAdd with ⟨lo1, hlo1⟩
        by_cases hkGt : k > lo
        · simp only [hkGt, ↓reduceIte]
          have hiSub : ∃ i : U32, k - 1#u32 = Result.ok i := by
            have hkPos : 1 ≤ k.val := by scalar_tac
            obtain ⟨i, hi, _⟩ := u32_sub_ok_rc k 1#u32 (by change 1 ≤ k.val; omega)
            exact ⟨i, hi⟩
          rcases hiSub with ⟨i, hi⟩
          rw [hi, bind_ok]
          refine WP.dspec_bind (okPost_to_dspec_rc (sys_close_range_trace_rc s1 lo i 0#u32)) fun p2 hp2 => ?_
          rcases p2 with ⟨r, _⟩
          dsimp only at hp2
          cases r with
          | Err _ => exact (WP.dspec_ok _).mpr hp2
          | Ok _ =>
            simp only [hlo1, bind_ok]
            exact (WP.dspec_ok _).mpr ⟨trivial, fun res hres => traceExtends_trans hp2 hres⟩
        · simp only [hkGt, ↓reduceIte]
          simp only [hlo1, bind_ok]
          exact (WP.dspec_ok _).mpr ⟨trivial, fun res hres => hres⟩
    · rcases res1 with ⟨_, _, failed⟩
      dsimp only at hres1
      cases failed <;> exact (WP.dspec_ok _).mpr hres1
  unfold postfork.fd_ops.close_fds_above2_except
  refine WP.dspec_bind hTry fun pOut hpOut => ?_
  rcases pOut with ⟨rOut, s1⟩
  dsimp only at hpOut
  cases rOut with
  | Ok _ => exact (WP.dspec_ok _).mpr hpOut
  | Err _ =>
    exact WP.dspec_mono (close_via_proc_self_fd_trace_rc s1 extra_keep_fd keep_fds)
      (fun _ h2 => traceExtends_trans hpOut h2)

private theorem apply_close_unkept_trace (s : ChildState) (closeUnkept : Bool) (safeRepW : I32)
    (keepFds : Slice I32) (hRun : s.status = .running) :
    OkPost (postfork.child.apply_close_unkept s closeUnkept safeRepW keepFds) fun p =>
      TraceExtends s p.2 := by
  unfold postfork.child.apply_close_unkept
  cases closeUnkept
  · exact okPost_ok _ _ (traceExtends_refl s)
  · exact close_fds_above2_except_trace_rc s safeRepW keepFds hRun

private theorem sys_chdir_trace_eq (s : ChildState) (hRun : s.status = .running) (path : sys.CStr)
    {r : core.result.Result Unit I32} {s' : ChildState} (hEq : sys.chdir s path = ok (r, s')) :
    TraceExtends s s' := by
  unfold sys.chdir runUnitSyscall at hEq
  rw [hRun] at hEq
  dsimp only [id] at hEq
  cases hf : currentFault s with
  | seccomp _ =>
    simp only [hf, Result.ok.injEq, Prod.mk.injEq] at hEq
    obtain ⟨_, rfl⟩ := hEq; exact ⟨_, rfl⟩
  | fail _ =>
    simp only [hf] at hEq
    cases hemp : path.isEmpty
    · simp only [hemp, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at hEq
      rw [← hEq.2]; exact ⟨_, rfl⟩
    · simp only [hemp, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at hEq
      rw [← hEq.2]; exact ⟨_, rfl⟩
  | normal | partialWrite _ | dentsBatch _ =>
    simp only [hf] at hEq
    cases hemp : path.isEmpty
    · simp only [hemp, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at hEq
      rw [← hEq.2]; exact ⟨_, rfl⟩
    · simp only [hemp, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at hEq
      rw [← hEq.2]; exact ⟨_, rfl⟩

end TraceHelpers

section StepWrappers

private theorem prepare_rep_w_safety
    (s : ChildState) (hRun : s.status = .running) (redir : Bool) (repW : I32) :
    OkPost (postfork.child.prepare_rep_w s redir repW) fun (r, s1) =>
      s1.status = .running ∧ SameChildConfig s1 s ∧
      s1.pgid = s.pgid ∧ s1.cwd = s.cwd ∧ s1.sig = s.sig ∧
      s1.descs = s.descs ∧ s1.writeLog = s.writeLog ∧
      s1.fds.length ≤ s.fds.length + 1 ∧
      TraceExtends s s1 ∧
      (∀ fd, r = .Ok fd →
        (redir = true → 2 < fd.val ∧
          (repW.val ≤ 2 → fd.val ≠ repW.val ∧ (oracleHasSeccomp s.oracle = false → s1.getFd repW.val = none) ∧ s.getFd fd.val = none) ∧
          (2 < repW.val → fd = repW)) ∧
        (redir = false → fd = repW) ∧
        (∃ e f, s.getFd repW.val = some e ∧ s1.getFd fd.val = some f ∧
          f.desc = e.desc ∧ f.cloexec = true) ∧
        (∀ k, k ≠ repW.val → k ≠ fd.val → s1.getFd k = s.getFd k)) := by
  unfold postfork.child.prepare_rep_w
  cases redir
  · dsimp only
    refine okPost_bind (okPost_and (set_cloexec_safety s hRun repW) (set_cloexec_trace_rc s repW))
      fun (r0, s1) ⟨⟨hRun1, hCfg1, hPg1, hCw1, hSig1, hDe1, hWl1, hLen1, hOk1⟩, hTr1⟩ => ?_
    cases r0 with
    | Err e =>
      exact ⟨(.Err e, s1), rfl, hRun1, hCfg1, hPg1, hCw1, hSig1, hDe1, hWl1, hLen1, hTr1,
        fun _ h => by cases h⟩
    | Ok u =>
      have hCl := hOk1 (by cases u; rfl)
      cases hsGet : s.getFd repW.val with
      | none => simp [CloexecTogglePost, hsGet] at hCl
      | some e =>
        simp only [CloexecTogglePost, hsGet, true_and] at hCl
        exact ⟨(.Ok repW, s1), rfl, hRun1, hCfg1, hPg1, hCw1, hSig1, hDe1, hWl1, hLen1, hTr1,
          fun fd hEq => by
            injection hEq with hEq'
            subst hEq'
            exact ⟨(fun h => by cases h), (fun _ => rfl),
              ⟨e, _, rfl, hCl.1, rfl, rfl⟩, fun k h1 _ => hCl.2 k h1⟩⟩
  · dsimp only
    refine okPost_mono
      (okPost_and (relocate_rep_above2_safety s hRun repW) (relocate_rep_above2_trace_rc s repW))
      fun (r0, s1) ⟨⟨hRun1, hCfg1, hPg1, hCw1, hSig1, hDe1, hWl1, hLen1, hOk1⟩, hTr1⟩ => ?_
    refine ⟨hRun1, hCfg1, hPg1, hCw1, hSig1, hDe1, hWl1, hLen1, hTr1, fun fd hEq => ?_⟩
    rcases hOk1 fd hEq with ⟨hGt2, hPair, hLe2, hGt2R, hOther⟩
    exact ⟨(fun _ => ⟨hGt2, hLe2, hGt2R⟩), (fun h => by cases h), hPair, hOther⟩

private theorem prepare_rep_w_dspec_blockedSigs
    (s : ChildState) (redir : Bool) (repW : I32) :
    WP.dspec (postfork.child.prepare_rep_w s redir repW) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold postfork.child.prepare_rep_w
  cases redir
  · refine WP.dspec_bind (set_cloexec_dspec_blockedSigs s repW) fun ⟨r, s1⟩ hs1 => ?_
    cases r <;> exact (WP.dspec_ok _).mpr hs1
  · exact relocate_rep_above2_dspec_blockedSigs s repW

private theorem prepare_rep_w_ok_of_open
    (s : ChildState) (hRun : s.status = .running) (hOr : s.oracle = [])
    (redir : Bool) (repW : I32) (hRepGe : 0#i32 ≤ repW) (hOpRep : s.isOpen repW.val = true)
    (hLim : redir = true → min s.fdLimit 2147483648 ≥ 6 + Int.ofNat s.fds.length) :
    OkPost (postfork.child.prepare_rep_w s redir repW) fun (r, s1) =>
      ∃ fd, r = .Ok fd ∧ s1.status = .running ∧ SameChildConfig s1 s ∧
        s1.pgid = s.pgid ∧ s1.cwd = s.cwd ∧ s1.sig = s.sig ∧
        s1.descs = s.descs ∧ s1.writeLog = s.writeLog ∧
        s1.fds.length ≤ s.fds.length + 1 ∧
        (redir = false → fd = repW) := by
  cases redir
  · unfold postfork.child.prepare_rep_w
    dsimp only
    refine okPost_bind (okPost_and (set_cloexec_safety s hRun repW) (set_cloexec_spec s hRun hOr repW))
      fun (r0, s1) ⟨⟨hRun1, hCfg1, hPg1, hCw1, hSig1, hDe1, hWl1, hLen1, _⟩, ⟨hClo, _⟩⟩ => ?_
    cases hGet : s.getFd repW.val with
    | none => simp [ChildState.isOpen, hGet] at hOpRep
    | some e =>
      simp only [CloexecTogglePost, hGet] at hClo
      rw [hClo.1]
      exact okPost_ok _ _ ⟨repW, rfl, hRun1, hCfg1, hPg1, hCw1, hSig1, hDe1, hWl1,
        hLen1, fun _ => rfl⟩
  · unfold postfork.child.prepare_rep_w
    dsimp only
    have hLim6 := hLim rfl
    cases hGet : s.getFd repW.val with
    | none => simp [ChildState.isOpen, hGet] at hOpRep
    | some e =>
      refine okPost_mono
        (relocate_rep_ok_of_open s hRun hOr repW hRepGe hGet (by omega))
        fun (r0, s1) ⟨hRun1, _, hLen1, hPg1, hCw1, hSig1, hDe1, hWl1, hCfg1, fd, _, hOk, _, _, _, _, _, _⟩ =>
        ⟨fd, hOk, hRun1, hCfg1, hPg1, hCw1, hSig1, hDe1, hWl1, hLen1, fun h => by cases h⟩

private theorem apply_redir_stdio_safety
    (s : ChildState) (hRun : s.status = .running) (redir : Bool)
    (inFd outFd errFd : I32) (closeSrcs : Bool) :
    OkPost (postfork.child.apply_redir_stdio s redir inFd outFd errFd closeSrcs) fun (r, s1) =>
      s1.status = .running ∧
      TraceExtends s s1 ∧
      (r = .Ok () →
        SameChildConfig s1 s ∧
        s1.pgid = s.pgid ∧ s1.cwd = s.cwd ∧ s1.sig = s.sig ∧
        s1.descs = s.descs ∧ s1.writeLog = s.writeLog ∧
        (redir = true → SetupStdioSafetyPost s inFd outFd errFd closeSrcs s1) ∧
        (redir = false → s1 = s)) := by
  unfold postfork.child.apply_redir_stdio
  cases redir
  · exact ⟨(.Ok (), s), rfl, hRun, traceExtends_refl s,
      fun _ => ⟨SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, (fun h => by cases h), fun _ => rfl⟩⟩
  · refine okPost_mono
      (okPost_and (setup_stdio_safety s hRun inFd outFd errFd closeSrcs)
        (setup_stdio_trace s inFd outFd errFd closeSrcs))
      fun (r0, s1) ⟨⟨hRun1, hOk1⟩, hTr1⟩ => ?_
    refine ⟨hRun1, hTr1, fun hr => ?_⟩
    rcases hOk1 hr with ⟨hCfg, hPg, hCw, hSig, hDe, hWl, hn0, hn1, hn2, h0, h1, h2, hKeep, hSec⟩
    exact ⟨hCfg, hPg, hCw, hSig, hDe, hWl, (fun _ => ⟨h0, h1, h2, hKeep, hSec⟩), fun h => by cases h⟩

private theorem apply_redir_stdio_dspec_blockedSigs
    (s : ChildState) (redir : Bool) (inFd outFd errFd : I32) (closeSrcs : Bool) :
    WP.dspec (postfork.child.apply_redir_stdio s redir inFd outFd errFd closeSrcs) fun p =>
      p.2.blockedSigs = s.blockedSigs := by
  unfold postfork.child.apply_redir_stdio
  cases redir
  · exact (WP.dspec_ok _).mpr rfl
  · exact setup_stdio_dspec_blockedSigs s inFd outFd errFd closeSrcs

private theorem apply_redir_stdio_ok_spec
    (s : ChildState) (hRun : s.status = .running) (hOr : s.oracle = [])
    (redir : Bool) (inFd outFd errFd : I32) (closeSrcs : Bool)
    (hNonNeg : redir = true → 0#i32 ≤ inFd ∧ 0#i32 ≤ outFd ∧ 0#i32 ≤ errFd)
    (hOpen : redir = true → s.isOpen inFd.val = true ∧ s.isOpen outFd.val = true ∧ s.isOpen errFd.val = true)
    (hLim : redir = true → min s.fdLimit 2147483648 ≥ 5 + Int.ofNat s.fds.length) :
    OkPost (postfork.child.apply_redir_stdio s redir inFd outFd errFd closeSrcs) fun (r, s1) =>
      r = .Ok () ∧
      (redir = true → SetupStdioPost s inFd outFd errFd closeSrcs s1) ∧
      (redir = false → s1 = s) := by
  unfold postfork.child.apply_redir_stdio
  cases redir
  · exact ⟨(.Ok (), s), rfl, rfl, (fun h => by cases h), fun _ => rfl⟩
  · exact okPost_mono
      (setup_stdio_spec s hRun hOr inFd outFd errFd closeSrcs (hNonNeg rfl) (hOpen rfl) (hLim rfl))
      fun (r0, s1) ⟨hr0, hPost⟩ => ⟨hr0, (fun _ => hPost), fun h => by cases h⟩

private theorem apply_close_unkept_safety
    (s : ChildState) (hRun : s.status = .running) (closeUnkept : Bool) (safeRepW : I32)
    (keepFds : Slice I32) :
    OkPost (postfork.child.apply_close_unkept s closeUnkept safeRepW keepFds) fun (r, s1) =>
      s1.status = .running ∧
      TraceExtends s s1 ∧
      (r = .Ok () →
        SameChildConfig s1 s ∧
        s1.pgid = s.pgid ∧ s1.cwd = s.cwd ∧ s1.sig = s.sig ∧ s1.writeLog = s.writeLog ∧
        (closeUnkept = true →
          (∀ fd e, 0 ≤ fd → fd ≤ 2147483647 →
            (fd ≤ 2 ∨ isKeptAbove2 safeRepW keepFds.val fd = true) →
            s.getFd fd = some e → s1.getDesc e.desc = s.getDesc e.desc) ∧
          (∀ fd : Int, 0 ≤ fd → fd ≤ 2 → s.getFd fd ≠ none → s1.getFd fd = s.getFd fd) ∧
          (∀ fd : Int, 3 ≤ fd → fd ≤ 2147483647 →
            isKeptAbove2 safeRepW keepFds.val fd = true → s.getFd fd ≠ none → s1.getFd fd = s.getFd fd) ∧
          CloseAbove2Post s safeRepW keepFds.val s1) ∧
        (closeUnkept = false → s1 = s)) := by
  unfold postfork.child.apply_close_unkept
  cases closeUnkept
  · exact ⟨(.Ok (), s), rfl, hRun, traceExtends_refl s,
      fun _ => ⟨SameChildConfig.refl s, rfl, rfl, rfl, rfl, (fun h => by cases h), fun _ => rfl⟩⟩
  · exact okPost_mono
      (okPost_and (close_fds_above2_except_safety s safeRepW keepFds hRun)
        (apply_close_unkept_trace s true safeRepW keepFds hRun))
      fun (r0, s1) ⟨⟨hRun1, hOk1⟩, hTr1⟩ => by
        refine ⟨hRun1, hTr1, fun hr => ?_⟩
        rcases hOk1 hr with ⟨hCfg, hPg, hCw, hSig, hWl, hDe, h02, hKp, hSec⟩
        exact ⟨hCfg, hPg, hCw, hSig, hWl, (fun _ => ⟨hDe, h02, hKp, hSec⟩), fun h => by cases h⟩

private theorem apply_close_unkept_dspec_blockedSigs
    (s : ChildState) (closeUnkept : Bool) (safeRepW : I32) (keepFds : Slice I32) :
    WP.dspec (postfork.child.apply_close_unkept s closeUnkept safeRepW keepFds) fun p =>
      p.2.blockedSigs = s.blockedSigs := by
  unfold postfork.child.apply_close_unkept
  cases closeUnkept
  · exact (WP.dspec_ok _).mpr rfl
  · exact close_fds_above2_except_dspec_blockedSigs s safeRepW keepFds

private theorem apply_close_unkept_ok_spec
    (s : ChildState) (hRun : s.status = .running) (hOr : s.oracle = [])
    (closeUnkept : Bool) (safeRepW : I32) (keepFds : Slice I32)
    (hCap : closeUnkept = true →
      s.closeRangeSupported = true ∨
      (s.procSelfFdAvailable = true ∧ min s.fdLimit 2147483648 ≥ 1 + Int.ofNat s.fds.length)) :
    OkPost (postfork.child.apply_close_unkept s closeUnkept safeRepW keepFds) fun (r, s1) =>
      r = .Ok () ∧
      (closeUnkept = true → CloseAbove2Post s safeRepW keepFds.val s1) ∧
      (closeUnkept = false → s1 = s) := by
  unfold postfork.child.apply_close_unkept
  cases closeUnkept
  · exact ⟨(.Ok (), s), rfl, rfl, (fun h => by cases h), fun _ => rfl⟩
  · exact okPost_mono (close_fds_above2_except_spec s safeRepW keepFds hRun hOr (hCap rfl))
      fun (r0, s1) ⟨hr0, _, _, _, _, _, _, _, _, hPost⟩ => ⟨hr0, (fun _ => hPost), fun h => by cases h⟩

end StepWrappers

section PostSyncAndRunChild

private theorem i32_nonneg_of_val {x : I32} (h : (0 : Int) ≤ x.val) : 0#i32 ≤ x := by
  scalar_tac

private theorem i32_val_nonneg {x : I32} (h : 0#i32 ≤ x) : (0 : Int) ≤ x.val := by
  scalar_tac

private theorem isKeptAbove2_self (fd : I32) (keepFds : List I32) (h : 2 < fd.val) :
    isKeptAbove2 fd keepFds fd.val = true := by
  simp only [isKeptAbove2, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_self_eq_true]
  exact ⟨h, Or.inl ⟨h, trivial⟩⟩

private theorem i32_val_le_max (x : I32) : x.val ≤ 2147483647 := by
  scalar_tac

private theorem rc_flag_redirect_stdio_eq :
    postfork.child.FLAG_REDIRECT_STDIO = FLAG_REDIRECT_STDIO := by
  unfold postfork.child.FLAG_REDIRECT_STDIO FLAG_REDIRECT_STDIO; rfl

private theorem rc_flag_close_unkept_eq :
    postfork.child.FLAG_CLOSE_UNKEPT_ABOVE2 = FLAG_CLOSE_UNKEPT_ABOVE2 := by
  unfold postfork.child.FLAG_CLOSE_UNKEPT_ABOVE2 FLAG_CLOSE_UNKEPT_ABOVE2; rfl

private theorem rc_flag_close_stdio_eq :
    postfork.child.FLAG_CLOSE_STDIO_SOURCES = FLAG_CLOSE_STDIO_SOURCES := by
  unfold postfork.child.FLAG_CLOSE_STDIO_SOURCES FLAG_CLOSE_STDIO_SOURCES; rfl

private theorem validRunChildNoOverlap_split
    {flags : U32} {syncR inFd outFd errFd repW : I32} {closeFds keepFds : List I32}
    (hOv : validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds keepFds = true) :
    sliceContainsNonnegSpec closeFds repW.val = false ∧
    sliceContainsNonnegSpec keepFds repW.val = false ∧
    slicesOverlapNonnegSpec closeFds keepFds = false ∧
    (flagSet flags FLAG_HAS_SYNC_BARRIER = true →
      repW ≠ syncR ∧
      sliceContainsNonnegSpec closeFds syncR.val = false ∧
      sliceContainsNonnegSpec keepFds syncR.val = false) ∧
    (flagSet flags FLAG_REDIRECT_STDIO = true →
      sliceHasStdioSlotSpec keepFds = false ∧
      fdInStdioSpec repW inFd outFd errFd = false ∧
      stdioInSliceSpec closeFds inFd outFd errFd = false ∧
      (flagSet flags FLAG_HAS_SYNC_BARRIER = true → fdInStdioSpec syncR inFd outFd errFd = false) ∧
      (flagSet flags FLAG_CLOSE_STDIO_SOURCES = true →
        (inFd.val > 2 → sliceContainsNonnegSpec keepFds inFd.val = false) ∧
        (outFd.val > 2 → sliceContainsNonnegSpec keepFds outFd.val = false) ∧
        (errFd.val > 2 → sliceContainsNonnegSpec keepFds errFd.val = false))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases h : sliceContainsNonnegSpec closeFds repW.val <;>
      first | rfl | (unfold validRunChildNoOverlap at hOv; simp [h] at hOv)
  · cases h : sliceContainsNonnegSpec keepFds repW.val <;>
      first | rfl | (unfold validRunChildNoOverlap at hOv; simp [h] at hOv)
  · cases h : slicesOverlapNonnegSpec closeFds keepFds <;>
      first | rfl | (unfold validRunChildNoOverlap at hOv; simp [h] at hOv)
  · intro hS
    refine ⟨?_, ?_, ?_⟩
    · intro hEq; unfold validRunChildNoOverlap at hOv; simp [hS, hEq] at hOv
    · cases h : sliceContainsNonnegSpec closeFds syncR.val <;>
        first | rfl | (unfold validRunChildNoOverlap at hOv; simp [hS, h] at hOv)
    · cases h : sliceContainsNonnegSpec keepFds syncR.val <;>
        first | rfl | (unfold validRunChildNoOverlap at hOv; simp [hS, h] at hOv)
  · intro hR
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · cases h : sliceHasStdioSlotSpec keepFds <;>
        first | rfl | (unfold validRunChildNoOverlap at hOv; simp [hR, h] at hOv)
    · cases h : fdInStdioSpec repW inFd outFd errFd <;>
        first | rfl | (unfold validRunChildNoOverlap at hOv; simp [hR, h] at hOv)
    · cases h : stdioInSliceSpec closeFds inFd outFd errFd <;>
        first | rfl | (unfold validRunChildNoOverlap at hOv; simp [hR, h] at hOv)
    · intro hS
      cases h : fdInStdioSpec syncR inFd outFd errFd <;>
        first | rfl | (unfold validRunChildNoOverlap at hOv; simp [hR, hS, h] at hOv)
    · intro hCS
      refine ⟨fun hi => ?_, fun ho => ?_, fun he => ?_⟩
      · cases h : sliceContainsNonnegSpec keepFds inFd.val <;>
          first | rfl | (unfold validRunChildNoOverlap at hOv
                         simp [hR, hCS, h] at hOv; omega)
      · cases h : sliceContainsNonnegSpec keepFds outFd.val <;>
          first | rfl | (unfold validRunChildNoOverlap at hOv
                         simp [hR, hCS, h] at hOv; omega)
      · cases h : sliceContainsNonnegSpec keepFds errFd.val <;>
          first | rfl | (unfold validRunChildNoOverlap at hOv
                         simp [hR, hCS, h] at hOv; omega)

private theorem validFlagsSpec_split {flags : U32} (hFl : validFlagsSpec flags = true) :
    flagSet flags FLAG_CLOSE_STDIO_SOURCES = true →
      flagSet flags FLAG_REDIRECT_STDIO = true ∧
      flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 = false := by
  intro hCS
  unfold validFlagsSpec at hFl
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hFl
  rcases hFl.2 with hf | ⟨hr, hu⟩
  · rw [hCS] at hf; cases hf
  · exact ⟨hr, hu⟩

private theorem preSync_trace_closedBeforeSync
    {s s1 sEnd : ChildState} {flags : U32} {syncR inFd outFd errFd repW : I32}
    {closeFds keepFds : List I32}
    (hPre : PreSyncOkPost s flags syncR inFd outFd errFd repW closeFds keepFds s1)
    (hExt : TraceExtends s1 sEnd) :
    flagSet flags FLAG_HAS_SYNC_BARRIER = true →
    closedBeforeSyncRead (sEnd.trace.drop s.trace.length) closeFds syncR := by
  intro _
  rcases hPre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 with ⟨tA, tB, hTr1, hNoRd, hClosed⟩
  rcases hExt with ⟨tRest, hTrEnd⟩
  have hDrop : sEnd.trace.drop s.trace.length = tA ++ (tB ++ tRest) := by
    rw [hTrEnd, hTr1, List.append_assoc, List.append_assoc, List.drop_left]
  rw [hDrop]
  exact closedBeforeSyncRead_append hNoRd hClosed

private theorem run_child_post_sync_safety
    (s s1 : ChildState)
    (flags : U32) (syncR inFd outFd errFd repW : I32)
    (closeFds : List I32) (keepFds : Slice I32)
    (cwd? : Option sys.CStr) (path : sys.CStr) (argv envp : sys.CStrArray)
    (hPre : PreSyncOkPost s flags syncR inFd outFd errFd repW closeFds keepFds.val s1) :
    OkPost
      (postfork.child.run_child_post_sync s1 { flags := flags, sync_r := syncR, stdin_fd := inFd, stdout_fd := outFd, stderr_fd := errFd, rep_w := repW } keepFds { cwd := cwd?, path := path, argv := argv, envp := envp })
      (RunChildSafetyPost s flags syncR inFd outFd errFd repW closeFds keepFds.val cwd? path argv envp) := by
  have hRun1 : s1.status = .running := hPre.1
  have hCfg1 : SameChildConfig s1 s := hPre.2.1
  have hWl1 : s1.writeLog = s.writeLog := hPre.2.2.1
  have hCw1 : s1.cwd = s.cwd := hPre.2.2.2.1
  have hFlT : validFlagsSpec flags = true := hPre.2.2.2.2.1
  have hRepGe : 0#i32 ≤ repW := hPre.2.2.2.2.2.1
  have hSgT : validSignsSpec flags syncR inFd outFd errFd = true := hPre.2.2.2.2.2.2.1
  have hOvT : validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds keepFds.val = true :=
    hPre.2.2.2.2.2.2.2.1
  have hPgid1T : flagSet flags FLAG_SET_PGID = true → s1.pgid = s.pid := hPre.2.2.2.2.2.2.2.2.2.1
  have hPgid1F : flagSet flags FLAG_SET_PGID = false → s1.pgid = s.pgid := hPre.2.2.2.2.2.2.2.2.2.2.1
  have hSig1T : flagSet flags FLAG_RESET_SIGPIPE = true →
      s1.getSig 13 = .default ∧ s1.blockedSigs = s.blockedSigs.filter (· != 13) :=
    hPre.2.2.2.2.2.2.2.2.2.2.2.1
  have hSig1F : flagSet flags FLAG_RESET_SIGPIPE = false →
      s1.getSig 13 = s.getSig 13 ∧ s1.blockedSigs = s.blockedSigs :=
    hPre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSig1Oth : ∀ g : Int, g ≠ 13 → s1.getSig g = s.getSig g :=
    hPre.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hKeep1 : ∀ k : Int, (k ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false) →
      sliceContainsNonnegSpec closeFds k = false → s1.getFd k = s.getFd k :=
    hPre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSec1 : oracleHasSeccomp s.oracle = false → ∀ k : Int,
      s1.getFd k =
        if sliceContainsNonnegSpec closeFds k || (flagSet flags FLAG_HAS_SYNC_BARRIER && k == syncR.val)
        then none else s.getFd k :=
    hPre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hStdOpenPre : flagSet flags FLAG_REDIRECT_STDIO = true →
      s.isOpen inFd.val = true ∧ s.isOpen outFd.val = true ∧ s.isOpen errFd.val = true :=
    hPre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hKpOpenPre : ∀ k ∈ keepFds.val, 0#i32 ≤ k → s.isOpen k.val = true :=
    hPre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFlSplit := validFlagsSpec_split hFlT
  have hOvSplit := validRunChildNoOverlap_split hOvT
  unfold postfork.child.run_child_post_sync
  simp only [rc_flag_redirect_stdio_eq, rc_flag_close_unkept_eq, rc_flag_close_stdio_eq,
    lift, Aeneas.Std.lift, bind_ok]
  let bRedir := (flags &&& FLAG_REDIRECT_STDIO != 0#u32)
  let bCloseUnk := (flags &&& FLAG_CLOSE_UNKEPT_ABOVE2 != 0#u32)
  let bCloseSrc := (flags &&& FLAG_CLOSE_STDIO_SOURCES != 0#u32)
  have hbRedirEq : bRedir = flagSet flags FLAG_REDIRECT_STDIO := rfl
  have hbUnkEq : bCloseUnk = flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 := rfl
  have hbSrcEq : bCloseSrc = flagSet flags FLAG_CLOSE_STDIO_SOURCES := rfl
  have h127 : ∀ (x : ChildState), x.status = .running → ∀ (w : I32) (st : U8) (e fb : I32),
      OkPost (postfork.child.report_and_exit x w st e fb)
        (RunChildSafetyPost s flags syncR inFd outFd errFd repW closeFds keepFds.val cwd? path argv envp) :=
    fun x hx w st e fb => okPost_mono (report_and_exit_status127 x hx w st e fb) fun _ hs => Or.inl hs
  refine okPost_bind
    (okPost_dspec (prepare_rep_w_safety s1 hRun1 bRedir repW)
      (prepare_rep_w_dspec_blockedSigs s1 bRedir repW))
    fun (r1, s2) ⟨hs2, hBlk2⟩ => ?_
  rcases hs2 with ⟨hRun2, hCfg2, hPg2, hCw2, hSig2, hDe2, hWl2, _, hTr12, hRepOk⟩
  cases r1 with
  | Err e => exact h127 s2 hRun2 repW _ e _
  | Ok fd =>
    rcases hRepOk fd rfl with ⟨hFdRedir, hFdNoRedir, ⟨_, fRel, _, hGetRel, _, hCloRel⟩, hFdOther2⟩
    refine okPost_bind
      (okPost_dspec (apply_redir_stdio_safety s2 hRun2 bRedir inFd outFd errFd bCloseSrc)
        (apply_redir_stdio_dspec_blockedSigs s2 bRedir inFd outFd errFd bCloseSrc))
      fun (r2, s3) ⟨hs3, hBlk3⟩ => ?_
    rcases hs3 with ⟨hRun3, hTr23, hRedirPost⟩
    cases r2 with
    | Err e => exact h127 s3 hRun3 fd _ e _
    | Ok u2 =>
      rcases hRedirPost (by cases u2; rfl) with ⟨hCfg3, hPg3, hCw3, hSig3, _, hWl3, hStdioT3, hStdioF3⟩
      refine okPost_bind
        (okPost_dspec
          (okPost_and (clear_cloexec_slice_safety s3 hRun3 keepFds)
            (clear_cloexec_slice_trace_rc s3 hRun3 keepFds))
          (clear_cloexec_slice_dspec_blockedSigs s3 keepFds))
        fun (r3, s4) ⟨⟨hs4, hTr34⟩, hBlk4⟩ => ?_
      rcases hs4 with ⟨hRun4, hCfg4, hPg4, hCw4, hSig4, _, hWl4, hClrOk4⟩
      cases r3 with
      | Err e => exact h127 s4 hRun4 fd _ e _
      | Ok u3 =>
        rcases hClrOk4 (by cases u3; rfl) with ⟨hClrNe4, hClrKp4⟩
        refine okPost_bind
          (okPost_dspec (apply_close_unkept_safety s4 hRun4 bCloseUnk fd keepFds)
            (apply_close_unkept_dspec_blockedSigs s4 bCloseUnk fd keepFds))
          fun (r4, s5) ⟨hs5, hBlk5⟩ => ?_
        rcases hs5 with ⟨hRun5, hTr45, hUnkPost⟩
        cases r4 with
        | Err e => exact h127 s5 hRun5 fd _ e _
        | Ok u4 =>
          rcases hUnkPost (by cases u4; rfl) with ⟨hCfg5, hPg5, hCw5, hSig5, hWl5, hUnkT5, hUnkF5⟩
          have hCfg50 : SameChildConfig s5 s := hCfg5.trans (hCfg4.trans (hCfg3.trans (hCfg2.trans hCfg1)))
          have hPg5S : s5.pgid = s1.pgid := hPg5.trans (hPg4.trans (hPg3.trans hPg2))
          have hWl5S : s5.writeLog = s.writeLog := hWl5.trans (hWl4.trans (hWl3.trans (hWl2.trans hWl1)))
          have hCw5S : s5.cwd = s.cwd := hCw5.trans (hCw4.trans (hCw3.trans (hCw2.trans hCw1)))
          have hSig5S : s5.sig = s1.sig := hSig5.trans (hSig4.trans (hSig3.trans hSig2))
          have hBlk5S : s5.blockedSigs = s1.blockedSigs := hBlk5.trans (hBlk4.trans (hBlk3.trans hBlk2))
          have hNoStdKeep : bRedir = true → ∀ k : Int, 0 ≤ k → k ≤ 2 →
              ∀ kp ∈ keepFds.val, 0#i32 ≤ kp → k ≠ kp.val := by
            intro hR k hk0 hk2 kp hkp hp0 heq
            subst heq
            have hStd := (hOvSplit.2.2.2.2 hR).1
            have hMem : sliceHasStdioSlotSpec keepFds.val = true := by
              rw [sliceHasStdioSlotSpec, List.any_eq_true]
              exact ⟨kp, hkp, by simp [decide_eq_true hk0, decide_eq_true hk2]⟩
            exact absurd hMem (by rw [hStd]; decide)
          have hKeepNeSrc : bRedir = true → bCloseSrc = true → ∀ kp ∈ keepFds.val, 0#i32 ≤ kp →
              kp.val ≠ inFd.val ∧ kp.val ≠ outFd.val ∧ kp.val ≠ errFd.val := by
            intro hR hCS kp hkp hp0
            have hC := (hOvSplit.2.2.2.2 hR).2.2.2.2 hCS
            have hNoStd := hNoStdKeep hR
            refine ⟨?_, ?_, ?_⟩
            · intro heq
              by_cases hgt : inFd.val > 2
              · have hF := hC.1 hgt
                have hIn : sliceContainsNonnegSpec keepFds.val inFd.val = true := by
                  rw [sliceContainsNonnegSpec, Bool.and_eq_true, List.any_eq_true]
                  exact ⟨decide_eq_true (by omega), kp, hkp, by simp [heq]⟩
                exact absurd hIn (by rw [hF]; decide)
              · exact hNoStd inFd.val (by scalar_tac) (by omega) kp hkp hp0 heq.symm
            · intro heq
              by_cases hgt : outFd.val > 2
              · have hF := hC.2.1 hgt
                have hIn : sliceContainsNonnegSpec keepFds.val outFd.val = true := by
                  rw [sliceContainsNonnegSpec, Bool.and_eq_true, List.any_eq_true]
                  exact ⟨decide_eq_true (by omega), kp, hkp, by simp [heq]⟩
                exact absurd hIn (by rw [hF]; decide)
              · exact hNoStd outFd.val (by scalar_tac) (by omega) kp hkp hp0 heq.symm
            · intro heq
              by_cases hgt : errFd.val > 2
              · have hF := hC.2.2 hgt
                have hIn : sliceContainsNonnegSpec keepFds.val errFd.val = true := by
                  rw [sliceContainsNonnegSpec, Bool.and_eq_true, List.any_eq_true]
                  exact ⟨decide_eq_true (by omega), kp, hkp, by simp [heq]⟩
                exact absurd hIn (by rw [hF]; decide)
              · exact hNoStd errFd.val (by scalar_tac) (by omega) kp hkp hp0 heq.symm
          have hKeepNeSync : flagSet flags FLAG_HAS_SYNC_BARRIER = true →
              ∀ kp ∈ keepFds.val, 0#i32 ≤ kp → kp.val ≠ syncR.val := by
            intro hS kp hkp hp0 heq
            have hF := (hOvSplit.2.2.2.1 hS).2.2
            have hIn : sliceContainsNonnegSpec keepFds.val syncR.val = true := by
              rw [sliceContainsNonnegSpec, Bool.and_eq_true, List.any_eq_true]
              exact ⟨decide_eq_true (by scalar_tac), kp, hkp, by simp [heq]⟩
            exact absurd hIn (by rw [hF]; decide)
          have hKeepNeClose : ∀ kp ∈ keepFds.val, 0#i32 ≤ kp →
              sliceContainsNonnegSpec closeFds kp.val = false := by
            intro kp hkp hp0
            by_contra hc
            simp only [Bool.not_eq_false, sliceContainsNonnegSpec, Bool.and_eq_true,
              decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hc
            rcases hc with ⟨_, c, hcM, hcEq⟩
            have hOv : slicesOverlapNonnegSpec closeFds keepFds.val = true := by
              rw [slicesOverlapNonnegSpec, List.any_eq_true]
              refine ⟨c, hcM, ?_⟩
              simp only [Bool.and_eq_true, decide_eq_true_eq, sliceContainsNonnegSpec, List.any_eq_true, beq_iff_eq]
              exact ⟨by scalar_tac, by scalar_tac, kp, hkp, hcEq.symm⟩
            exact absurd hOv (by rw [hOvSplit.2.2.1]; decide)
          have finishExec : ∀ (sPre : ChildState),
              sPre.status = .running →
              SameChildConfig sPre s →
              sPre.pgid = s5.pgid →
              sPre.writeLog = s.writeLog →
              sPre.sig = s1.sig →
              sPre.blockedSigs = s1.blockedSigs →
              (∀ k, sPre.getFd k = s5.getFd k) →
              TraceExtends s5 sPre →
              (cwd? = none → sPre.cwd = s.cwd) →
              (∀ dir, cwd? = some dir → sPre.cwd = resolveChdirTarget s dir) →
              OkPost (do
                let (e, sExec) ← sys.execve sPre path argv envp
                postfork.child.report_and_exit sExec fd postfork.child.STAGE_EXECVE e postfork.child.ENOENT)
                (RunChildSafetyPost s flags syncR inFd outFd errFd repW closeFds keepFds.val cwd? path argv envp) := by
            intro sPre hRunP hCfgP hPgP hWlP hSigP hBlkP hFdsP hTr5P hCwN hCwS
            obtain ⟨eEx, sEx, hExEq, _, _, _, _, _, _, _, hExSpec⟩ :=
              sys_execve_running sPre hRunP path argv envp
            rw [hExEq, bind_ok]
            have hExFail : sEx.status = .running →
                OkPost (postfork.child.report_and_exit sEx fd postfork.child.STAGE_EXECVE eEx postfork.child.ENOENT)
                  (RunChildSafetyPost s flags syncR inFd outFd errFd repW closeFds keepFds.val cwd? path argv envp) :=
              fun hStRun => h127 sEx hStRun fd _ eEx _
            cases hcf : currentFault sPre with
            | seccomp _ =>
              simp only [hcf] at hExSpec
              exact hExFail hExSpec.2.2
            | fail _ =>
              simp only [hcf] at hExSpec
              by_cases hemp : path.isEmpty = true
              · simp only [hemp, ↓reduceIte] at hExSpec
                exact hExFail hExSpec.2.2
              · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at hExSpec
                exact hExFail hExSpec.2.2
            | normal | partialWrite _ | dentsBatch _ =>
              simp only [hcf] at hExSpec
              by_cases hemp : path.isEmpty = true
              · simp only [hemp, ↓reduceIte] at hExSpec
                exact hExFail hExSpec.2.2
              · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at hExSpec
                have hExStatus : sEx.status = .execd (imageOf sPre path argv envp) := hExSpec.2.2
                have hNotRun : sEx.status ≠ .running := by rw [hExStatus]; intro h; cases h
                refine okPost_mono
                  (report_and_exit_not_running sEx hNotRun fd postfork.child.STAGE_EXECVE eEx postfork.child.ENOENT)
                  fun sFin hFinEq => ?_
                rw [hFinEq]
                let img := imageOf sPre path argv envp
                have hTrEx : TraceExtends sPre sEx := sys_execve_trace_eq sPre path argv envp hExEq
                have hTr1P : TraceExtends s1 sPre :=
                  traceExtends_trans hTr12 (traceExtends_trans hTr23 (traceExtends_trans hTr34 (traceExtends_trans hTr45 hTr5P)))
                have hTrAll : TraceExtends s1 sEx := traceExtends_trans hTr1P hTrEx
                have hCls := preSync_trace_closedBeforeSync hPre hTrAll
                have hWrEx : sEx.writeLog = s.writeLog := by
                  unfold sys.execve at hExEq
                  rw [hRunP, hcf] at hExEq
                  simp only [hemp, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at hExEq
                  obtain ⟨_, rfl⟩ := hExEq
                  exact hWlP
                have hCwdImg : img.cwd = expectedCwdAfter s.cwd cwd? s.chdirResolved := by
                  cases hc : cwd? with
                  | none => simp [img, imageOf, expectedCwdAfter, hCwN hc]
                  | some dir =>
                    show sPre.cwd = expectedCwdAfter s.cwd (some dir) s.chdirResolved
                    rw [hCwS dir hc]; rfl
                have hsPreSig : ∀ k, sPre.getSig k = s1.getSig k := fun k => by
                  simp [ChildState.getSig, hSigP]
                have hSig13R : flagSet flags FLAG_RESET_SIGPIPE = true →
                    execImageGetSig img 13 = .default ∧ img.blockedSigs = s.blockedSigs.filter (· != 13) ∧
                    img.blockedSigs.contains 13 = false := by
                  intro hRsp
                  rcases hSig1T hRsp with ⟨hs13, hbs⟩
                  refine ⟨?_, ?_, ?_⟩
                  · change execImageGetSig (imageOf sPre path argv envp) 13 = Disp.default
                    rw [execImageGetSig_imageOf, hsPreSig 13, hs13]
                  · change sPre.blockedSigs = s.blockedSigs.filter (· != 13)
                    rw [hBlkP, hbs]
                  · change sPre.blockedSigs.contains 13 = false
                    rw [hBlkP, hbs]; exact blockedSigs_filter13_not_contains13 s.blockedSigs
                have hSig13F : flagSet flags FLAG_RESET_SIGPIPE = false →
                    execImageGetSig img 13 = (if s.getSig 13 == .ignore then .ignore else .default) ∧
                    img.blockedSigs = s.blockedSigs := by
                  intro hRspF
                  rcases hSig1F hRspF with ⟨hs13, hbs⟩
                  refine ⟨?_, ?_⟩
                  · change execImageGetSig (imageOf sPre path argv envp) 13 =
                      if s.getSig 13 == Disp.ignore then Disp.ignore else Disp.default
                    rw [execImageGetSig_imageOf, hsPreSig 13, hs13]
                    cases s.getSig 13 <;> rfl
                  · change sPre.blockedSigs = s.blockedSigs
                    rw [hBlkP, hbs]
                have hSigOth : ∀ g : Int, g ≠ 13 →
                    execImageGetSig img g = (if s.getSig g == .ignore then .ignore else .default) := by
                  intro g hg
                  change execImageGetSig (imageOf sPre path argv envp) g =
                    if s.getSig g == Disp.ignore then Disp.ignore else Disp.default
                  rw [execImageGetSig_imageOf, hsPreSig g, hSig1Oth g hg]
                  cases s.getSig g <;> rfl
                have hPgidImg : img.pgid = (if flagSet flags FLAG_SET_PGID then s.pid else s.pgid) := by
                  change sPre.pgid = _
                  rw [hPgP, hPg5S]
                  cases hPgB : flagSet flags FLAG_SET_PGID
                  · simp [hPgid1F hPgB]
                  · simp [hPgid1T hPgB]
                have hImgFd : ∀ k, execImageGetFd img k =
                    match s5.getFd k with | some e => if e.cloexec then none else some e | none => none := by
                  intro k
                  change execImageGetFd (imageOf sPre path argv envp) k = _
                  rw [execImageGetFd_imageOf, hFdsP k]
                  cases s5.getFd k <;> rfl
                have hS4Get2 : ∀ (x : I32), flagSet flags FLAG_REDIRECT_STDIO = true →
                    fdInStdioSpec repW inFd outFd errFd = false →
                    stdioInSliceSpec closeFds inFd outFd errFd = false →
                    (x = inFd ∨ x = outFd ∨ x = errFd) →
                    s.isOpen x.val = true →
                    s2.getFd x.val = s.getFd x.val := by
                  intro x hR hRepStd hSlStd hxMem hxOpen
                  have hNeRep : x.val ≠ repW.val := by
                    intro heq
                    unfold fdInStdioSpec at hRepStd
                    have hEqI : repW = x := IScalar.eq_of_val_eq heq.symm
                    subst hEqI
                    rcases hxMem with rfl | rfl | rfl <;> simp at hRepStd
                  have hNotCl : sliceContainsNonnegSpec closeFds x.val = false := by
                    cases hc : sliceContainsNonnegSpec closeFds x.val
                    · rfl
                    · unfold stdioInSliceSpec at hSlStd
                      rcases hxMem with rfl | rfl | rfl <;> simp [hc] at hSlStd
                  have hNotSy : x.val ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false := by
                    by_cases hS : flagSet flags FLAG_HAS_SYNC_BARRIER = true
                    · left; intro heq
                      have hSyncStd := (hOvSplit.2.2.2.2 hR).2.2.2.1 hS
                      unfold fdInStdioSpec at hSyncStd
                      have hEqI : syncR = x := IScalar.eq_of_val_eq heq.symm
                      subst hEqI
                      rcases hxMem with rfl | rfl | rfl <;> simp at hSyncStd
                    · right; exact Bool.eq_false_iff.mpr hS
                  have hS1x : s1.getFd x.val = s.getFd x.val := hKeep1 x.val hNotSy hNotCl
                  have hNeFd : x.val ≠ fd.val := by
                    rcases hFdRedir (by rw [hbRedirEq]; exact hR) with ⟨_, hLe, hGt⟩
                    by_cases hr2 : repW.val ≤ 2
                    · have hFdNone : s1.getFd fd.val = none := (hLe hr2).2.2
                      intro heq
                      rw [← heq, hS1x] at hFdNone
                      simp [ChildState.isOpen, hFdNone] at hxOpen
                    · have hFdEq := hGt (by omega)
                      rw [hFdEq]; exact hNeRep
                  exact hFdOther2 x.val hNeRep hNeFd |>.trans hS1x
                have hStdioImg : flagSet flags FLAG_REDIRECT_STDIO = true →
                    (∃ e0 f0, s.getFd inFd.val = some e0 ∧ execImageGetFd img 0 = some f0 ∧ f0.desc = e0.desc ∧ f0.cloexec = false) ∧
                    (∃ e1 f1, s.getFd outFd.val = some e1 ∧ execImageGetFd img 1 = some f1 ∧ f1.desc = e1.desc ∧ f1.cloexec = false) ∧
                    (∃ e2 f2, s.getFd errFd.val = some e2 ∧ execImageGetFd img 2 = some f2 ∧ f2.desc = e2.desc ∧ f2.cloexec = false) := by
                  intro hR
                  have hRb : bRedir = true := by rw [hbRedirEq]; exact hR
                  rcases hStdOpenPre hR with ⟨hOpIn, hOpOut, hOpErr⟩
                  have hRepStd := (hOvSplit.2.2.2.2 hR).2.1
                  have hSlStd := (hOvSplit.2.2.2.2 hR).2.2.1
                  rcases hStdioT3 hRb with ⟨⟨e0', f0', h0s2, h0s3, h0d, h0c⟩,
                    ⟨e1', f1', h1s2, h1s3, h1d, h1c⟩, ⟨e2', f2', h2s2, h2s3, h2d, h2c⟩, _, _⟩
                  have mkSlot : ∀ (j : Int) {f : FdEntry}, 0 ≤ j → j ≤ 2 →
                      s3.getFd j = some f → f.cloexec = false → execImageGetFd img j = some f := by
                    intro j f hj0 hj2 hjs3 hfc
                    have hjs4 : s4.getFd j = s3.getFd j :=
                      hClrNe4 j (fun kp hkp hp0 heq => hNoStdKeep hR j hj0 hj2 kp hkp hp0 heq)
                    have hjs5 : s5.getFd j = s4.getFd j := by
                      cases hUnk : bCloseUnk
                      · rw [hUnkF5 hUnk]
                      · exact (hUnkT5 hUnk).2.1 j hj0 hj2 (by rw [hjs4, hjs3]; exact Option.some_ne_none _)
                    rw [hImgFd j, hjs5, hjs4, hjs3]
                    simp [hfc]
                  refine ⟨⟨e0', f0', ?_, mkSlot 0 (by decide) (by decide) h0s3 h0c, h0d, h0c⟩,
                    ⟨e1', f1', ?_, mkSlot 1 (by decide) (by decide) h1s3 h1c, h1d, h1c⟩,
                    ⟨e2', f2', ?_, mkSlot 2 (by decide) (by decide) h2s3 h2c, h2d, h2c⟩⟩
                  · rw [← hS4Get2 inFd hR hRepStd hSlStd (Or.inl rfl) hOpIn]; exact h0s2
                  · rw [← hS4Get2 outFd hR hRepStd hSlStd (Or.inr (Or.inl rfl)) hOpOut]; exact h1s2
                  · rw [← hS4Get2 errFd hR hRepStd hSlStd (Or.inr (Or.inr rfl)) hOpErr]; exact h2s2
                have hKpNeFd : ∀ k ∈ keepFds.val, 0#i32 ≤ k → k.val ≠ fd.val := by
                  intro k hk hk0
                  have hOpK := hKpOpenPre k hk hk0
                  have hNeRep : k.val ≠ repW.val := by
                    intro heq
                    have hIn : sliceContainsNonnegSpec keepFds.val repW.val = true := by
                      rw [sliceContainsNonnegSpec, Bool.and_eq_true, List.any_eq_true]
                      exact ⟨decide_eq_true (by rw [← heq]; exact i32_val_nonneg hk0), k, hk, beq_iff_eq.mpr heq⟩
                    exact absurd hIn (by rw [hOvSplit.2.1]; decide)
                  cases hRb : bRedir
                  · rw [hFdNoRedir hRb]; exact hNeRep
                  · rcases hFdRedir hRb with ⟨_, hLe, hGt⟩
                    by_cases hr2 : repW.val ≤ 2
                    · have hFdNone := (hLe hr2).2.2
                      have hS1k : s1.getFd k.val = s.getFd k.val := by
                        have hSy : k.val ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false := by
                          by_cases hS : flagSet flags FLAG_HAS_SYNC_BARRIER = true
                          · exact Or.inl (hKeepNeSync hS k hk hk0)
                          · exact Or.inr (Bool.eq_false_iff.mpr hS)
                        exact hKeep1 k.val hSy (hKeepNeClose k hk hk0)
                      intro heq
                      rw [← heq, hS1k] at hFdNone
                      simp [ChildState.isOpen, hFdNone] at hOpK
                    · rw [hGt (by omega)]; exact hNeRep
                have hKeepImg : ∀ k ∈ keepFds.val, 0#i32 ≤ k →
                    ∃ ek fk, s.getFd k.val = some ek ∧ execImageGetFd img k.val = some fk ∧
                      fk.desc = ek.desc ∧ fk.cloexec = false := by
                  intro k hk hk0
                  have hOpK := hKpOpenPre k hk hk0
                  cases hGetK : s.getFd k.val with
                  | none => simp [ChildState.isOpen, hGetK] at hOpK
                  | some ek =>
                    have hSy : k.val ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false := by
                      by_cases hS : flagSet flags FLAG_HAS_SYNC_BARRIER = true
                      · exact Or.inl (hKeepNeSync hS k hk hk0)
                      · exact Or.inr (Bool.eq_false_iff.mpr hS)
                    have hS1k : s1.getFd k.val = some ek := (hKeep1 k.val hSy (hKeepNeClose k hk hk0)).trans hGetK
                    have hNeRep : k.val ≠ repW.val := by
                      intro heq
                      have hIn : sliceContainsNonnegSpec keepFds.val repW.val = true := by
                        rw [sliceContainsNonnegSpec, Bool.and_eq_true, List.any_eq_true]
                        exact ⟨decide_eq_true (by rw [← heq]; exact i32_val_nonneg hk0), k, hk, beq_iff_eq.mpr heq⟩
                      exact absurd hIn (by rw [hOvSplit.2.1]; decide)
                    have hS2k : s2.getFd k.val = some ek :=
                      (hFdOther2 k.val hNeRep (hKpNeFd k hk hk0)).trans hS1k
                    have hS3k : s3.getFd k.val = some ek := by
                      cases hRb : bRedir
                      · rw [hStdioF3 hRb]; exact hS2k
                      · have hR : flagSet flags FLAG_REDIRECT_STDIO = true := by rw [← hbRedirEq]; exact hRb
                        have hkGt2 : k.val > 2 := by
                          by_contra hle
                          exact hNoStdKeep hR k.val (by scalar_tac) (by omega) k hk hk0 rfl
                        have hCond : bCloseSrc = false ∨ (k.val ≠ inFd.val ∧ k.val ≠ outFd.val ∧ k.val ≠ errFd.val) := by
                          cases hCS : bCloseSrc
                          · exact Or.inl rfl
                          · exact Or.inr (hKeepNeSrc hR hCS k hk hk0)
                        exact ((hStdioT3 hRb).2.2.2.1 k.val hkGt2 hCond (by rw [hS2k]; exact Option.some_ne_none _)).trans hS2k
                    rcases hClrKp4 k hk hk0 with ⟨e3, f4, h3k, h4k, hd34, hc4⟩
                    rw [hS3k] at h3k
                    injection h3k with he3Eq
                    have hS5k : s5.getFd k.val = some f4 := by
                      cases hUnk : bCloseUnk
                      · rw [hUnkF5 hUnk]; exact h4k
                      · by_cases hk2 : k.val ≤ 2
                        · exact ((hUnkT5 hUnk).2.1 k.val (i32_val_nonneg hk0) hk2
                            (by rw [h4k]; exact Option.some_ne_none _)).trans h4k
                        · have hk3 : 3 ≤ k.val := by omega
                          have hkMax : k.val ≤ 2147483647 := i32_val_le_max k
                          have hKept : isKeptAbove2 fd keepFds.val k.val = true := by
                            simp only [isKeptAbove2, Bool.and_eq_true, decide_eq_true_eq,
                              Bool.or_eq_true, sliceContainsNonnegSpec, List.any_eq_true, beq_iff_eq]
                            exact ⟨hk3, Or.inr ⟨i32_val_nonneg hk0, k, hk, rfl⟩⟩
                          exact ((hUnkT5 hUnk).2.2.1 k.val hk3 hkMax hKept
                            (by rw [h4k]; exact Option.some_ne_none _)).trans h4k
                    refine ⟨ek, f4, rfl, ?_, hd34.trans (congrArg FdEntry.desc he3Eq.symm), hc4⟩
                    rw [hImgFd k.val, hS5k]
                    simp only [hc4, Bool.false_eq_true, ↓reduceIte]
                have hFdClosed : s4.getFd fd.val = some fRel := by
                  have hFdNotKp : ∀ kp ∈ keepFds.val, 0#i32 ≤ kp → fd.val ≠ kp.val :=
                    fun kp hkp hp0 heq => hKpNeFd kp hkp hp0 heq.symm
                  have h43 : s4.getFd fd.val = s3.getFd fd.val := hClrNe4 fd.val hFdNotKp
                  have h32 : s3.getFd fd.val = s2.getFd fd.val := by
                    cases hRb : bRedir
                    · rw [hStdioF3 hRb]
                    · have hR : flagSet flags FLAG_REDIRECT_STDIO = true := by rw [← hbRedirEq]; exact hRb
                      rcases hFdRedir hRb with ⟨hGt2, hLe, hGt⟩
                      have hCond : bCloseSrc = false ∨
                          (fd.val ≠ inFd.val ∧ fd.val ≠ outFd.val ∧ fd.val ≠ errFd.val) := by
                        right
                        have hRepStd := (hOvSplit.2.2.2.2 hR).2.1
                        have hNeRepStd : repW.val ≠ inFd.val ∧ repW.val ≠ outFd.val ∧ repW.val ≠ errFd.val := by
                          unfold fdInStdioSpec at hRepStd
                          refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
                          · have h1 := IScalar.eq_of_val_eq h; simp [h1] at hRepStd
                          · have h1 := IScalar.eq_of_val_eq h; simp [h1] at hRepStd
                          · have h1 := IScalar.eq_of_val_eq h; simp [h1] at hRepStd
                        by_cases hr2 : repW.val ≤ 2
                        · have hFdNone := (hLe hr2).2.2
                          rcases hStdOpenPre hR with ⟨hOpIn, hOpOut, hOpErr⟩
                          have hSlStd := (hOvSplit.2.2.2.2 hR).2.2.1
                          have mkNot : ∀ (x : I32),
                              (x = inFd ∨ x = outFd ∨ x = errFd) → s.isOpen x.val = true → fd.val ≠ x.val := by
                            intro x hx hxOp heq
                            have hNotCl : sliceContainsNonnegSpec closeFds x.val = false := by
                              cases hc : sliceContainsNonnegSpec closeFds x.val
                              · rfl
                              · unfold stdioInSliceSpec at hSlStd
                                rcases hx with rfl | rfl | rfl <;> simp [hc] at hSlStd
                            have hNotSy : x.val ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false := by
                              by_cases hS : flagSet flags FLAG_HAS_SYNC_BARRIER = true
                              · left; intro heqS
                                have hSyncStd := (hOvSplit.2.2.2.2 hR).2.2.2.1 hS
                                unfold fdInStdioSpec at hSyncStd
                                have hEqI : syncR = x := IScalar.eq_of_val_eq heqS.symm
                                subst hEqI
                                rcases hx with rfl | rfl | rfl <;> simp at hSyncStd
                              · right; exact Bool.eq_false_iff.mpr hS
                            have hS1x := hKeep1 x.val hNotSy hNotCl
                            rw [heq, hS1x] at hFdNone
                            simp [ChildState.isOpen, hFdNone] at hxOp
                          exact ⟨mkNot inFd (Or.inl rfl) hOpIn,
                            mkNot outFd (Or.inr (Or.inl rfl)) hOpOut,
                            mkNot errFd (Or.inr (Or.inr rfl)) hOpErr⟩
                        · rw [hGt (by omega)]; exact hNeRepStd
                      exact (hStdioT3 hRb).2.2.2.1 fd.val hGt2 hCond (by rw [hGetRel]; exact Option.some_ne_none _)
                  rw [h43, h32, hGetRel]
                have hCloseAboveImg : flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 = true →
                    ∀ k : Int, 3 ≤ k → k ≤ 2147483647 →
                      sliceContainsNonnegSpec keepFds.val k = false → execImageGetFd img k = none := by
                  intro hU k hk3 hkMax hNotKp
                  have hUb : bCloseUnk = true := by rw [hbUnkEq]; exact hU
                  have hClPost := (hUnkT5 hUb).2.2.2
                  have hKSpec := hClPost.2 k hk3 hkMax
                  rw [hImgFd k]
                  by_cases hKep : isKeptAbove2 fd keepFds.val k = true
                  · simp only [hKep, ↓reduceIte] at hKSpec
                    have hEqFd : k = fd.val := by
                      simp only [isKeptAbove2, Bool.and_eq_true, decide_eq_true_eq,
                        Bool.or_eq_true, beq_iff_eq] at hKep
                      rcases hKep.2 with ⟨_, hEq⟩ | hIn
                      · exact hEq.symm
                      · exact absurd hIn (by rw [hNotKp]; decide)
                    subst hEqFd
                    rw [hKSpec, hFdClosed]
                    simp [hCloRel]
                  · have hKepF : isKeptAbove2 fd keepFds.val k = false := Bool.eq_false_iff.mpr hKep
                    simp only [hKepF, Bool.false_eq_true, ↓reduceIte] at hKSpec
                    rw [hKSpec]
                have hExecPost : oracleHasSeccomp s.oracle = false →
                    RunChildExecPost s flags syncR inFd outFd errFd repW closeFds keepFds.val cwd? path argv envp sEx := by
                  intro hNoSec
                  have hNoSec1 : oracleHasSeccomp s1.oracle = false := by rw [hCfg1.oracle]; exact hNoSec
                  have hNoSec2 : oracleHasSeccomp s2.oracle = false := by rw [hCfg2.oracle]; exact hNoSec1
                  have hNoSec3 : oracleHasSeccomp s3.oracle = false := by rw [hCfg3.oracle]; exact hNoSec2
                  have hSig13Spec : flagSet flags FLAG_RESET_SIGPIPE = true →
                      execImageGetSig img 13 = .default ∧ img.blockedSigs = s.blockedSigs.filter (· != 13) :=
                    fun h => ⟨(hSig13R h).1, (hSig13R h).2.1⟩
                  have hRepClosed : (flagSet flags FLAG_REDIRECT_STDIO = false ∨ 2 < repW.val) →
                      execImageGetFd img repW.val = none := by
                    intro hCond
                    have hRepFdEq : fd = repW := by
                      rcases hCond with hRF | hGt2
                      · exact hFdNoRedir (by rw [hbRedirEq]; exact hRF)
                      · cases hRb : bRedir
                        · exact hFdNoRedir hRb
                        · exact (hFdRedir hRb).2.2 hGt2
                    have hS5Rep : s5.getFd repW.val = some fRel := by
                      rw [← hRepFdEq]
                      cases hUnk : bCloseUnk
                      · rw [hUnkF5 hUnk]; exact hFdClosed
                      · by_cases hfd2 : fd.val ≤ 2
                        · exact ((hUnkT5 hUnk).2.1 fd.val (by rw [hRepFdEq]; scalar_tac) hfd2
                            (by rw [hFdClosed]; exact Option.some_ne_none _)).trans hFdClosed
                        · have hKept : isKeptAbove2 fd keepFds.val fd.val = true :=
                            isKeptAbove2_self fd keepFds.val (by omega)
                          exact ((hUnkT5 hUnk).2.2.1 fd.val (by omega) (by scalar_tac) hKept
                            (by rw [hFdClosed]; exact Option.some_ne_none _)).trans hFdClosed
                    rw [hImgFd repW.val, hS5Rep]
                    simp [hCloRel]
                  have hNoRedirStdio : flagSet flags FLAG_REDIRECT_STDIO = false →
                      ∀ fd0 : Int, 0 ≤ fd0 → fd0 ≤ 2 →
                        if fd0 == repW.val || (flagSet flags FLAG_HAS_SYNC_BARRIER && fd0 == syncR.val) ||
                            sliceContainsNonnegSpec closeFds fd0 then
                          execImageGetFd img fd0 = none
                        else if sliceContainsNonnegSpec keepFds.val fd0 then
                          ∃ ek fk, s.getFd fd0 = some ek ∧ execImageGetFd img fd0 = some fk ∧
                            fk.desc = ek.desc ∧ fk.cloexec = false
                        else
                          match s.getFd fd0 with
                          | some e => execImageGetFd img fd0 = if e.cloexec then none else some e
                          | none => execImageGetFd img fd0 = none := by
                    intro hRF fd0 h0 h2
                    have hRbF : bRedir = false := by rw [hbRedirEq]; exact hRF
                    have hFdEq : fd = repW := hFdNoRedir hRbF
                    have hS5_4 : s5.getFd fd0 = s4.getFd fd0 := by
                      cases hUnk : bCloseUnk
                      · rw [hUnkF5 hUnk]
                      · exact (hUnkT5 hUnk).2.2.2.1 fd0 h0 h2
                    have hS3_2 : s3.getFd fd0 = s2.getFd fd0 := by rw [hStdioF3 hRbF]
                    by_cases hC1 : (fd0 == repW.val || (flagSet flags FLAG_HAS_SYNC_BARRIER && fd0 == syncR.val) ||
                        sliceContainsNonnegSpec closeFds fd0) = true
                    · simp only [hC1, ↓reduceIte]
                      by_cases hEqRep : fd0 = repW.val
                      · subst hEqRep
                        have hFdValEq : fd.val = repW.val := congrArg IScalar.val hFdEq
                        rw [← hFdValEq] at hS5_4 ⊢
                        rw [hImgFd fd.val, hS5_4, hFdClosed]
                        simp [hCloRel]
                      · have hNotKp : ∀ kp ∈ keepFds.val, 0#i32 ≤ kp → fd0 ≠ kp.val := by
                          intro kp hkp hp0 heq
                          have h1 : (fd0 == repW.val) = false := beq_false_of_ne hEqRep
                          simp only [h1, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hC1
                          rcases hC1 with ⟨hSyncF, rfl⟩ | hCl
                          · exact hKeepNeSync hSyncF kp hkp hp0 heq.symm
                          · have := hKeepNeClose kp hkp hp0; rw [← heq, hCl] at this; cases this
                        have hS4_2 : s4.getFd fd0 = s2.getFd fd0 := (hClrNe4 fd0 hNotKp).trans hS3_2
                        have hS2_1 : s2.getFd fd0 = s1.getFd fd0 :=
                          hFdOther2 fd0 hEqRep (by rw [hFdEq]; exact hEqRep)
                        have h1 : (fd0 == repW.val) = false := beq_false_of_ne hEqRep
                        simp only [h1, Bool.false_or] at hC1
                        have hS1None : s1.getFd fd0 = none := by
                          rw [hSec1 hNoSec fd0]
                          rw [Bool.or_comm] at hC1
                          simp [hC1]
                        rw [hImgFd fd0, hS5_4, hS4_2, hS2_1, hS1None]
                    · have hC1F : (fd0 == repW.val || (flagSet flags FLAG_HAS_SYNC_BARRIER && fd0 == syncR.val) ||
                          sliceContainsNonnegSpec closeFds fd0) = false := Bool.eq_false_iff.mpr hC1
                      simp only [hC1F, Bool.false_eq_true, ↓reduceIte]
                      by_cases hC2 : sliceContainsNonnegSpec keepFds.val fd0 = true
                      · simp only [hC2, ↓reduceIte]
                        simp only [sliceContainsNonnegSpec, Bool.and_eq_true, decide_eq_true_eq,
                          List.any_eq_true, beq_iff_eq] at hC2
                        rcases hC2 with ⟨hk0, kp, hkp, rfl⟩
                        exact hKeepImg kp hkp (i32_nonneg_of_val hk0)
                      · have hC2F : sliceContainsNonnegSpec keepFds.val fd0 = false :=
                          Bool.eq_false_iff.mpr hC2
                        simp only [hC2F, Bool.false_eq_true, ↓reduceIte]
                        have hNotKp : ∀ kp ∈ keepFds.val, 0#i32 ≤ kp → fd0 ≠ kp.val := by
                          intro kp hkp hp0 heq
                          have hMem : sliceContainsNonnegSpec keepFds.val fd0 = true := by
                            rw [sliceContainsNonnegSpec, Bool.and_eq_true, List.any_eq_true]
                            exact ⟨decide_eq_true h0, kp, hkp, beq_iff_eq.mpr heq.symm⟩
                          rw [hMem] at hC2F; cases hC2F
                        simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hC1F
                        have hNeRep : fd0 ≠ repW.val := hC1F.1.1
                        have hNotSy : fd0 ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false := by
                          rcases hC1F.1.2 with hF | hNe
                          · exact Or.inr hF
                          · exact Or.inl hNe
                        have hS2_1 : s2.getFd fd0 = s1.getFd fd0 :=
                          hFdOther2 fd0 hNeRep (by rw [hFdEq]; exact hNeRep)
                        have hS1_0 : s1.getFd fd0 = s.getFd fd0 := hKeep1 fd0 hNotSy hC1F.2
                        rw [hImgFd fd0, hS5_4, hClrNe4 fd0 hNotKp, hS3_2, hS2_1, hS1_0]
                        cases s.getFd fd0 <;> rfl
                  have hNoCloseAbove2 : flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 = false →
                      ∀ k : Int, k > 2 →
                        if k == repW.val || (flagSet flags FLAG_HAS_SYNC_BARRIER && k == syncR.val) ||
                            sliceContainsNonnegSpec closeFds k ||
                            (flagSet flags FLAG_CLOSE_STDIO_SOURCES &&
                              (k == inFd.val || k == outFd.val || k == errFd.val)) then
                          execImageGetFd img k = none
                        else if sliceContainsNonnegSpec keepFds.val k then
                          ∃ ek fk, s.getFd k = some ek ∧ execImageGetFd img k = some fk ∧
                            fk.desc = ek.desc ∧ fk.cloexec = false
                        else
                          match s.getFd k with
                          | some e => execImageGetFd img k = if e.cloexec then none else some e
                          | none => execImageGetFd img k = none := by
                    intro hUF k hk2
                    have hUbF : bCloseUnk = false := by rw [hbUnkEq]; exact hUF
                    have hS5_4 : s5 = s4 := hUnkF5 hUbF
                    have hS3Spec : s3.getFd k =
                        if flagSet flags FLAG_REDIRECT_STDIO && flagSet flags FLAG_CLOSE_STDIO_SOURCES &&
                            (k == inFd.val || k == outFd.val || k == errFd.val) then
                          none
                        else s2.getFd k := by
                      cases hRb : bRedir
                      · have hRF : flagSet flags FLAG_REDIRECT_STDIO = false := by
                          rw [← hbRedirEq]; exact hRb
                        simp [hRF, hStdioF3 hRb]
                      · have hRT : flagSet flags FLAG_REDIRECT_STDIO = true := by
                          rw [← hbRedirEq]; exact hRb
                        have hStdPost := (hStdioT3 hRb).2.2.2.2 hNoSec2
                        have hkStd := hStdPost.2.2.2 k hk2
                        rw [hRT, Bool.true_and, ← hbSrcEq]
                        exact hkStd
                    have hCondEq : (flagSet flags FLAG_REDIRECT_STDIO && flagSet flags FLAG_CLOSE_STDIO_SOURCES &&
                        (k == inFd.val || k == outFd.val || k == errFd.val)) =
                        (flagSet flags FLAG_CLOSE_STDIO_SOURCES &&
                          (k == inFd.val || k == outFd.val || k == errFd.val)) := by
                      cases hCS : flagSet flags FLAG_CLOSE_STDIO_SOURCES
                      · simp
                      · have hR := (hFlSplit hCS).1; simp [hR]
                    rw [hCondEq] at hS3Spec
                    by_cases hC1 : (k == repW.val || (flagSet flags FLAG_HAS_SYNC_BARRIER && k == syncR.val) ||
                        sliceContainsNonnegSpec closeFds k ||
                        (flagSet flags FLAG_CLOSE_STDIO_SOURCES &&
                          (k == inFd.val || k == outFd.val || k == errFd.val))) = true
                    · simp only [hC1, ↓reduceIte]
                      by_cases hEqRep : k = repW.val
                      · subst hEqRep
                        have hRepClosed' := hRepClosed (Or.inr hk2)
                        exact hRepClosed'
                      · by_cases hEqFd : k = fd.val
                        · subst hEqFd
                          rw [hImgFd fd.val, hS5_4, hFdClosed]
                          simp [hCloRel]
                        · have hNotKp : ∀ kp ∈ keepFds.val, 0#i32 ≤ kp → k ≠ kp.val := by
                            intro kp hkp hp0 heq
                            have hEqRepB : (k == repW.val) = false := beq_false_of_ne hEqRep
                            simp only [hEqRepB, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
                              beq_iff_eq] at hC1
                            rcases hC1 with (⟨hSy, rfl⟩ | hCl) | ⟨hCS, hStdM⟩
                            · exact hKeepNeSync hSy kp hkp hp0 heq.symm
                            · have := hKeepNeClose kp hkp hp0; rw [← heq, hCl] at this; cases this
                            · have hR := (hFlSplit hCS).1
                              have hNeSrc := hKeepNeSrc hR (by rw [hbSrcEq]; exact hCS) kp hkp hp0
                              subst heq
                              rcases hStdM with (h1 | h2) | h3
                              · exact hNeSrc.1 h1
                              · exact hNeSrc.2.1 h2
                              · exact hNeSrc.2.2 h3
                          have hS4_3 := hClrNe4 k hNotKp
                          have hS2_1 := hFdOther2 k hEqRep hEqFd
                          have hEqRepB : (k == repW.val) = false := beq_false_of_ne hEqRep
                          simp only [hEqRepB, Bool.false_or] at hC1
                          have hS3None : s3.getFd k = none := by
                            rw [hS3Spec]
                            split
                            · rfl
                            · next hNStd =>
                              have hNStdF : (flagSet flags FLAG_CLOSE_STDIO_SOURCES &&
                                  (k == inFd.val || k == outFd.val || k == errFd.val)) = false :=
                                Bool.eq_false_iff.mpr hNStd
                              rw [hNStdF, Bool.or_false] at hC1
                              rw [hS2_1, hSec1 hNoSec k, Bool.or_comm]
                              simp [hC1]
                          rw [hImgFd k, hS5_4, hS4_3, hS3None]
                    · have hC1F : (k == repW.val || (flagSet flags FLAG_HAS_SYNC_BARRIER && k == syncR.val) ||
                          sliceContainsNonnegSpec closeFds k ||
                          (flagSet flags FLAG_CLOSE_STDIO_SOURCES &&
                            (k == inFd.val || k == outFd.val || k == errFd.val))) = false :=
                        Bool.eq_false_iff.mpr hC1
                      simp only [hC1F, Bool.false_eq_true, ↓reduceIte]
                      by_cases hC2 : sliceContainsNonnegSpec keepFds.val k = true
                      · simp only [hC2, ↓reduceIte]
                        simp only [sliceContainsNonnegSpec, Bool.and_eq_true, decide_eq_true_eq,
                          List.any_eq_true, beq_iff_eq] at hC2
                        rcases hC2 with ⟨hk0, kp, hkp, rfl⟩
                        exact hKeepImg kp hkp (i32_nonneg_of_val hk0)
                      · have hC2F : sliceContainsNonnegSpec keepFds.val k = false :=
                          Bool.eq_false_iff.mpr hC2
                        simp only [hC2F, Bool.false_eq_true, ↓reduceIte]
                        have hNotKp : ∀ kp ∈ keepFds.val, 0#i32 ≤ kp → k ≠ kp.val := by
                          intro kp hkp hp0 heq
                          have hMem : sliceContainsNonnegSpec keepFds.val k = true := by
                            rw [sliceContainsNonnegSpec, Bool.and_eq_true, List.any_eq_true]
                            exact ⟨decide_eq_true (by omega), kp, hkp, beq_iff_eq.mpr heq.symm⟩
                          rw [hMem] at hC2F; cases hC2F
                        simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hC1F
                        have hNeRep : k ≠ repW.val := hC1F.1.1.1
                        have hNotSy : k ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false := by
                          rcases hC1F.1.1.2 with hF | hNe
                          · exact Or.inr hF
                          · exact Or.inl hNe
                        have hNotCl : sliceContainsNonnegSpec closeFds k = false := hC1F.1.2
                        have hNotSrc : (flagSet flags FLAG_CLOSE_STDIO_SOURCES &&
                            (k == inFd.val || k == outFd.val || k == errFd.val)) = false := by
                          rcases hC1F.2 with hF | hNe
                          · rw [hF]; rfl
                          · rw [Bool.and_eq_false_iff]; right
                            rcases hNe with ⟨⟨h1, h2⟩, h3⟩
                            simp [beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h3]
                        simp only [hNotSrc, Bool.false_eq_true, ↓reduceIte] at hS3Spec
                        by_cases hEqFd : k = fd.val
                        · subst hEqFd
                          have hIsNoneS : s.getFd fd.val = none := by
                            cases hRb : bRedir
                            · exact absurd (hFdNoRedir hRb ▸ rfl) hNeRep
                            · rcases hFdRedir hRb with ⟨_, hLe, hGt⟩
                              by_cases hr2 : repW.val ≤ 2
                              · have hS1None := (hLe hr2).2.2
                                rwa [hKeep1 fd.val hNotSy hNotCl] at hS1None
                              · exact absurd (hGt (by omega) ▸ rfl) hNeRep
                          rw [hIsNoneS, hImgFd fd.val, hS5_4, hFdClosed]
                          simp [hCloRel]
                        · have hS2_1 := hFdOther2 k hNeRep hEqFd
                          have hS1_0 := hKeep1 k hNotSy hNotCl
                          rw [hImgFd k, hS5_4, hClrNe4 k hNotKp, hS3Spec, hS2_1, hS1_0]
                          cases s.getFd k <;> rfl
                  exact ⟨img, hExStatus, hWrEx, hCls, rfl, rfl, rfl, hPgidImg, hCwdImg, hSig13Spec,
                    hSig13F, hSigOth, hRepClosed, hStdioImg, hNoRedirStdio, hKeepImg, hCloseAboveImg,
                    hNoCloseAbove2⟩
                exact Or.inr (Or.inr ⟨hExecPost, img, hExStatus, hWrEx, hCls, rfl, rfl, rfl, hCwdImg,
                  (fun h => ⟨(hSig13R h).1, (hSig13R h).2.2⟩), hSigOth, hStdioImg, hKeepImg,
                  hCloseAboveImg⟩)
          cases cwd? with
          | none =>
            exact finishExec s5 hRun5 hCfg50 rfl hWl5S hSig5S hBlk5S (fun _ => rfl) (traceExtends_refl s5)
              (fun _ => hCw5S) (fun _ h => by cases h)
          | some dir =>
            change OkPost (do
              let (rCh, s6) ← sys.chdir s5 dir
              match rCh with
              | .Ok _ => do
                let (e, sExec) ← sys.execve s6 path argv envp
                postfork.child.report_and_exit sExec fd postfork.child.STAGE_EXECVE e postfork.child.ENOENT
              | .Err e => postfork.child.report_and_exit s6 fd postfork.child.STAGE_CHDIR e postfork.fd_ops.EIO) _
            obtain ⟨rCh, s6, hChEq, hCfg6, _, _, hSig6, hWl6, hPg6, _, hCwErr6, hCwOk6, _⟩ :=
              sys_chdir_running s5 hRun5 dir
            rw [hChEq, bind_ok]
            have hRun6 : s6.status = .running := hCfg6.status.trans hRun5
            have hTr56 : TraceExtends s5 s6 := sys_chdir_trace_eq s5 hRun5 dir hChEq
            cases rCh with
            | Err e => exact h127 s6 hRun6 fd _ e _
            | Ok _ =>
              have hFds6 : ∀ k, s6.getFd k = s5.getFd k := by
                intro k; unfold ChildState.getFd
                have : s6.fds = s5.fds := by
                  unfold sys.chdir runUnitSyscall at hChEq
                  rw [hRun5] at hChEq
                  dsimp only [id] at hChEq
                  cases hf : currentFault s5 with
                  | seccomp _ =>
                    simp only [hf, Result.ok.injEq, Prod.mk.injEq] at hChEq
                    cases hChEq.1
                  | fail _ =>
                    simp only [hf] at hChEq
                    cases hemp : dir.isEmpty
                    · simp only [hemp, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at hChEq
                      rw [← hChEq.2]
                    · simp only [hemp, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at hChEq
                      cases hChEq.1
                  | normal | partialWrite _ | dentsBatch _ =>
                    simp only [hf] at hChEq
                    cases hemp : dir.isEmpty
                    · simp only [hemp, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at hChEq
                      rw [← hChEq.2]
                    · simp only [hemp, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at hChEq
                      cases hChEq.1
                rw [this]
              have hBlk6 : s6.blockedSigs = s5.blockedSigs :=
                dspec_of_ok (sys_chdir_dspec_blockedSigs s5 dir) hChEq
              have hCwRes : s6.cwd = resolveChdirTarget s dir := by
                rw [hCwOk6 rfl]
                simp [resolveChdirTarget, hCw5S, hCfg50.chdirResolved]
              exact finishExec s6 hRun6 (hCfg6.trans hCfg50) hPg6 (hWl6.trans hWl5S)
                (hSig6.trans hSig5S) (hBlk6.trans hBlk5S) hFds6 hTr56
                (fun h => by cases h) (fun d hd => by cases hd; exact hCwRes)

/-- Arbitrary-oracle safety theorem for `postfork.child.run_child` from any running state. -/
theorem run_child_safety_core
    (s : ChildState) (hRun : s.status = .running)
    (flags : U32) (syncR inFd outFd errFd repW : I32)
    (closeFds keepFds : Slice I32)
    (cwd? : Option sys.CStr) (path : sys.CStr) (argv envp : sys.CStrArray) :
    OkPost
      (postfork.child.run_child s { flags := flags, sync_r := syncR, stdin_fd := inFd, stdout_fd := outFd, stderr_fd := errFd, rep_w := repW } closeFds keepFds { cwd := cwd?, path := path, argv := argv, envp := envp })
      (RunChildSafetyPost s flags syncR inFd outFd errFd repW closeFds.val keepFds.val cwd? path argv envp) := by
  unfold postfork.child.run_child
  refine okPost_bind
    (run_child_pre_sync_safety s hRun flags syncR inFd outFd errFd repW closeFds keepFds)
    fun (b, s1) hb => ?_
  cases b
  · exact okPost_ok _ _ (hb.elim Or.inl (fun h => Or.inr (Or.inl h)))
  · exact run_child_post_sync_safety s s1 flags syncR inFd outFd errFd repW closeFds.val keepFds cwd? path argv envp hb

/-- Totality of `postfork.child.run_child` across all `ChildState`s and inputs. -/
theorem run_child_total
    (s : ChildState) (flags : U32) (syncR inFd outFd errFd repW : I32)
    (closeFds keepFds : Slice I32)
    (cwd? : Option sys.CStr) (path : sys.CStr) (argv envp : sys.CStrArray) :
    OkPost
      (postfork.child.run_child s { flags := flags, sync_r := syncR, stdin_fd := inFd, stdout_fd := outFd, stderr_fd := errFd, rep_w := repW } closeFds keepFds { cwd := cwd?, path := path, argv := argv, envp := envp })
      (fun _ => True) := by
  unfold postfork.child.run_child
  refine okPost_bind (run_child_pre_sync_total s flags syncR inFd outFd errFd repW closeFds keepFds)
    fun (b, s1) _ => ?_
  cases b
  · exact okPost_ok _ _ trivial
  · unfold postfork.child.run_child_post_sync
    simp only [lift, Aeneas.Std.lift, bind_ok]
    have hPrepTot : ∀ x rd, OkPost (postfork.child.prepare_rep_w x rd repW) (fun _ => True) := fun x rd => by
      unfold postfork.child.prepare_rep_w
      cases rd
      · exact okPost_bind (set_cloexec_total x repW) fun (r, _) _ => by cases r <;> exact ⟨_, rfl, trivial⟩
      · exact okPost_mono (relocate_rep_above2_total x repW) fun _ _ => trivial
    have hRedirTot : ∀ x rd cs, OkPost (postfork.child.apply_redir_stdio x rd inFd outFd errFd cs) (fun _ => True) :=
      fun x rd cs => by
        unfold postfork.child.apply_redir_stdio
        cases rd
        · exact ⟨_, rfl, trivial⟩
        · exact okPost_mono (setup_stdio_total x inFd outFd errFd cs) fun _ _ => trivial
    have hUnkTot : ∀ x cu fd, OkPost (postfork.child.apply_close_unkept x cu fd keepFds) (fun _ => True) :=
      fun x cu fd => by
        unfold postfork.child.apply_close_unkept
        cases cu
        · exact ⟨_, rfl, trivial⟩
        · exact okPost_mono (close_fds_above2_except_total x fd keepFds) fun _ _ => trivial
    have hChdirTot : ∀ x d, OkPost (sys.chdir x d) (fun _ => True) := fun x d => by
      by_cases hRun : x.status = .running
      · obtain ⟨r, x', hEq, _⟩ := sys_chdir_running x hRun d; exact ⟨(r, x'), hEq, trivial⟩
      · unfold sys.chdir; rw [runUnitSyscall_not_running x hRun]; exact ⟨_, rfl, trivial⟩
    have hExecTot : ∀ x, OkPost (sys.execve x path argv envp) (fun _ => True) := fun x => by
      by_cases hRun : x.status = .running
      · obtain ⟨e, x', hEq, _⟩ := sys_execve_running x hRun path argv envp; exact ⟨(e, x'), hEq, trivial⟩
      · rw [sys_execve_not_running x hRun]; exact ⟨_, rfl, trivial⟩
    refine okPost_bind (hPrepTot s1 _) fun (r1, s2) _ => ?_
    cases r1 with
    | Err _ => exact okPost_mono (report_and_exit_total s2 repW _ _ _) fun _ _ => trivial
    | Ok fd =>
      refine okPost_bind (hRedirTot s2 _ _) fun (r2, s3) _ => ?_
      cases r2 with
      | Err _ => exact okPost_mono (report_and_exit_total s3 fd _ _ _) fun _ _ => trivial
      | Ok _ =>
        refine okPost_bind (clear_cloexec_slice_total s3 keepFds) fun (r3, s4) _ => ?_
        cases r3 with
        | Err _ => exact okPost_mono (report_and_exit_total s4 fd _ _ _) fun _ _ => trivial
        | Ok _ =>
          refine okPost_bind (hUnkTot s4 _ fd) fun (r4, s5) _ => ?_
          cases r4 with
          | Err _ => exact okPost_mono (report_and_exit_total s5 fd _ _ _) fun _ _ => trivial
          | Ok _ =>
            cases cwd? with
            | none =>
              refine okPost_bind (hExecTot s5) fun (e, s6) _ => ?_
              exact okPost_mono (report_and_exit_total s6 fd _ _ _) fun _ _ => trivial
            | some dir =>
              refine okPost_bind (hChdirTot s5 dir) fun (r5, s6) _ => ?_
              cases r5 with
              | Err _ => exact okPost_mono (report_and_exit_total s6 fd _ _ _) fun _ _ => trivial
              | Ok _ =>
                refine okPost_bind (hExecTot s6) fun (e, s7) _ => ?_
                exact okPost_mono (report_and_exit_total s7 fd _ _ _) fun _ _ => trivial

private theorem run_child_free_fd_after_setup
    (s s1 s2 s3 s4 : ChildState) (flags : U32) (syncR inFd outFd errFd repW fd : I32)
    (closeFds keepFds : List I32)
    (hSlack : min s.fdLimit 2147483648 ≥ minRunChildFdSlack flags + Int.ofNat s.fds.length)
    (hFl4 : s4.fdLimit = s.fdLimit)
    (hSec1 : oracleHasSeccomp s.oracle = false → ∀ k : Int,
      s1.getFd k =
        if sliceContainsNonnegSpec closeFds k || (flagSet flags FLAG_HAS_SYNC_BARRIER && k == syncR.val)
        then none else s.getFd k)
    (hNoSec : oracleHasSeccomp s.oracle = false)
    (hOther2 : ∀ k, k ≠ repW.val → k ≠ fd.val → s2.getFd k = s1.getFd k)
    (hStdioT3 : flagSet flags FLAG_REDIRECT_STDIO = true → SetupStdioPost s2 inFd outFd errFd (flagSet flags FLAG_CLOSE_STDIO_SOURCES) s3)
    (hStdioF3 : flagSet flags FLAG_REDIRECT_STDIO = false → s3 = s2)
    (hClrNe4 : ∀ k : Int, (∀ kp ∈ keepFds, 0#i32 ≤ kp → k ≠ kp.val) → s4.getFd k = s3.getFd k)
    (hOpKp : ∀ kp ∈ keepFds, 0#i32 ≤ kp → s.isOpen kp.val = true)
    (hFdRedir : flagSet flags FLAG_REDIRECT_STDIO = true → 2 < repW.val → fd = repW)
    (hFdNoRedir : flagSet flags FLAG_REDIRECT_STDIO = false → fd = repW) :
    ∃ dirfd, findLowestFreeFd s4 0 = some dirfd := by
  by_cases hR : flagSet flags FLAG_REDIRECT_STDIO = true
  · have hSlack6 : min s4.fdLimit 2147483648 ≥ 6 + Int.ofNat s.fds.length := by
      have hm : minRunChildFdSlack flags = 6 := by simp [minRunChildFdSlack, hR]
      rw [hFl4, ← hm]; exact hSlack
    refine findLowestFreeFd_after_setupStdio s s4 fd.val hSlack6 fun x _ hOpx => ?_
    by_cases hx02 : x = 0 ∨ x = 1 ∨ x = 2
    · rcases hx02 with rfl | rfl | rfl <;> simp
    · have hx2 : x > 2 := by omega
      by_cases hxFd : x = fd.val
      · exact Or.inr (Or.inr (Or.inr (Or.inl hxFd)))
      · right; right; right; right
        by_cases hKp : ∃ kp ∈ keepFds, 0#i32 ≤ kp ∧ x = kp.val
        · rcases hKp with ⟨kp, hkp, hp0, rfl⟩; exact hOpKp kp hkp hp0
        · have hx43 := hClrNe4 x (fun kp hkp hp0 heq => hKp ⟨kp, hkp, hp0, heq⟩)
          have hx32 : s3.getFd x = if flagSet flags FLAG_CLOSE_STDIO_SOURCES &&
              (x == inFd.val || x == outFd.val || x == errFd.val) then none else s2.getFd x :=
            (hStdioT3 hR).2.2.2 x hx2
          rw [ChildState.isOpen, hx43, hx32] at hOpx
          cases hCS : (flagSet flags FLAG_CLOSE_STDIO_SOURCES &&
              (x == inFd.val || x == outFd.val || x == errFd.val))
          · simp only [hCS, Bool.false_eq_true, ↓reduceIte] at hOpx
            have hxNeRep : x ≠ repW.val := by
              intro hEq
              have hGt2 : 2 < repW.val := by omega
              have hFdEq := hFdRedir hR hGt2
              apply hxFd; rw [hEq, hFdEq]
            rw [hOther2 x hxNeRep hxFd, hSec1 hNoSec x] at hOpx
            split at hOpx
            · simp at hOpx
            · exact hOpx
          · simp [hCS] at hOpx
  · have hRF : flagSet flags FLAG_REDIRECT_STDIO = false := Bool.eq_false_iff.mpr hR
    have hFdEq := hFdNoRedir hRF
    have hSlack4 : min s4.fdLimit 2147483648 ≥ 4 + Int.ofNat s.fds.length := by
      have hm : minRunChildFdSlack flags = 4 := by simp [minRunChildFdSlack, hRF]
      rw [hFl4, ← hm]; exact hSlack
    refine findLowestFreeFd_some_of_card_lt s4 0 (repW.val :: s.fds.map Prod.fst) (le_refl 0) ?_ ?_
    · simp only [List.length_cons, List.length_map, Int.ofNat_eq_natCast, Nat.cast_add] at hSlack4 ⊢
      omega
    · intro x _ hOpx
      by_cases hxRep : x = repW.val
      · rw [hxRep]; exact List.mem_cons_self
      · right
        by_cases hKp : ∃ kp ∈ keepFds, 0#i32 ≤ kp ∧ x = kp.val
        · rcases hKp with ⟨kp, hkp, hp0, rfl⟩
          have hkOp := hOpKp kp hkp hp0
          rw [ChildState.isOpen, ChildState.getFd] at hkOp
          cases hfind : s.fds.find? (fun p => p.1 == kp.val) with
          | none => rw [hfind] at hkOp; simp at hkOp
          | some p =>
            have hfst : p.1 = kp.val := beq_iff_eq.mp (List.find?_some (p := fun q : Int × FdEntry => q.1 == kp.val) hfind)
            exact hfst ▸ List.mem_map.mpr ⟨p, List.mem_of_find?_eq_some hfind, rfl⟩
        · have hx43 := hClrNe4 x (fun kp hkp hp0 heq => hKp ⟨kp, hkp, hp0, heq⟩)
          have hx32 : s3.getFd x = s2.getFd x := by rw [hStdioF3 hRF]
          have hx21 : s2.getFd x = s1.getFd x := hOther2 x hxRep (by rw [hFdEq]; exact hxRep)
          rw [ChildState.isOpen, hx43, hx32, hx21, hSec1 hNoSec x] at hOpx
          cases hc : (sliceContainsNonnegSpec closeFds x || (flagSet flags FLAG_HAS_SYNC_BARRIER && x == syncR.val))
          · simp only [hc, Bool.false_eq_true, ↓reduceIte, ChildState.getFd] at hOpx
            cases hfind : s.fds.find? (fun p => p.1 == x) with
            | none => rw [hfind] at hOpx; simp at hOpx
            | some p =>
              have hfst : p.1 = x := beq_iff_eq.mp (List.find?_some (p := fun q : Int × FdEntry => q.1 == x) hfind)
              exact hfst ▸ List.mem_map.mpr ⟨p, List.mem_of_find?_eq_some hfind, rfl⟩
          · simp [hc] at hOpx

private theorem rc_stage_close_unkept_eq : postfork.child.STAGE_CLOSE_UNKEPT = 5#u8 := by
  unfold postfork.child.STAGE_CLOSE_UNKEPT; rfl
private theorem rc_stage_chdir_eq : postfork.child.STAGE_CHDIR = 6#u8 := by
  unfold postfork.child.STAGE_CHDIR; rfl
private theorem rc_stage_execve_eq : postfork.child.STAGE_EXECVE = 7#u8 := by
  unfold postfork.child.STAGE_EXECVE; rfl
private theorem rc_enoent_eq : postfork.child.ENOENT = ENOENT := by
  unfold postfork.child.ENOENT ENOENT; rfl

private theorem normalizeErrnoSpec_sanitizeErrno (e : I32) :
    normalizeErrnoSpec (sanitizeErrno e) postfork.fd_ops.EIO = sanitizeErrno e := by
  have hb := sanitizeErrno_bounds e
  unfold normalizeErrnoSpec
  have hgt : sanitizeErrno e > 0#i32 := by scalar_tac
  simp [hgt]

private theorem normalizeErrnoSpec_enoent :
    normalizeErrnoSpec ENOENT postfork.fd_ops.EIO = ENOENT := by
  unfold normalizeErrnoSpec ENOENT; decide

private theorem run_child_post_sync_after_setup
    (s s1 : ChildState)
    (flags : U32) (syncR inFd outFd errFd repW : I32)
    (closeFds : List I32) (keepFds : Slice I32)
    (cwd? : Option sys.CStr) (path : sys.CStr) (argv envp : sys.CStrArray)
    (hOr : s.oracle = [])
    (hPre : PreSyncOkPost s flags syncR inFd outFd errFd repW closeFds keepFds.val s1)
    (hOpRep : s.isOpen repW.val = true)
    (hSlack : min s.fdLimit 2147483648 ≥ minRunChildFdSlack flags + Int.ofNat s.fds.length)
    (P : ChildState → Prop)
    (hCont : ∀ (fd : I32) (s4 : ChildState) (fRel : FdEntry),
      s4.status = .running →
      s4.oracle = [] →
      SameChildConfig s4 s →
      s4.descs = s1.descs →
      s4.writeLog = s.writeLog →
      (∃ eRep, s.getFd repW.val = some eRep ∧ s4.getFd fd.val = some fRel ∧
        fRel.desc = eRep.desc ∧ fRel.cloexec = true) →
      (∃ dirfd, findLowestFreeFd s4 0 = some dirfd) →
      0#i32 ≤ fd →
      OkPost (do
        let (r4, s5) ← postfork.child.apply_close_unkept s4 (flags &&& FLAG_CLOSE_UNKEPT_ABOVE2 != 0#u32) fd keepFds
        match r4 with
        | .Ok _ =>
          match cwd? with
          | none =>
            let (e, sExec) ← sys.execve s5 path argv envp
            postfork.child.report_and_exit sExec fd postfork.child.STAGE_EXECVE e postfork.child.ENOENT
          | some dir =>
            let (rCh, s6) ← sys.chdir s5 dir
            match rCh with
            | .Ok _ =>
              let (e, sExec) ← sys.execve s6 path argv envp
              postfork.child.report_and_exit sExec fd postfork.child.STAGE_EXECVE e postfork.child.ENOENT
            | .Err e =>
              postfork.child.report_and_exit s6 fd postfork.child.STAGE_CHDIR e postfork.fd_ops.EIO
        | .Err e =>
          postfork.child.report_and_exit s5 fd postfork.child.STAGE_CLOSE_UNKEPT e postfork.fd_ops.EIO) P) :
    OkPost
      (postfork.child.run_child_post_sync s1 { flags := flags, sync_r := syncR, stdin_fd := inFd, stdout_fd := outFd, stderr_fd := errFd, rep_w := repW } keepFds { cwd := cwd?, path := path, argv := argv, envp := envp })
      P := by
  have hRun1 := hPre.1
  have hCfg1 := hPre.2.1
  have hWl1 := hPre.2.2.1
  have hFlT := hPre.2.2.2.2.1
  have hRepGe := hPre.2.2.2.2.2.1
  have hSgT := hPre.2.2.2.2.2.2.1
  have hOvT := hPre.2.2.2.2.2.2.2.1
  have hNoSec : oracleHasSeccomp s.oracle = false := by simp [oracleHasSeccomp, hOr]
  have hLen1 : s1.fds.length ≤ s.fds.length := hPre.2.2.2.2.2.2.2.2.1 hNoSec
  have hKeep1 := hPre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSec1 := hPre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hStdOpenPre := hPre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hKpOpenPre := hPre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFlSplit := validFlagsSpec_split hFlT
  have hOvSplit := validRunChildNoOverlap_split hOvT
  have hOr1 : s1.oracle = [] := hCfg1.oracle.trans hOr
  have hRepNotSy : repW.val ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false := by
    by_cases hS : flagSet flags FLAG_HAS_SYNC_BARRIER = true
    · left; exact fun h => (hOvSplit.2.2.2.1 hS).1 (IScalar.eq_of_val_eq h)
    · right; exact Bool.eq_false_iff.mpr hS
  have hS1RepEq : s1.getFd repW.val = s.getFd repW.val := hKeep1 repW.val hRepNotSy hOvSplit.1
  have hRepOpen1 : s1.isOpen repW.val = true := by
    simpa [ChildState.isOpen, hS1RepEq] using hOpRep
  have hLim6 : flagSet flags FLAG_REDIRECT_STDIO = true → min s1.fdLimit 2147483648 ≥ 6 + Int.ofNat s1.fds.length := by
    intro hR
    have hm : minRunChildFdSlack flags = 6 := by simp [minRunChildFdSlack, hR]
    have hLen1' : Int.ofNat s1.fds.length ≤ Int.ofNat s.fds.length := Int.ofNat_le.mpr hLen1
    rw [hm] at hSlack
    rw [hCfg1.fdLimit]; omega
  unfold postfork.child.run_child_post_sync
  simp only [rc_flag_redirect_stdio_eq, rc_flag_close_unkept_eq, rc_flag_close_stdio_eq,
    lift, Aeneas.Std.lift, bind_ok]
  let bRedir := (flags &&& FLAG_REDIRECT_STDIO != 0#u32)
  let bCloseUnk := (flags &&& FLAG_CLOSE_UNKEPT_ABOVE2 != 0#u32)
  let bCloseSrc := (flags &&& FLAG_CLOSE_STDIO_SOURCES != 0#u32)
  have hbRedirEq : bRedir = flagSet flags FLAG_REDIRECT_STDIO := rfl
  have hbSrcEq : bCloseSrc = flagSet flags FLAG_CLOSE_STDIO_SOURCES := rfl
  refine okPost_bind
    (okPost_and (prepare_rep_w_safety s1 hRun1 bRedir repW)
      (prepare_rep_w_ok_of_open s1 hRun1 hOr1 bRedir repW hRepGe hRepOpen1
        (fun hRb => hLim6 (by rw [← hbRedirEq]; exact hRb))))
    fun (r1, s2) ⟨⟨_, _, _, _, _, _, _, _, _, hRepSafeOk⟩,
      ⟨fd, hr1Eq, hRun2, hCfg2, _, _, _, hDe2, hWl2, hLen2, hFdNoRedir⟩⟩ => ?_
  rw [hr1Eq]
  rcases hRepSafeOk fd hr1Eq with ⟨hFdRedir, _, ⟨eRep1, fRel, hE1, hGetRel, hDescRel, hCloRel⟩, hOther2⟩
  rw [hS1RepEq] at hE1
  have hOr2 : s2.oracle = [] := hCfg2.oracle.trans hOr1
  have hCfg20 : SameChildConfig s2 s := hCfg2.trans hCfg1
  have hSignsRedir : bRedir = true → 0#i32 ≤ inFd ∧ 0#i32 ≤ outFd ∧ 0#i32 ≤ errFd := by
    intro hRb
    have hR : flagSet flags FLAG_REDIRECT_STDIO = true := by rw [← hbRedirEq]; exact hRb
    have hSgR := (Bool.and_eq_true _ _ |>.mp hSgT).2
    simp only [Bool.or_eq_true, Bool.not_eq_true', hR, Bool.and_eq_true,
      decide_eq_true_eq] at hSgR
    rcases hSgR with hImp | ⟨⟨h1, h2⟩, h3⟩
    · cases hImp
    · exact ⟨h1, h2, h3⟩
  have hGetS2Std : ∀ (x : I32), flagSet flags FLAG_REDIRECT_STDIO = true →
      (x = inFd ∨ x = outFd ∨ x = errFd) → s.isOpen x.val = true →
      s2.getFd x.val = s.getFd x.val := by
    intro x hR hxMem hxOpen
    have hRb : bRedir = true := by rw [hbRedirEq]; exact hR
    have hRepStd := (hOvSplit.2.2.2.2 hR).2.1
    have hSlStd := (hOvSplit.2.2.2.2 hR).2.2.1
    have hNeRep : x.val ≠ repW.val := by
      intro heq
      unfold fdInStdioSpec at hRepStd
      have hEqI : repW = x := IScalar.eq_of_val_eq heq.symm
      subst hEqI
      rcases hxMem with rfl | rfl | rfl <;> simp at hRepStd
    have hNotCl : sliceContainsNonnegSpec closeFds x.val = false := by
      cases hc : sliceContainsNonnegSpec closeFds x.val
      · rfl
      · unfold stdioInSliceSpec at hSlStd
        rcases hxMem with rfl | rfl | rfl <;> simp [hc] at hSlStd
    have hNotSy : x.val ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false := by
      by_cases hS : flagSet flags FLAG_HAS_SYNC_BARRIER = true
      · left; intro heq
        have hSyncStd := (hOvSplit.2.2.2.2 hR).2.2.2.1 hS
        unfold fdInStdioSpec at hSyncStd
        have hEqI : syncR = x := IScalar.eq_of_val_eq heq.symm
        subst hEqI
        rcases hxMem with rfl | rfl | rfl <;> simp at hSyncStd
      · right; exact Bool.eq_false_iff.mpr hS
    have hS1x : s1.getFd x.val = s.getFd x.val := hKeep1 x.val hNotSy hNotCl
    have hNeFd : x.val ≠ fd.val := by
      rcases hFdRedir hRb with ⟨_, hLe, hGt⟩
      by_cases hr2 : repW.val ≤ 2
      · have hFdNone : s1.getFd fd.val = none := (hLe hr2).2.2
        intro heq
        rw [← heq, hS1x] at hFdNone
        simp [ChildState.isOpen, hFdNone] at hxOpen
      · rw [hGt (by omega)]; exact hNeRep
    exact (hOther2 x.val hNeRep hNeFd).trans hS1x
  have hOpen2 : bRedir = true →
      s2.isOpen inFd.val = true ∧ s2.isOpen outFd.val = true ∧ s2.isOpen errFd.val = true := by
    intro hRb
    have hR : flagSet flags FLAG_REDIRECT_STDIO = true := by rw [← hbRedirEq]; exact hRb
    rcases hStdOpenPre hR with ⟨hOi, hOo, hOe⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [ChildState.isOpen, hGetS2Std inFd hR (Or.inl rfl) hOi] using hOi
    · simpa [ChildState.isOpen, hGetS2Std outFd hR (Or.inr (Or.inl rfl)) hOo] using hOo
    · simpa [ChildState.isOpen, hGetS2Std errFd hR (Or.inr (Or.inr rfl)) hOe] using hOe
  have hLim5 : bRedir = true → min s2.fdLimit 2147483648 ≥ 5 + Int.ofNat s2.fds.length := by
    intro hRb
    have hR : flagSet flags FLAG_REDIRECT_STDIO = true := by rw [← hbRedirEq]; exact hRb
    have h6 := hLim6 hR
    have hL1 : (s1.fds.length : Int) ≤ (s.fds.length : Int) := Int.ofNat_le.mpr hLen1
    have hL2 : (s2.fds.length : Int) ≤ (s1.fds.length : Int) + 1 := by
      have : s2.fds.length ≤ s1.fds.length + 1 := hLen2
      omega
    simp only [Int.ofNat_eq_natCast] at h6 ⊢
    rw [hCfg2.fdLimit]
    omega
  refine okPost_bind
    (okPost_and (apply_redir_stdio_safety s2 hRun2 bRedir inFd outFd errFd bCloseSrc)
      (apply_redir_stdio_ok_spec s2 hRun2 hOr2 bRedir inFd outFd errFd bCloseSrc
        hSignsRedir hOpen2 hLim5))
    fun (r2, s3) ⟨⟨hRun3, _, hRedirSafe⟩, ⟨hr2Eq, hStdioT3, hStdioF3⟩⟩ => ?_
  rw [hr2Eq]
  rcases hRedirSafe hr2Eq with ⟨hCfg3, _, _, _, hDe3, hWl3, hStdSafetyT3, _⟩
  have hOr3 : s3.oracle = [] := hCfg3.oracle.trans hOr2
  have hCfg30 : SameChildConfig s3 s := hCfg3.trans hCfg20
  have hKeepNeSync : flagSet flags FLAG_HAS_SYNC_BARRIER = true →
      ∀ kp ∈ keepFds.val, 0#i32 ≤ kp → kp.val ≠ syncR.val := by
    intro hS kp hkp hp0 heq
    have hF := (hOvSplit.2.2.2.1 hS).2.2
    have hIn : sliceContainsNonnegSpec keepFds.val syncR.val = true := by
      rw [sliceContainsNonnegSpec, Bool.and_eq_true, List.any_eq_true]
      exact ⟨decide_eq_true (by scalar_tac), kp, hkp, beq_iff_eq.mpr heq⟩
    exact absurd hIn (by rw [hF]; decide)
  have hKeepNeClose : ∀ kp ∈ keepFds.val, 0#i32 ≤ kp →
      sliceContainsNonnegSpec closeFds kp.val = false := by
    intro kp hkp hp0
    by_contra hc
    simp only [Bool.not_eq_false, sliceContainsNonnegSpec, Bool.and_eq_true,
      decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hc
    rcases hc with ⟨_, c, hcM, hcEq⟩
    have hOv : slicesOverlapNonnegSpec closeFds keepFds.val = true := by
      rw [slicesOverlapNonnegSpec, List.any_eq_true]
      exact ⟨c, hcM, by
        simp only [Bool.and_eq_true, decide_eq_true_eq, sliceContainsNonnegSpec, List.any_eq_true, beq_iff_eq]
        exact ⟨by scalar_tac, by scalar_tac, kp, hkp, hcEq.symm⟩⟩
    exact absurd hOv (by rw [hOvSplit.2.2.1]; decide)
  have hKpNeRep : ∀ kp ∈ keepFds.val, 0#i32 ≤ kp → kp.val ≠ repW.val := by
    intro kp hkp hp0 heq
    have hIn : sliceContainsNonnegSpec keepFds.val repW.val = true := by
      rw [sliceContainsNonnegSpec, Bool.and_eq_true, List.any_eq_true]
      exact ⟨decide_eq_true (by scalar_tac), kp, hkp, beq_iff_eq.mpr heq⟩
    exact absurd hIn (by rw [hOvSplit.2.1]; decide)
  have hKpNeFd : ∀ kp ∈ keepFds.val, 0#i32 ≤ kp → kp.val ≠ fd.val := by
    intro kp hkp hp0
    cases hRb : bRedir
    · rw [hFdNoRedir hRb]; exact hKpNeRep kp hkp hp0
    · rcases hFdRedir hRb with ⟨_, hLe, hGt⟩
      by_cases hr2 : repW.val ≤ 2
      · have hFdNone := (hLe hr2).2.2
        have hSy : kp.val ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false := by
          by_cases hS : flagSet flags FLAG_HAS_SYNC_BARRIER = true
          · exact Or.inl (hKeepNeSync hS kp hkp hp0)
          · exact Or.inr (Bool.eq_false_iff.mpr hS)
        have hS1k : s1.getFd kp.val = s.getFd kp.val := hKeep1 kp.val hSy (hKeepNeClose kp hkp hp0)
        have hOpK := hKpOpenPre kp hkp hp0
        intro heq
        rw [← heq, hS1k] at hFdNone
        simp [ChildState.isOpen, hFdNone] at hOpK
      · rw [hGt (by omega)]; exact hKpNeRep kp hkp hp0
  have hNoStdKeep : bRedir = true → ∀ k : Int, 0 ≤ k → k ≤ 2 →
      ∀ kp ∈ keepFds.val, 0#i32 ≤ kp → k ≠ kp.val := by
    intro hRb k hk0 hk2 kp hkp hp0 heq
    subst heq
    have hR : flagSet flags FLAG_REDIRECT_STDIO = true := by rw [← hbRedirEq]; exact hRb
    have hStd := (hOvSplit.2.2.2.2 hR).1
    have hMem : sliceHasStdioSlotSpec keepFds.val = true := by
      rw [sliceHasStdioSlotSpec, List.any_eq_true]
      exact ⟨kp, hkp, by simp [decide_eq_true hk0, decide_eq_true hk2]⟩
    exact absurd hMem (by rw [hStd]; decide)
  have hKeepNeSrc : bRedir = true → bCloseSrc = true → ∀ kp ∈ keepFds.val, 0#i32 ≤ kp →
      kp.val ≠ inFd.val ∧ kp.val ≠ outFd.val ∧ kp.val ≠ errFd.val := by
    intro hRb hCSb kp hkp hp0
    have hR : flagSet flags FLAG_REDIRECT_STDIO = true := by rw [← hbRedirEq]; exact hRb
    have hCS : flagSet flags FLAG_CLOSE_STDIO_SOURCES = true := by rw [← hbSrcEq]; exact hCSb
    have hC := (hOvSplit.2.2.2.2 hR).2.2.2.2 hCS
    have hNoStd := hNoStdKeep hRb
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      by_cases hgt : inFd.val > 2
      · have hF := hC.1 hgt
        have hIn : sliceContainsNonnegSpec keepFds.val inFd.val = true := by
          rw [sliceContainsNonnegSpec, Bool.and_eq_true, List.any_eq_true]
          exact ⟨decide_eq_true (by omega), kp, hkp, by simp [heq]⟩
        exact absurd hIn (by rw [hF]; decide)
      · exact hNoStd inFd.val (by scalar_tac) (by omega) kp hkp hp0 heq.symm
    · intro heq
      by_cases hgt : outFd.val > 2
      · have hF := hC.2.1 hgt
        have hIn : sliceContainsNonnegSpec keepFds.val outFd.val = true := by
          rw [sliceContainsNonnegSpec, Bool.and_eq_true, List.any_eq_true]
          exact ⟨decide_eq_true (by omega), kp, hkp, by simp [heq]⟩
        exact absurd hIn (by rw [hF]; decide)
      · exact hNoStd outFd.val (by scalar_tac) (by omega) kp hkp hp0 heq.symm
    · intro heq
      by_cases hgt : errFd.val > 2
      · have hF := hC.2.2 hgt
        have hIn : sliceContainsNonnegSpec keepFds.val errFd.val = true := by
          rw [sliceContainsNonnegSpec, Bool.and_eq_true, List.any_eq_true]
          exact ⟨decide_eq_true (by omega), kp, hkp, by simp [heq]⟩
        exact absurd hIn (by rw [hF]; decide)
      · exact hNoStd errFd.val (by scalar_tac) (by omega) kp hkp hp0 heq.symm
  have hOpen3Keep : ∀ kp ∈ keepFds.val, 0#i32 ≤ kp → s3.isOpen kp.val = true := by
    intro kp hkp hp0
    have hOpK := hKpOpenPre kp hkp hp0
    have hSy : kp.val ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false := by
      by_cases hS : flagSet flags FLAG_HAS_SYNC_BARRIER = true
      · exact Or.inl (hKeepNeSync hS kp hkp hp0)
      · exact Or.inr (Bool.eq_false_iff.mpr hS)
    have hS1k : s1.getFd kp.val = s.getFd kp.val := hKeep1 kp.val hSy (hKeepNeClose kp hkp hp0)
    have hS2k : s2.getFd kp.val = s1.getFd kp.val := hOther2 kp.val (hKpNeRep kp hkp hp0) (hKpNeFd kp hkp hp0)
    have hS3k : s3.getFd kp.val = s2.getFd kp.val := by
      cases hRb : bRedir
      · rw [hStdioF3 hRb]
      · have hkGt2 : kp.val > 2 := by
          by_contra hle
          exact hNoStdKeep hRb kp.val (by scalar_tac) (by omega) kp hkp hp0 rfl
        have hCond : bCloseSrc = false ∨ (kp.val ≠ inFd.val ∧ kp.val ≠ outFd.val ∧ kp.val ≠ errFd.val) := by
          cases hCS : bCloseSrc
          · exact Or.inl rfl
          · exact Or.inr (hKeepNeSrc hRb hCS kp hkp hp0)
        have hNon2 : s2.getFd kp.val ≠ none := by
          intro hN
          have hOp2 : s2.isOpen kp.val = true := by simpa [ChildState.isOpen, hS2k, hS1k] using hOpK
          simp [ChildState.isOpen, hN] at hOp2
        exact (hStdSafetyT3 hRb).2.2.2.1 kp.val hkGt2 hCond hNon2
    simpa [ChildState.isOpen, hS3k, hS2k, hS1k] using hOpK
  refine okPost_bind (clear_cloexec_slice_ok s3 hRun3 hOr3 keepFds hOpen3Keep)
    fun p ⟨hr3Eq, hRun4, hCfg4, hOr4, _, _, _, hDe4, hWl4, hClrNe4, _⟩ => ?_
  rcases p with ⟨r3, s4⟩
  dsimp only at hr3Eq hRun4 hCfg4 hOr4 hDe4 hWl4 hClrNe4
  subst hr3Eq
  have hCfg40 : SameChildConfig s4 s := hCfg4.trans hCfg30
  have hFdOpen4 : s4.getFd fd.val = some fRel := by
    have hFdNotKp : ∀ kp ∈ keepFds.val, 0#i32 ≤ kp → fd.val ≠ kp.val :=
      fun kp hkp hp0 heq => hKpNeFd kp hkp hp0 heq.symm
    have h43 : s4.getFd fd.val = s3.getFd fd.val := hClrNe4 fd.val hFdNotKp
    have h32 : s3.getFd fd.val = s2.getFd fd.val := by
      cases hRb : bRedir
      · rw [hStdioF3 hRb]
      · have hR : flagSet flags FLAG_REDIRECT_STDIO = true := by rw [← hbRedirEq]; exact hRb
        rcases hFdRedir hRb with ⟨hGt2, hLe, hGt⟩
        have hCond : bCloseSrc = false ∨
            (fd.val ≠ inFd.val ∧ fd.val ≠ outFd.val ∧ fd.val ≠ errFd.val) := by
          right
          have hRepStd := (hOvSplit.2.2.2.2 hR).2.1
          have hNeRepStd : repW.val ≠ inFd.val ∧ repW.val ≠ outFd.val ∧ repW.val ≠ errFd.val := by
            unfold fdInStdioSpec at hRepStd
            refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
            · have h1 := IScalar.eq_of_val_eq h; simp [h1] at hRepStd
            · have h1 := IScalar.eq_of_val_eq h; simp [h1] at hRepStd
            · have h1 := IScalar.eq_of_val_eq h; simp [h1] at hRepStd
          by_cases hr2 : repW.val ≤ 2
          · have hFdNone := (hLe hr2).2.2
            rcases hStdOpenPre hR with ⟨hOpIn, hOpOut, hOpErr⟩
            have hSlStd := (hOvSplit.2.2.2.2 hR).2.2.1
            have mkNot : ∀ (x : I32),
                (x = inFd ∨ x = outFd ∨ x = errFd) → s.isOpen x.val = true → fd.val ≠ x.val := by
              intro x hx hxOp heq
              have hNotCl : sliceContainsNonnegSpec closeFds x.val = false := by
                cases hc : sliceContainsNonnegSpec closeFds x.val
                · rfl
                · unfold stdioInSliceSpec at hSlStd
                  rcases hx with rfl | rfl | rfl <;> simp [hc] at hSlStd
              have hNotSy : x.val ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false := by
                by_cases hS : flagSet flags FLAG_HAS_SYNC_BARRIER = true
                · left; intro heqS
                  have hSyncStd := (hOvSplit.2.2.2.2 hR).2.2.2.1 hS
                  unfold fdInStdioSpec at hSyncStd
                  have hEqI : syncR = x := IScalar.eq_of_val_eq heqS.symm
                  subst hEqI
                  rcases hx with rfl | rfl | rfl <;> simp at hSyncStd
                · right; exact Bool.eq_false_iff.mpr hS
              have hS1x := hKeep1 x.val hNotSy hNotCl
              rw [heq, hS1x] at hFdNone
              simp [ChildState.isOpen, hFdNone] at hxOp
            exact ⟨mkNot inFd (Or.inl rfl) hOpIn,
              mkNot outFd (Or.inr (Or.inl rfl)) hOpOut,
              mkNot errFd (Or.inr (Or.inr rfl)) hOpErr⟩
          · rw [hGt (by omega)]; exact hNeRepStd
        exact (hStdSafetyT3 hRb).2.2.2.1 fd.val hGt2 hCond (by rw [hGetRel]; exact Option.some_ne_none _)
    rw [h43, h32, hGetRel]
  have hFree4 : ∃ dirfd, findLowestFreeFd s4 0 = some dirfd :=
    run_child_free_fd_after_setup s s1 s2 s3 s4 flags syncR inFd outFd errFd repW fd
      closeFds keepFds.val hSlack hCfg40.fdLimit hSec1 hNoSec hOther2 hStdioT3 hStdioF3
      hClrNe4 hKpOpenPre (fun hR hGt2 => (hFdRedir (by rw [hbRedirEq]; exact hR)).2.2 hGt2)
      (fun hRF => hFdNoRedir (by rw [hbRedirEq]; exact hRF))
  have hFdGe : 0#i32 ≤ fd := by
    cases hRb : bRedir
    · rw [hFdNoRedir hRb]; exact hRepGe
    · have hGt2 := (hFdRedir hRb).1; scalar_tac
  exact hCont fd s4 fRel hRun4 hOr4 hCfg40 (hDe4.trans (hDe3.trans hDe2))
    (hWl4.trans (hWl3.trans (hWl2.trans hWl1))) ⟨eRep1, hE1, hFdOpen4, hDescRel, hCloRel⟩
    hFree4 hFdGe

private theorem run_child_exec_after_pre
    (s s1 : ChildState)
    (flags : U32) (syncR inFd outFd errFd repW : I32)
    (closeFds : List I32) (keepFds : Slice I32)
    (cwd? : Option sys.CStr) (path : sys.CStr) (argv envp : sys.CStrArray)
    (hOr : s.oracle = [])
    (hPre : PreSyncOkPost s flags syncR inFd outFd errFd repW closeFds keepFds.val s1)
    (hOpRep : s.isOpen repW.val = true)
    (hSlack : min s.fdLimit 2147483648 ≥ minRunChildFdSlack flags + Int.ofNat s.fds.length)
    (hCap : flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 = true →
      s.closeRangeSupported = true ∨ s.procSelfFdAvailable = true)
    (hPathNe : path ≠ [])
    (hCwdNe : ∀ dir : Bytes, cwd? = some dir → dir ≠ []) :
    OkPost
      (postfork.child.run_child_post_sync s1 { flags := flags, sync_r := syncR, stdin_fd := inFd, stdout_fd := outFd, stderr_fd := errFd, rep_w := repW } keepFds { cwd := cwd?, path := path, argv := argv, envp := envp })
      (RunChildExecPost s flags syncR inFd outFd errFd repW closeFds keepFds.val cwd? path argv envp) := by
  have hNoAbort : OkPost
      (postfork.child.run_child_post_sync s1 { flags := flags, sync_r := syncR, stdin_fd := inFd, stdout_fd := outFd, stderr_fd := errFd, rep_w := repW } keepFds { cwd := cwd?, path := path, argv := argv, envp := envp })
      (fun s' => s'.status ≠ .exited 127#i32 ∧ s'.status ≠ .exited 125#i32) := by
    refine run_child_post_sync_after_setup s s1 flags syncR inFd outFd errFd repW
      closeFds keepFds cwd? path argv envp hOr hPre hOpRep hSlack _ ?_
    intro fd s4 fRel hRun4 hOr4 hCfg40 _ _ _ hFree4 _
    let bCloseUnk := (flags &&& FLAG_CLOSE_UNKEPT_ABOVE2 != 0#u32)
    have hCap4 : bCloseUnk = true →
        s4.closeRangeSupported = true ∨
        (s4.procSelfFdAvailable = true ∧ ∃ dirfd, findLowestFreeFd s4 0 = some dirfd) := by
      intro hU
      rcases hCap hU with hCr | hPr
      · left; rw [hCfg40.closeRangeSupported]; exact hCr
      · right; exact ⟨by rw [hCfg40.procSelfFdAvailable]; exact hPr, hFree4⟩
    have hUnk : OkPost (postfork.child.apply_close_unkept s4 bCloseUnk fd keepFds) fun (r4, s5) =>
        r4 = .Ok () ∧ s5.status = .running ∧ s5.oracle = [] := by
      unfold postfork.child.apply_close_unkept
      cases hU : bCloseUnk
      · exact ⟨(.Ok (), s4), rfl, rfl, hRun4, hOr4⟩
      · exact okPost_mono (close_fds_above2_except_spec_of_free s4 fd keepFds hRun4 hOr4 (hCap4 hU))
          fun (r, s5) ⟨hr, _, hRun5, _, _, _, _, hOr5, _⟩ => ⟨hr, hRun5, hOr5.trans hOr4⟩
    refine okPost_bind hUnk fun p ⟨hr4Eq, hRun5, hOr5⟩ => ?_
    rcases p with ⟨r4, s5⟩
    dsimp only at hr4Eq hRun5 hOr5
    subst hr4Eq
    change OkPost (match cwd? with
      | none => do
        let (e, sExec) ← sys.execve s5 path argv envp
        postfork.child.report_and_exit sExec fd postfork.child.STAGE_EXECVE e postfork.child.ENOENT
      | some dir => do
        let (rCh, s6) ← sys.chdir s5 dir
        match rCh with
        | .Ok _ =>
          let (e, sExec) ← sys.execve s6 path argv envp
          postfork.child.report_and_exit sExec fd postfork.child.STAGE_EXECVE e postfork.child.ENOENT
        | .Err e =>
          postfork.child.report_and_exit s6 fd postfork.child.STAGE_CHDIR e postfork.fd_ops.EIO) _
    have hExecOn : ∀ (x : ChildState), x.status = .running → x.oracle = [] →
        OkPost (do
          let (e, sExec) ← sys.execve x path argv envp
          postfork.child.report_and_exit sExec fd postfork.child.STAGE_EXECVE e postfork.child.ENOENT)
          (fun s' => s'.status ≠ .exited 127#i32 ∧ s'.status ≠ .exited 125#i32) := by
      intro x hxRun hxOr
      obtain ⟨eEx, sEx, hExEq, _, _, _, _, _, _, _, hExSpec⟩ := sys_execve_running x hxRun path argv envp
      rw [hExEq, bind_ok]
      have hNorm : currentFault x = .normal := currentFault_oracle_nil x hxOr
      have hemp : path.isEmpty = false := by cases path with | nil => exact absurd rfl hPathNe | cons _ _ => rfl
      simp only [hNorm, hemp, Bool.false_eq_true, ↓reduceIte] at hExSpec
      have hNotRun : sEx.status ≠ .running := by rw [hExSpec.2.2]; intro h; cases h
      exact okPost_mono (report_and_exit_not_running sEx hNotRun fd _ eEx _) fun s' hs' => by
        rw [hs', hExSpec.2.2]; constructor <;> (intro h; cases h)
    cases hc : cwd? with
    | none => exact hExecOn s5 hRun5 hOr5
    | some dir =>
      dsimp only
      obtain ⟨rCh, s6, hChEq, hCfg6, _, _, _, _, _, _, _, _, hChOr⟩ := sys_chdir_running s5 hRun5 dir
      rw [hChEq, bind_ok]
      have hemp : dir.isEmpty = false := by
        have := hCwdNe dir hc
        cases dir with | nil => exact absurd rfl this | cons _ _ => rfl
      have hOkCh : rCh = .Ok () := (hChOr hOr5).2 hemp
      rw [hOkCh]
      exact hExecOn s6 (hCfg6.status.trans hRun5) (hCfg6.oracle.trans hOr5)
  refine okPost_mono
    (okPost_and (run_child_post_sync_safety s s1 flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp hPre)
      hNoAbort)
    fun s' ⟨hSafe, h127, h125⟩ => ?_
  rcases hSafe with hEx127 | ⟨_, hEx125, _⟩ | ⟨hExec, _⟩
  · exact absurd hEx127 h127
  · exact absurd hEx125 h125
  · exact hExec (by simp [oracleHasSeccomp, hOr])

/-- Exact execution postcondition for `postfork.child.run_child` under `ValidRunChildExecPre`. -/
theorem run_child_exec
    (s : ChildState) (flags : U32) (syncR inFd outFd errFd repW : I32)
    (closeFds keepFds : Slice I32)
    (cwd? : Option sys.CStr) (path : sys.CStr) (argv envp : sys.CStrArray)
    (hPre : ValidRunChildExecPre s flags syncR inFd outFd errFd repW closeFds.val keepFds.val cwd? path) :
    OkPost
      (postfork.child.run_child s { flags := flags, sync_r := syncR, stdin_fd := inFd, stdout_fd := outFd, stderr_fd := errFd, rep_w := repW } closeFds keepFds { cwd := cwd?, path := path, argv := argv, envp := envp })
      (RunChildExecPost s flags syncR inFd outFd errFd repW closeFds.val keepFds.val cwd? path argv envp) := by
  rcases hPre with ⟨hRun, hOr, hFl, hRepGe, hSg, hOv, hPgPre, hSlack, hCap, hOpRep,
    hStdOp, hKpOp, hSyncStream, hPathNe, hCwdNe⟩
  unfold postfork.child.run_child
  refine okPost_bind
    (run_child_pre_sync_exec_ok s hRun hOr flags syncR inFd outFd errFd repW closeFds keepFds
      hFl hRepGe hSg hOv hPgPre hStdOp hKpOp hSyncStream)
    fun (b, s1) ⟨hb, hPreOk⟩ => ?_
  subst hb
  exact run_child_exec_after_pre s s1 flags syncR inFd outFd errFd repW closeFds.val keepFds
    cwd? path argv envp hOr hPreOk hOpRep hSlack hCap hPathNe hCwdNe

private theorem run_child_stage_failures_after_pre
    (s s1 : ChildState)
    (flags : U32) (syncR inFd outFd errFd repW : I32)
    (closeFds keepFds : Slice I32)
    (cwd? : Option sys.CStr) (path : sys.CStr) (argv envp : sys.CStrArray)
    (hOr : s.oracle = [])
    (hPre : PreSyncOkPost s flags syncR inFd outFd errFd repW closeFds.val keepFds.val s1)
    {repEnt : FdEntry} (hRepFd : s.getFd repW.val = some repEnt)
    {rd : Bool} {rem : Bytes} (hRepDesc : s.getDesc repEnt.desc = .stream rd true false rem)
    (hSlack : min s.fdLimit 2147483648 ≥ minRunChildFdSlack flags + Int.ofNat s.fds.length) :
    (flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 && !s.closeRangeSupported && !s.procSelfFdAvailable = true →
      OkPost (postfork.child.run_child_post_sync s1 { flags := flags, sync_r := syncR, stdin_fd := inFd, stdout_fd := outFd, stderr_fd := errFd, rep_w := repW } keepFds { cwd := cwd?, path := path, argv := argv, envp := envp })
        fun s' => s'.status = .exited 127#i32 ∧
          appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc =
            expectedFailureWireBytes 5#u8 (sanitizeErrno s.procOpenErrno)) ∧
    ((!flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 || s.closeRangeSupported || s.procSelfFdAvailable) = true →
      (cwd? = some [] →
        OkPost (postfork.child.run_child_post_sync s1 { flags := flags, sync_r := syncR, stdin_fd := inFd, stdout_fd := outFd, stderr_fd := errFd, rep_w := repW } keepFds { cwd := cwd?, path := path, argv := argv, envp := envp })
          fun s' => s'.status = .exited 127#i32 ∧
            appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc =
              expectedFailureWireBytes 6#u8 ENOENT) ∧
      (cwd? = none → path = [] →
        OkPost (postfork.child.run_child_post_sync s1 { flags := flags, sync_r := syncR, stdin_fd := inFd, stdout_fd := outFd, stderr_fd := errFd, rep_w := repW } keepFds { cwd := cwd?, path := path, argv := argv, envp := envp })
          fun s' => s'.status = .exited 127#i32 ∧
            appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc =
              expectedFailureWireBytes 7#u8 ENOENT)) := by
  have hOpRep : s.isOpen repW.val = true := by simp [ChildState.isOpen, hRepFd]
  have hDescS1 : ∃ rd' rem', s1.getDesc repEnt.desc = .stream rd' true false rem' :=
    hPre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 repEnt.desc rd rem hRepDesc
  refine ⟨fun hNoCap => ?_, fun hCap => ⟨fun hCwdEmpty => ?_, fun hCwdNone hPathEmpty => ?_⟩⟩
  · refine run_child_post_sync_after_setup s s1 flags syncR inFd outFd errFd repW
      closeFds.val keepFds cwd? path argv envp hOr hPre hOpRep hSlack _ ?_
    intro fd s4 fRel hRun4 hOr4 hCfg40 hDe41 hWl4 hRel4 hFree4 hFdGe
    rcases hRel4 with ⟨eRep4, hRepS4, hFd4, hRelDesc4, _⟩
    rw [hRepFd] at hRepS4; injection hRepS4 with heRepEq; subst heRepEq
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hNoCap
    rcases hNoCap with ⟨⟨hU, hCrF⟩, hPrF⟩
    have hUb : (flags &&& FLAG_CLOSE_UNKEPT_ABOVE2 != 0#u32) = true := hU
    rw [hUb]
    unfold postfork.child.apply_close_unkept
    have hNoSec4 : oracleHasSeccomp s4.oracle = false := by simp [oracleHasSeccomp, hOr4]
    have hUnkErr := close_fds_above2_except_err_spec_of_free s4 fd keepFds hRun4 hNoSec4
      (by rw [hCfg40.closeRangeSupported]; exact hCrF)
      (by rw [hCfg40.procSelfFdAvailable]; exact hPrF) hFree4
    change OkPost (do
      let (r4, s5) ← postfork.child.apply_close_unkept s4 true fd keepFds
      match r4 with
      | .Ok _ => _
      | .Err e => postfork.child.report_and_exit s5 fd postfork.child.STAGE_CLOSE_UNKEPT e postfork.fd_ops.EIO) _
    refine okPost_bind hUnkErr fun p ⟨hr4, hCfg5, hRun5, _, _, _, hDe5, hWl5, hFds5⟩ => ?_
    rcases p with ⟨r4, s5⟩
    dsimp only at hr4 hCfg5 hRun5 hDe5 hWl5 hFds5
    subst hr4
    change OkPost (postfork.child.report_and_exit s5 fd postfork.child.STAGE_CLOSE_UNKEPT
      (sanitizeErrno s4.procOpenErrno) postfork.fd_ops.EIO) _
    have hFd5 : s5.getFd fd.val = some fRel := by simpa [ChildState.getFd, hFds5] using hFd4
    have hOr5 : s5.oracle = [] := hCfg5.oracle.trans hOr4
    rcases hDescS1 with ⟨rd', rem', hDs1⟩
    have hDe5' : s5.getDesc fRel.desc = .stream rd' true false rem' := by
      rw [hRelDesc4, ChildState.getDesc, hDe5, hDe41]; exact hDs1
    refine okPost_mono
      (report_and_exit_bytes s5 hRun5 hOr5 fd postfork.child.STAGE_CLOSE_UNKEPT
        (sanitizeErrno s4.procOpenErrno) postfork.fd_ops.EIO hFdGe hFd5 hDe5')
      fun s' ⟨hSt, hApp⟩ => ?_
    rw [rc_stage_close_unkept_eq, normalizeErrnoSpec_sanitizeErrno, hCfg40.procOpenErrno,
      hRelDesc4, hWl5, hWl4] at hApp
    exact ⟨hSt, hApp⟩
  · refine run_child_post_sync_after_setup s s1 flags syncR inFd outFd errFd repW
      closeFds.val keepFds cwd? path argv envp hOr hPre hOpRep hSlack _ ?_
    intro fd s4 fRel hRun4 hOr4 hCfg40 hDe41 hWl4 hRel4 hFree4 hFdGe
    rcases hRel4 with ⟨eRep4, hRepS4, hFd4, hRelDesc4, _⟩
    rw [hRepFd] at hRepS4; injection hRepS4 with heRepEq; subst heRepEq
    rcases hDescS1 with ⟨rd', rem', hDs1⟩
    have hDe4' : s4.getDesc fRel.desc = .stream rd' true false rem' := by
      rw [hRelDesc4, ChildState.getDesc, hDe41]; exact hDs1
    let bCloseUnk := (flags &&& FLAG_CLOSE_UNKEPT_ABOVE2 != 0#u32)
    have hUnk : OkPost (postfork.child.apply_close_unkept s4 bCloseUnk fd keepFds) fun (r4, s5) =>
        r4 = .Ok () ∧ s5.status = .running ∧ s5.oracle = [] ∧ s5.writeLog = s.writeLog ∧
        s5.getFd fd.val = some fRel ∧ s5.getDesc fRel.desc = .stream rd' true false rem' := by
      unfold postfork.child.apply_close_unkept
      cases hU : bCloseUnk
      · exact ⟨(.Ok (), s4), rfl, rfl, hRun4, hOr4, hWl4, hFd4, hDe4'⟩
      · have hCap4 : s4.closeRangeSupported = true ∨
            (s4.procSelfFdAvailable = true ∧ ∃ dirfd, findLowestFreeFd s4 0 = some dirfd) := by
          simp only [Bool.or_eq_true, Bool.not_eq_true'] at hCap
          rcases hCap with (hNF | hCr) | hPr
          · have hUT : flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 = true := hU
            rw [hUT] at hNF; cases hNF
          · left; rw [hCfg40.closeRangeSupported]; exact hCr
          · right; exact ⟨by rw [hCfg40.procSelfFdAvailable]; exact hPr, hFree4⟩
        refine okPost_mono (close_fds_above2_except_spec_of_free s4 fd keepFds hRun4 hOr4 hCap4)
          fun (r, s5) ⟨hr, _, hRun5, _, _, _, hWl5, hOr5, hDeFd5, hCl5⟩ => ?_
        have hFd5 : s5.getFd fd.val = some fRel := by
          by_cases hfd2 : fd.val ≤ 2
          · rw [hCl5.1 fd.val (by scalar_tac) hfd2, hFd4]
          · have hKept : isKeptAbove2 fd keepFds.val fd.val = true := by
              simp only [isKeptAbove2, Bool.and_eq_true, decide_eq_true_eq,
                Bool.or_eq_true, beq_self_eq_true]
              exact ⟨by omega, Or.inl ⟨by scalar_tac, trivial⟩⟩
            have hK2 := hCl5.2 fd.val (by omega) (by scalar_tac)
            simp only [hKept, ↓reduceIte] at hK2
            rw [hK2, hFd4]
        have hDe5' : s5.getDesc fRel.desc = .stream rd' true false rem' := by
          rw [hDeFd5 fd.val fRel hFd4]; exact hDe4'
        exact ⟨hr, hRun5, hOr5.trans hOr4, hWl5.trans hWl4, hFd5, hDe5'⟩
    refine okPost_bind hUnk fun p ⟨hr4Eq, hRun5, hOr5, hWl5, hFd5, hDe5'⟩ => ?_
    rcases p with ⟨r4, s5⟩
    dsimp only at hr4Eq hRun5 hOr5 hWl5 hFd5 hDe5'
    subst hr4Eq
    rw [hCwdEmpty]
    change OkPost (do
      let (rCh, s6) ← sys.chdir s5 []
      match rCh with
      | .Ok _ => _
      | .Err e => postfork.child.report_and_exit s6 fd postfork.child.STAGE_CHDIR e postfork.fd_ops.EIO) _
    obtain ⟨rCh, s6, hChEq, hCfg6, hFds6, hDe6, _, hWl6, _, _, _, _, hChOr⟩ := sys_chdir_running s5 hRun5 []
    rw [hChEq, bind_ok]
    have hrCh : rCh = .Err ENOENT := (hChOr hOr5).1 rfl
    subst hrCh
    change OkPost (postfork.child.report_and_exit s6 fd postfork.child.STAGE_CHDIR ENOENT postfork.fd_ops.EIO) _
    have hRun6 : s6.status = .running := hCfg6.status.trans hRun5
    have hOr6 : s6.oracle = [] := hCfg6.oracle.trans hOr5
    have hFd6 : s6.getFd fd.val = some fRel := by simpa [ChildState.getFd, hFds6] using hFd5
    have hDe6' : s6.getDesc fRel.desc = .stream rd' true false rem' := by
      simpa [ChildState.getDesc, hDe6] using hDe5'
    refine okPost_mono
      (report_and_exit_bytes s6 hRun6 hOr6 fd postfork.child.STAGE_CHDIR ENOENT postfork.fd_ops.EIO hFdGe hFd6 hDe6')
      fun s' ⟨hSt, hApp⟩ => ?_
    rw [rc_stage_chdir_eq, normalizeErrnoSpec_enoent, hRelDesc4, hWl6, hWl5] at hApp
    exact ⟨hSt, hApp⟩
  · refine run_child_post_sync_after_setup s s1 flags syncR inFd outFd errFd repW
      closeFds.val keepFds cwd? path argv envp hOr hPre hOpRep hSlack _ ?_
    intro fd s4 fRel hRun4 hOr4 hCfg40 hDe41 hWl4 hRel4 hFree4 hFdGe
    rcases hRel4 with ⟨eRep4, hRepS4, hFd4, hRelDesc4, _⟩
    rw [hRepFd] at hRepS4; injection hRepS4 with heRepEq; subst heRepEq
    rcases hDescS1 with ⟨rd', rem', hDs1⟩
    have hDe4' : s4.getDesc fRel.desc = .stream rd' true false rem' := by
      rw [hRelDesc4, ChildState.getDesc, hDe41]; exact hDs1
    let bCloseUnk := (flags &&& FLAG_CLOSE_UNKEPT_ABOVE2 != 0#u32)
    have hUnk : OkPost (postfork.child.apply_close_unkept s4 bCloseUnk fd keepFds) fun (r4, s5) =>
        r4 = .Ok () ∧ s5.status = .running ∧ s5.oracle = [] ∧ s5.writeLog = s.writeLog ∧
        s5.getFd fd.val = some fRel ∧ s5.getDesc fRel.desc = .stream rd' true false rem' := by
      unfold postfork.child.apply_close_unkept
      cases hU : bCloseUnk
      · exact ⟨(.Ok (), s4), rfl, rfl, hRun4, hOr4, hWl4, hFd4, hDe4'⟩
      · have hCap4 : s4.closeRangeSupported = true ∨
            (s4.procSelfFdAvailable = true ∧ ∃ dirfd, findLowestFreeFd s4 0 = some dirfd) := by
          simp only [Bool.or_eq_true, Bool.not_eq_true'] at hCap
          rcases hCap with (hNF | hCr) | hPr
          · have hUT : flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 = true := hU
            rw [hUT] at hNF; cases hNF
          · left; rw [hCfg40.closeRangeSupported]; exact hCr
          · right; exact ⟨by rw [hCfg40.procSelfFdAvailable]; exact hPr, hFree4⟩
        refine okPost_mono (close_fds_above2_except_spec_of_free s4 fd keepFds hRun4 hOr4 hCap4)
          fun (r, s5) ⟨hr, _, hRun5, _, _, _, hWl5, hOr5, hDeFd5, hCl5⟩ => ?_
        have hFd5 : s5.getFd fd.val = some fRel := by
          by_cases hfd2 : fd.val ≤ 2
          · rw [hCl5.1 fd.val (by scalar_tac) hfd2, hFd4]
          · have hKept : isKeptAbove2 fd keepFds.val fd.val = true := by
              simp only [isKeptAbove2, Bool.and_eq_true, decide_eq_true_eq,
                Bool.or_eq_true, beq_self_eq_true]
              exact ⟨by omega, Or.inl ⟨by scalar_tac, trivial⟩⟩
            have hK2 := hCl5.2 fd.val (by omega) (by scalar_tac)
            simp only [hKept, ↓reduceIte] at hK2
            rw [hK2, hFd4]
        have hDe5' : s5.getDesc fRel.desc = .stream rd' true false rem' := by
          rw [hDeFd5 fd.val fRel hFd4]; exact hDe4'
        exact ⟨hr, hRun5, hOr5.trans hOr4, hWl5.trans hWl4, hFd5, hDe5'⟩
    refine okPost_bind hUnk fun p ⟨hr4Eq, hRun5, hOr5, hWl5, hFd5, hDe5'⟩ => ?_
    rcases p with ⟨r4, s5⟩
    dsimp only at hr4Eq hRun5 hOr5 hWl5 hFd5 hDe5'
    subst hr4Eq
    rw [hCwdNone, hPathEmpty]
    change OkPost (do
      let (e, sExec) ← sys.execve s5 [] argv envp
      postfork.child.report_and_exit sExec fd postfork.child.STAGE_EXECVE e postfork.child.ENOENT) _
    obtain ⟨eEx, sEx, hExEq, hOrEx, hFdsEx, hDeEx, _, _, _, hWlEx, _, hExSpec⟩ :=
      sys_execve_running s5 hRun5 [] argv envp
    rw [hExEq, bind_ok]
    have hNorm : currentFault s5 = .normal := currentFault_oracle_nil s5 hOr5
    simp only [hNorm, List.isEmpty_nil, ↓reduceIte] at hExSpec
    rcases hExSpec with ⟨rfl, hRunEx⟩
    have hFdEx : sEx.getFd fd.val = some fRel := by simpa [ChildState.getFd, hFdsEx] using hFd5
    have hDeEx' : sEx.getDesc fRel.desc = .stream rd' true false rem' := by
      simpa [ChildState.getDesc, hDeEx] using hDe5'
    refine okPost_mono
      (report_and_exit_bytes sEx hRunEx (hOrEx.trans hOr5) fd postfork.child.STAGE_EXECVE ENOENT postfork.child.ENOENT
        hFdGe hFdEx hDeEx')
      fun s' ⟨hSt, hApp⟩ => ?_
    have hNE : normalizeErrnoSpec ENOENT ENOENT = ENOENT := by decide
    rw [rc_stage_execve_eq, rc_enoent_eq, hNE, hRelDesc4, hWlEx, hWl5] at hApp
    exact ⟨hSt, hApp⟩

private theorem run_child_broken_rep_bad_flags
    (s : ChildState) (hRun : s.status = .running)
    (flags : U32) (syncR inFd outFd errFd repW : I32)
    (closeFds keepFds : Slice I32)
    (cwd? : Option sys.CStr) (path : sys.CStr) (argv envp : sys.CStrArray)
    (hRep : ¬ repW < 0#i32) (hBad : (!validFlagsSpec flags) = true) :
    OkPost
      (postfork.child.run_child s { flags := flags, sync_r := syncR, stdin_fd := inFd, stdout_fd := outFd, stderr_fd := errFd, rep_w := repW } closeFds keepFds { cwd := cwd?, path := path, argv := argv, envp := envp })
      fun s' => s'.status = .exited 127#i32 := by
  have hPre : OkPost
      (postfork.child.run_child_pre_sync s { flags := flags, sync_r := syncR, stdin_fd := inFd, stdout_fd := outFd, stderr_fd := errFd, rep_w := repW } closeFds keepFds)
      fun (b, s1) => b = false ∧ s1.status = .exited 127#i32 := by
    unfold postfork.child.run_child_pre_sync
    simp only [hRep, ↓reduceIte]
    refine okPost_bind (validate_child_args_spec flags syncR inFd outFd errFd repW closeFds keepFds)
      fun rVal hrVal => ?_
    simp only [hBad, ↓reduceIte] at hrVal
    rw [hrVal]
    refine okPost_bind (report_and_exit_status127 s hRun repW _ _ _) fun sExit hSt => ?_
    exact okPost_ok _ _ ⟨rfl, hSt⟩
  unfold postfork.child.run_child
  exact okPost_bind hPre fun (b, s1) ⟨hb, hSt⟩ => by
    subst hb
    exact okPost_ok _ _ hSt

private theorem run_child_tail_trivial
    (s s1 : ChildState) (b : Bool) (flags : U32) (syncR inFd outFd errFd repW : I32)
    (closeFds keepFds : Slice I32) (cwd? : Option sys.CStr) (path : sys.CStr)
    (argv envp : sys.CStrArray)
    (hSafePre :
      if b = true then PreSyncOkPost s flags syncR inFd outFd errFd repW closeFds.val keepFds.val s1
      else
        s1.status = Status.exited 127#i32 ∨
          flagSet flags FLAG_HAS_SYNC_BARRIER = true ∧
            s1.status = Status.exited 125#i32 ∧
              s1.writeLog = s.writeLog ∧
                (oracleHasSeccomp s.oracle = false →
                    ChildState.isOpen s1 syncR.val = false ∧
                      ∀ cfd ∈ closeFds.val, 0#i32 ≤ cfd → ChildState.isOpen s1 cfd.val = false) ∧
                  closedBeforeSyncRead (List.drop s.trace.length s1.trace) closeFds.val syncR) :
    OkPost
      (if b = true then
         postfork.child.run_child_post_sync s1 { flags := flags, sync_r := syncR, stdin_fd := inFd, stdout_fd := outFd, stderr_fd := errFd, rep_w := repW } keepFds { cwd := cwd?, path := path, argv := argv, envp := envp }
       else ok s1)
      fun _ => True := by
  cases b
  · exact okPost_ok _ _ trivial
  · exact okPost_mono
      (run_child_post_sync_safety s s1 flags syncR inFd outFd errFd repW closeFds.val keepFds cwd? path argv envp hSafePre)
      fun _ _ => trivial

private theorem run_child_validation_stages_spec
    (s : ChildState) (hRun : s.status = .running) (hOr : s.oracle = [])
    (flags : U32) (syncR inFd outFd errFd repW : I32)
    (closeFds keepFds : Slice I32)
    (cwd? : Option sys.CStr) (path : sys.CStr) (argv envp : sys.CStrArray) :
    OkPost
      (postfork.child.run_child s { flags := flags, sync_r := syncR, stdin_fd := inFd, stdout_fd := outFd, stderr_fd := errFd, rep_w := repW } closeFds keepFds { cwd := cwd?, path := path, argv := argv, envp := envp })
      fun s' =>
        if repW < 0#i32 then
          s'.status = .exited 127#i32 ∧ s'.writeLog = s.writeLog
        else
          match s.getFd repW.val with
          | none => True
          | some repEnt =>
            match s.getDesc repEnt.desc with
            | .stream _ true false _ =>
              if !validFlagsSpec flags then
                s'.status = .exited 127#i32 ∧
                appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc =
                  expectedFailureWireBytes 1#u8 EINVAL
              else if !validSignsSpec flags syncR inFd outFd errFd then
                s'.status = .exited 127#i32 ∧
                appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc =
                  expectedFailureWireBytes 1#u8 EBADF
              else if !validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds.val keepFds.val then
                s'.status = .exited 127#i32 ∧
                appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc =
                  expectedFailureWireBytes 1#u8 EINVAL
              else if flagSet flags FLAG_SET_PGID && decide (s.pid > 0) && decide (s.pid = s.sid) then
                s'.status = .exited 127#i32 ∧
                appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc =
                  expectedFailureWireBytes 2#u8 EPERM
              else if (flagSet flags FLAG_HAS_SYNC_BARRIER && !s.isOpen syncR.val) ||
                  (flagSet flags FLAG_REDIRECT_STDIO && (!s.isOpen inFd.val || !s.isOpen outFd.val || !s.isOpen errFd.val)) ||
                  keepFds.val.any (fun k => decide (0#i32 ≤ k) && !s.isOpen k.val) then
                s'.status = .exited 127#i32 ∧
                appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc =
                  expectedFailureWireBytes 4#u8 EBADF
              else if flagSet flags FLAG_HAS_SYNC_BARRIER then
                match s.getFd syncR.val with
                | none => True
                | some syncEnt =>
                  match s.getDesc syncEnt.desc with
                  | .stream true _ _ [] =>
                    s'.status = .exited 125#i32 ∧
                    s'.writeLog = s.writeLog ∧
                    closedBeforeSyncRead (s'.trace.drop s.trace.length) closeFds.val syncR
                  | .stream true _ _ (_ :: _) =>
                    flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 &&
                      !s.closeRangeSupported && !s.procSelfFdAvailable &&
                      decide (min s.fdLimit 2147483648 ≥ minRunChildFdSlack flags + Int.ofNat s.fds.length) = true →
                      s'.status = .exited 127#i32 ∧
                      appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc =
                        expectedFailureWireBytes 5#u8 (sanitizeErrno s.procOpenErrno)
                  | _ => True
              else
                (flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 &&
                  !s.closeRangeSupported && !s.procSelfFdAvailable &&
                  decide (min s.fdLimit 2147483648 ≥ minRunChildFdSlack flags + Int.ofNat s.fds.length) = true →
                  s'.status = .exited 127#i32 ∧
                  appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc =
                    expectedFailureWireBytes 5#u8 (sanitizeErrno s.procOpenErrno)) ∧
                ((!flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 ||
                    s.closeRangeSupported || s.procSelfFdAvailable) &&
                  decide (min s.fdLimit 2147483648 ≥ minRunChildFdSlack flags + Int.ofNat s.fds.length) = true →
                  (cwd? = some [] →
                    s'.status = .exited 127#i32 ∧
                    appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc = expectedFailureWireBytes 6#u8 ENOENT) ∧
                  (cwd? = none → path = [] →
                    s'.status = .exited 127#i32 ∧
                    appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc = expectedFailureWireBytes 7#u8 ENOENT))
            | .stream _ true true _ =>
              if !validFlagsSpec flags then s'.status = .exited 127#i32 else True
            | _ => True := by
  by_cases hBrokenBad : ¬ repW < 0#i32 ∧ ((!validFlagsSpec flags) = true) ∧
      ∃ repEnt rd rem, s.getFd repW.val = some repEnt ∧ s.getDesc repEnt.desc = .stream rd true true rem
  · rcases hBrokenBad with ⟨hRep, hBad, repEnt, rd, rem, hRepFd, hDesc⟩
    simp only [hRep, ↓reduceIte, hRepFd, hDesc]
    exact okPost_mono
      (run_child_broken_rep_bad_flags s hRun flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp hRep hBad)
      fun _ hs' => by simp only [hBad, ↓reduceIte]; exact hs'
  · unfold postfork.child.run_child
    refine okPost_bind
      (okPost_and
        (run_child_pre_sync_oracle_empty s hRun hOr flags syncR inFd outFd errFd repW closeFds keepFds)
        (run_child_pre_sync_safety s hRun flags syncR inFd outFd errFd repW closeFds keepFds))
      fun p ⟨hPreOr, hSafePre⟩ => ?_
    rcases p with ⟨b, s1⟩
    dsimp only at hPreOr hSafePre ⊢
    by_cases hRep : repW < 0#i32
    · simp only [hRep, ↓reduceIte] at hPreOr ⊢
      rcases hPreOr with ⟨rfl, hSt, hWl⟩
      exact okPost_ok _ _ ⟨hSt, hWl⟩
    · simp only [hRep, ↓reduceIte] at hPreOr ⊢
      cases hRepFd : s.getFd repW.val with
      | none =>
        exact okPost_mono (run_child_tail_trivial s s1 b flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp hSafePre)
          fun _ _ => trivial
      | some repEnt =>
        cases hDesc : s.getDesc repEnt.desc with
        | directory _ | procSelfFd _ =>
          exact okPost_mono (run_child_tail_trivial s s1 b flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp hSafePre)
            fun _ _ => by simp only [hDesc]
        | stream rd wr bp rem =>
          cases wr
          · exact okPost_mono (run_child_tail_trivial s s1 b flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp hSafePre)
              fun _ _ => by simp only [hDesc]
          · cases bp
            · simp only [hRepFd, hDesc] at hPreOr ⊢
              by_cases hValFl : !validFlagsSpec flags
              · simp only [hValFl, ↓reduceIte] at hPreOr ⊢
                rcases hPreOr with ⟨rfl, hSt, hApp⟩
                exact okPost_ok _ _ ⟨hSt, hApp⟩
              · simp only [hValFl, Bool.false_eq_true, ↓reduceIte] at hPreOr ⊢
                by_cases hValSg : !validSignsSpec flags syncR inFd outFd errFd
                · simp only [hValSg, ↓reduceIte] at hPreOr ⊢
                  rcases hPreOr with ⟨rfl, hSt, hApp⟩
                  exact okPost_ok _ _ ⟨hSt, hApp⟩
                · simp only [hValSg, Bool.false_eq_true, ↓reduceIte] at hPreOr ⊢
                  by_cases hValOv : !validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds.val keepFds.val
                  · simp only [hValOv, ↓reduceIte] at hPreOr ⊢
                    rcases hPreOr with ⟨rfl, hSt, hApp⟩
                    exact okPost_ok _ _ ⟨hSt, hApp⟩
                  · simp only [hValOv, Bool.false_eq_true, ↓reduceIte] at hPreOr ⊢
                    by_cases hSess : (flagSet flags FLAG_SET_PGID && decide (s.pid > 0) && decide (s.pid = s.sid)) = true
                    · simp only [hSess, ↓reduceIte] at hPreOr ⊢
                      rcases hPreOr with ⟨rfl, hSt, hApp⟩
                      exact okPost_ok _ _ ⟨hSt, hApp⟩
                    · simp only [hSess, Bool.false_eq_true, ↓reduceIte] at hPreOr ⊢
                      by_cases hFdsBad : ((flagSet flags FLAG_HAS_SYNC_BARRIER && !s.isOpen syncR.val) ||
                          (flagSet flags FLAG_REDIRECT_STDIO && (!s.isOpen inFd.val || !s.isOpen outFd.val || !s.isOpen errFd.val)) ||
                          keepFds.val.any (fun k => decide (0#i32 ≤ k) && !s.isOpen k.val)) = true
                      · simp only [hFdsBad, ↓reduceIte] at hPreOr ⊢
                        rcases hPreOr with ⟨rfl, hSt, hApp⟩
                        exact okPost_ok _ _ ⟨hSt, hApp⟩
                      · simp only [hFdsBad, Bool.false_eq_true, ↓reduceIte] at hPreOr ⊢
                        by_cases hSync : flagSet flags FLAG_HAS_SYNC_BARRIER = true
                        · simp only [hSync, ↓reduceIte] at hPreOr ⊢
                          cases hSyncFd : s.getFd syncR.val with
                          | none =>
                            exact okPost_mono (run_child_tail_trivial s s1 b flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp hSafePre)
                              fun _ _ => trivial
                          | some syncEnt =>
                            cases hSyncDesc : s.getDesc syncEnt.desc with
                            | directory _ | procSelfFd _ =>
                              exact okPost_mono (run_child_tail_trivial s s1 b flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp hSafePre)
                                fun _ _ => by simp only [hSyncDesc]
                            | stream sr sw sb srem =>
                              cases sr
                              · exact okPost_mono (run_child_tail_trivial s s1 b flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp hSafePre)
                                  fun _ _ => by simp only [hSyncDesc]
                              · cases srem with
                                | nil =>
                                  simp only [hSyncFd, hSyncDesc] at hPreOr ⊢
                                  rcases hPreOr with ⟨rfl, hSt, hWl, hCl⟩
                                  exact okPost_ok _ _ ⟨hSt, hWl, hCl⟩
                                | cons b0 r0 =>
                                  simp only [hSyncFd, hSyncDesc] at hPreOr ⊢
                                  rcases hPreOr with ⟨rfl, hPreOk, _, _, _⟩
                                  change PreSyncOkPost s flags syncR inFd outFd errFd repW closeFds.val keepFds.val s1 at hSafePre
                                  by_cases hNoCap : (flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 &&
                                      !s.closeRangeSupported && !s.procSelfFdAvailable &&
                                      decide (min s.fdLimit 2147483648 ≥ minRunChildFdSlack flags + Int.ofNat s.fds.length)) = true
                                  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hNoCap
                                    refine okPost_mono
                                      ((run_child_stage_failures_after_pre s s1 flags syncR inFd outFd errFd repW
                                        closeFds keepFds cwd? path argv envp hOr hPreOk hRepFd hDesc hNoCap.2).1
                                        (by simp [hNoCap.1.1.1, hNoCap.1.1.2, hNoCap.1.2]))
                                      fun s' hs' _ => hs'
                                  · exact okPost_mono
                                      (run_child_post_sync_safety s s1 flags syncR inFd outFd errFd repW
                                        closeFds.val keepFds cwd? path argv envp hSafePre)
                                      fun _ _ hCond => absurd hCond hNoCap
                        · have hSyncF : flagSet flags FLAG_HAS_SYNC_BARRIER = false := Bool.eq_false_iff.mpr hSync
                          simp only [hSyncF, Bool.false_eq_true, ↓reduceIte] at hPreOr ⊢
                          rcases hPreOr with ⟨rfl, hPreOk, _, _⟩
                          change PreSyncOkPost s flags syncR inFd outFd errFd repW closeFds.val keepFds.val s1 at hSafePre
                          by_cases hSlack : min s.fdLimit 2147483648 ≥ minRunChildFdSlack flags + Int.ofNat s.fds.length
                          · have hPairs := run_child_stage_failures_after_pre s s1 flags syncR inFd outFd errFd repW
                              closeFds keepFds cwd? path argv envp hOr hPreOk hRepFd hDesc hSlack
                            by_cases hNoCap : (flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 &&
                                !s.closeRangeSupported && !s.procSelfFdAvailable) = true
                            · refine okPost_mono (hPairs.1 hNoCap) fun s' hs' => ⟨fun _ => hs', fun hC => ?_⟩
                              exfalso
                              simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
                                decide_eq_true_eq] at hNoCap hC
                              rcases hC.1 with (h1 | h2) | h3
                              · rw [h1] at hNoCap; cases hNoCap.1.1
                              · rw [h2] at hNoCap; cases hNoCap.1.2
                              · rw [h3] at hNoCap; cases hNoCap.2
                            · have hCap : (!flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 ||
                                  s.closeRangeSupported || s.procSelfFdAvailable) = true := by
                                by_contra hCF
                                apply hNoCap
                                simp only [Bool.or_eq_true, Bool.not_eq_true'] at hCF
                                push Not at hCF
                                simp only [Bool.and_eq_true, Bool.not_eq_true']
                                exact ⟨⟨by cases hU : flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 <;> simp_all,
                                  by cases hC : s.closeRangeSupported <;> simp_all⟩,
                                  by cases hP : s.procSelfFdAvailable <;> simp_all⟩
                              cases cwd? with
                              | some dir =>
                                cases dir with
                                | nil =>
                                  have hPairs0 := run_child_stage_failures_after_pre s s1 flags syncR inFd outFd errFd repW
                                    closeFds keepFds (some []) path argv envp hOr hPreOk hRepFd hDesc hSlack
                                  refine okPost_mono ((hPairs0.2 hCap).1 rfl) fun s' hs' => ?_
                                  exact ⟨fun hN => by exfalso; rw [Bool.and_eq_true] at hN; exact hNoCap hN.1,
                                    fun _ => ⟨fun _ => hs', fun h => by cases h⟩⟩
                                | cons hd tl =>
                                  refine okPost_mono
                                    (run_child_post_sync_safety s s1 flags syncR inFd outFd errFd repW
                                      closeFds.val keepFds (some (hd :: tl)) path argv envp hSafePre)
                                    fun _ _ => ?_
                                  refine ⟨fun hN => by exfalso; rw [Bool.and_eq_true] at hN; exact hNoCap hN.1,
                                    fun _ => ?_⟩
                                  refine ⟨fun h => by simp at h, fun h => by cases h⟩
                              | none =>
                                cases path with
                                | nil =>
                                  have hPairs0 := run_child_stage_failures_after_pre s s1 flags syncR inFd outFd errFd repW
                                    closeFds keepFds none [] argv envp hOr hPreOk hRepFd hDesc hSlack
                                  refine okPost_mono ((hPairs0.2 hCap).2 rfl rfl) fun s' hs' => ?_
                                  refine ⟨fun hN => by exfalso; rw [Bool.and_eq_true] at hN; exact hNoCap hN.1,
                                    fun _ => ?_⟩
                                  refine ⟨(fun h => by cases h), fun _ _ => hs'⟩
                                | cons hp0 hpt =>
                                  refine okPost_mono
                                    (run_child_post_sync_safety s s1 flags syncR inFd outFd errFd repW
                                      closeFds.val keepFds none (hp0 :: hpt) argv envp hSafePre)
                                    fun _ _ => ?_
                                  refine ⟨fun hN => by exfalso; rw [Bool.and_eq_true] at hN; exact hNoCap hN.1,
                                    fun _ => ?_⟩
                                  refine ⟨(fun h => by cases h), fun _ h => by simp at h⟩
                          · refine okPost_mono
                              (run_child_post_sync_safety s s1 flags syncR inFd outFd errFd repW
                                closeFds.val keepFds cwd? path argv envp hSafePre)
                              fun _ _ =>
                                ⟨fun hN => by
                                  exfalso; rw [Bool.and_eq_true, decide_eq_true_eq] at hN
                                  exact hSlack (decide_eq_true_eq.mp hN.2),
                                 fun hC => by
                                  exfalso; rw [Bool.and_eq_true, decide_eq_true_eq] at hC
                                  exact hSlack (decide_eq_true_eq.mp hC.2)⟩
            · by_cases hValFl : !validFlagsSpec flags
              · exfalso
                exact hBrokenBad ⟨hRep, hValFl, repEnt, rd, rem, hRepFd, hDesc⟩
              · simp only [hValFl, Bool.false_eq_true, ↓reduceIte]
                exact okPost_mono (run_child_tail_trivial s s1 b flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp hSafePre)
                  fun _ _ => by simp only [hDesc]

/-- Zero-hypothesis verification of `test_postfork_runChild_safetyAndExecPost` on `rustAeneasApi`. -/
theorem test_postfork_runChild_safetyAndExecPost_allPass :
    Core.AllPass (test_postfork_runChild_safetyAndExecPost rustAeneasApi) := by
  dsimp [Core.AllPass, Core.AllPassRun, test_postfork_runChild_safetyAndExecPost, rustAeneasApi,
    Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert, Bind.bind, Pure.pure]
  intro s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp
  by_cases hRun : s.status = .running
  · have hB : (s.status == Status.running) = true := beq_iff_eq.mpr hRun
    simp only [hB, ↓reduceIte]
    exact ⟨run_child_safety_core s hRun flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp,
      fun hPre => ⟨run_child_exec s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp hPre, trivial⟩⟩
  · have hB : (s.status == Status.running) = false := beq_false_of_ne hRun
    simp only [hB, Bool.false_eq_true, ↓reduceIte]
    exact ⟨run_child_total s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp,
      fun hPre => ⟨run_child_exec s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp hPre, trivial⟩⟩

/-- Witness reachability for `test_postfork_runChild_safetyAndExecPost`. -/
theorem test_postfork_runChild_safetyAndExecPost_canReach :
    Core.CanReach (test_postfork_runChild_safetyAndExecPost rustAeneasApi) := by
  let s₀ : ChildState :=
    { status := .running, oracle := [], fdLimit := 64,
      fds := [(0, { desc := 10, cloexec := false })],
      descs := [(10, .stream false true false [])] }
  let sl0 : Slice I32 := Slice.from [] (by simp)
  have hPre : ValidRunChildExecPre s₀ 0#u32 0#i32 0#i32 0#i32 0#i32 0#i32 [] [] none [47#u8] := by
    refine ⟨rfl, rfl, (by decide), (by decide), (by decide), (by decide),
      (fun h => by simp [flagSet, FLAG_SET_PGID] at h), (by decide),
      (fun h => by simp [flagSet, FLAG_CLOSE_UNKEPT_ABOVE2] at h), (by decide),
      (fun h => by simp [flagSet, FLAG_REDIRECT_STDIO] at h),
      (fun _ hk => by cases hk),
      (fun h => by simp [flagSet, FLAG_HAS_SYNC_BARRIER] at h),
      (by decide), (fun _ h => by cases h)⟩
  have hAll := test_postfork_runChild_safetyAndExecPost_allPass
    s₀ 0#u32 0#i32 0#i32 0#i32 0#i32 0#i32 sl0 sl0 none [47#u8] [] []
  dsimp [Core.AllPass, Core.AllPassRun, test_postfork_runChild_safetyAndExecPost, rustAeneasApi,
    Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert, Bind.bind, Pure.pure] at hAll
  dsimp [Core.CanReach, Core.CanReachRun, test_postfork_runChild_safetyAndExecPost, rustAeneasApi,
    Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert, Bind.bind, Pure.pure]
  exact ⟨s₀, 0#u32, 0#i32, 0#i32, 0#i32, 0#i32, 0#i32, sl0, sl0, none, [47#u8], [], [],
    hAll.1, hPre, hAll.2 hPre⟩

/-- Zero-hypothesis verification of `test_postfork_runChild_validationStagesAndBarrier` on `rustAeneasApi`. -/
theorem test_postfork_runChild_validationStagesAndBarrier_allPass :
    Core.AllPass (test_postfork_runChild_validationStagesAndBarrier rustAeneasApi) := by
  dsimp [Core.AllPass, Core.AllPassRun, test_postfork_runChild_validationStagesAndBarrier, rustAeneasApi,
    Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert, Bind.bind, Pure.pure]
  intro s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp ⟨hRun, hOr⟩
  have hBase := fun c p =>
    run_child_validation_stages_spec s hRun hOr flags syncR inFd outFd errFd repW closeFds keepFds c p argv envp
  by_cases hRep : repW < 0#i32
  · simp only [hRep, decide_true, ↓reduceIte]
    have hb := hBase cwd? path
    simp only [hRep, ↓reduceIte] at hb
    exact ⟨hb, trivial⟩
  · simp only [hRep, decide_false, Bool.false_eq_true, ↓reduceIte]
    cases hRepFd : s.getFd repW.val with
    | none => try trivial
    | some repEnt =>
      dsimp only
      cases hDesc : s.getDesc repEnt.desc with
      | directory _ | procSelfFd _ => try trivial
      | stream rd wr bp rem =>
        cases wr
        · try trivial
        · cases bp
          · dsimp only
            by_cases hValFl : !validFlagsSpec flags
            · simp only [hValFl, ↓reduceIte]
              have hb := hBase cwd? path
              simp only [hRep, hRepFd, hDesc, hValFl, ↓reduceIte] at hb
              exact ⟨hb, trivial⟩
            · simp only [hValFl, Bool.false_eq_true, ↓reduceIte]
              by_cases hValSg : !validSignsSpec flags syncR inFd outFd errFd
              · simp only [hValSg, ↓reduceIte]
                have hb := hBase cwd? path
                simp only [hRep, hRepFd, hDesc, hValFl, hValSg, Bool.false_eq_true, ↓reduceIte] at hb
                exact ⟨hb, trivial⟩
              · simp only [hValSg, Bool.false_eq_true, ↓reduceIte]
                by_cases hValOv : !validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds.val keepFds.val
                · simp only [hValOv, ↓reduceIte]
                  have hb := hBase cwd? path
                  simp only [hRep, hRepFd, hDesc, hValFl, hValSg, hValOv, Bool.false_eq_true, ↓reduceIte] at hb
                  exact ⟨hb, trivial⟩
                · simp only [hValOv, Bool.false_eq_true, ↓reduceIte]
                  by_cases hSess : (flagSet flags FLAG_SET_PGID && decide (s.pid > 0) && decide (s.pid = s.sid)) = true
                  · simp only [hSess, ↓reduceIte]
                    have hb := hBase cwd? path
                    simp only [hRep, hRepFd, hDesc, hValFl, hValSg, hValOv, hSess, Bool.false_eq_true, ↓reduceIte] at hb
                    exact ⟨hb, trivial⟩
                  · simp only [hSess, Bool.false_eq_true, ↓reduceIte]
                    by_cases hFdsBad : ((flagSet flags FLAG_HAS_SYNC_BARRIER && !s.isOpen syncR.val) ||
                        (flagSet flags FLAG_REDIRECT_STDIO && (!s.isOpen inFd.val || !s.isOpen outFd.val || !s.isOpen errFd.val)) ||
                        keepFds.val.any (fun k => decide (0#i32 ≤ k) && !s.isOpen k.val)) = true
                    · simp only [hFdsBad, ↓reduceIte]
                      have hb := hBase cwd? path
                      simp only [hRep, hRepFd, hDesc, hValFl, hValSg, hValOv, hSess, hFdsBad, Bool.false_eq_true, ↓reduceIte] at hb
                      exact ⟨hb, trivial⟩
                    · simp only [hFdsBad, Bool.false_eq_true, ↓reduceIte]
                      by_cases hSync : flagSet flags FLAG_HAS_SYNC_BARRIER = true
                      · simp only [hSync, ↓reduceIte]
                        cases hSyncFd : s.getFd syncR.val with
                        | none => try trivial
                        | some syncEnt =>
                          dsimp only
                          cases hSyncDesc : s.getDesc syncEnt.desc with
                          | directory _ | procSelfFd _ => try trivial
                          | stream sr sw sb srem =>
                            cases sr
                            · try trivial
                            · cases srem with
                              | nil =>
                                dsimp only
                                have hb := hBase cwd? path
                                simp only [hRep, hRepFd, hDesc, hValFl, hValSg, hValOv, hSess, hFdsBad, Bool.false_eq_true, ↓reduceIte] at hb
                                simp only [hSync, hSyncFd, hSyncDesc, ↓reduceIte] at hb
                                exact ⟨hb, trivial⟩
                              | cons b0 r0 =>
                                dsimp only
                                by_cases hC5 : (flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 &&
                                    !s.closeRangeSupported && !s.procSelfFdAvailable &&
                                    decide (min s.fdLimit 2147483648 ≥ minRunChildFdSlack flags + (s.fds.length : Int))) = true
                                · simp only [hC5, ↓reduceIte]
                                  have hb := hBase cwd? path
                                  simp only [hRep, hRepFd, hDesc, hValFl, hValSg, hValOv, hSess, hFdsBad, Bool.false_eq_true, ↓reduceIte] at hb
                                  simp only [hSync, hSyncFd, hSyncDesc, ↓reduceIte] at hb
                                  exact ⟨okPost_mono hb (fun _ h => h hC5), trivial⟩
                                · simp only [hC5, Bool.false_eq_true, ↓reduceIte]
                      · have hSyncF : flagSet flags FLAG_HAS_SYNC_BARRIER = false := Bool.eq_false_iff.mpr hSync
                        simp only [hSyncF, Bool.false_eq_true, ↓reduceIte]
                        by_cases hC5 : (flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 &&
                            !s.closeRangeSupported && !s.procSelfFdAvailable &&
                            decide (min s.fdLimit 2147483648 ≥ minRunChildFdSlack flags + (s.fds.length : Int))) = true
                        · simp only [hC5, ↓reduceIte]
                          have hb := hBase cwd? path
                          simp only [hRep, hRepFd, hDesc, hValFl, hValSg, hValOv, hSess, hFdsBad, Bool.false_eq_true, ↓reduceIte] at hb
                          simp only [hSyncF, Bool.false_eq_true, ↓reduceIte] at hb
                          exact ⟨okPost_mono hb (fun _ h => h.1 hC5), trivial⟩
                        · simp only [hC5, Bool.false_eq_true, ↓reduceIte]
                          by_cases hC67 : ((!flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 ||
                              s.closeRangeSupported || s.procSelfFdAvailable) &&
                              decide (min s.fdLimit 2147483648 ≥ minRunChildFdSlack flags + (s.fds.length : Int))) = true
                          · simp only [hC67, ↓reduceIte]
                            have h6 := hBase (some []) path
                            have h7 := hBase none []
                            simp only [hRep, hRepFd, hDesc, hValFl, hValSg, hValOv, hSess, hFdsBad, Bool.false_eq_true, ↓reduceIte] at h6 h7
                            simp only [hSyncF, Bool.false_eq_true, ↓reduceIte] at h6 h7
                            exact ⟨okPost_mono h6 (fun _ h => (h.2 hC67).1 trivial),
                              okPost_mono h7 (fun _ h => (h.2 hC67).2 trivial trivial), trivial⟩
                          · simp only [hC67, Bool.false_eq_true, ↓reduceIte]
          · dsimp only
            by_cases hValFl : !validFlagsSpec flags
            · simp only [hValFl, ↓reduceIte]
              have hb := hBase cwd? path
              simp only [hRep, hRepFd, hDesc, hValFl, ↓reduceIte] at hb
              exact ⟨hb, trivial⟩
            · simp only [hValFl, Bool.false_eq_true, ↓reduceIte]

/-- Witness reachability for `test_postfork_runChild_validationStagesAndBarrier`. -/
theorem test_postfork_runChild_validationStagesAndBarrier_canReach :
    Core.CanReach (test_postfork_runChild_validationStagesAndBarrier rustAeneasApi) := by
  let s₀ : ChildState :=
    { status := .running, oracle := [], fdLimit := 64,
      fds := [(0, { desc := 10, cloexec := false })],
      descs := [(10, .stream false true false [])] }
  let sl0 : Slice I32 := Slice.from [] (by simp)
  have hAll := test_postfork_runChild_validationStagesAndBarrier_allPass
    s₀ 0#u32 0#i32 0#i32 0#i32 0#i32 0#i32 sl0 sl0 none [47#u8] [] [] ⟨rfl, rfl⟩
  dsimp only [Core.AllPass, Core.AllPassRun, test_postfork_runChild_validationStagesAndBarrier,
    rustAeneasApi, Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert,
    Bind.bind, Pure.pure] at hAll
  dsimp only [Core.CanReach, Core.CanReachRun, test_postfork_runChild_validationStagesAndBarrier,
    rustAeneasApi, Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert,
    Bind.bind, Pure.pure]
  exact ⟨s₀, 0#u32, 0#i32, 0#i32, 0#i32, 0#i32, 0#i32, sl0, sl0, none, [47#u8], [], [], ⟨rfl, rfl⟩, hAll⟩

end PostSyncAndRunChild

end LeanSwe.PostFork.Proofs
