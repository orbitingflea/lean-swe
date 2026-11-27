import LeanSweProofs.PostFork.Proofs.FdOps

/-!
# PostFork `/proc/self/fd` Fallback and `close_fds_above2_except` Proofs

Total and functional correctness specifications for `close_dirent_batch`,
`close_via_proc_self_fd`, and `close_fds_above2_except`, plus zero-hypothesis
`AllPass` and `CanReach` proofs for
`test_postfork_closeFdsAbove2Except_closeRangeAndProcFallback`.
-/

namespace LeanSwe.PostFork.Proofs

open _root_.Aeneas _root_.Aeneas.Std Result ControlFlow Error
open LeanSwe.PostFork
open LeanSwe.PostFork.Aeneas.Internal
open LeanSwe.PostFork.Aeneas.Internal.World
open LeanSwe.PostFork.Aeneas
open LeanSwe.PostFork.Aeneas.Model

private theorem usize_max_ge_close : 4294967295 ≤ Usize.max := by
  have h1 := Usize.cMax_bound.1
  have h2 : UScalar.cMax UScalarTy.Usize = 4294967295 := by decide
  omega

private theorem usize_bits_ge32 : 32 ≤ UScalarTy.Usize.numBits := by
  change 32 ≤ System.Platform.numBits
  cases System.Platform.numBits_eq with
  | inl h => simp [h]
  | inr h => simp [h]

private theorem usize_shl8_ok (hi : Usize) :
    ∃ sh : Usize, hi <<< 8#i32 = Result.ok sh := by
  change ∃ sh, UScalar.shiftLeft_IScalar hi 8#i32 = Result.ok sh
  unfold UScalar.shiftLeft_IScalar
  have hge : (8#i32 : I32).val ≥ 0 := by decide
  simp only [hge, ↓reduceIte]
  unfold UScalar.shiftLeft
  have hlt : (8#i32 : I32).toNat < UScalarTy.Usize.numBits := by
    have : (8#i32 : I32).toNat = 8 := by decide
    have := usize_bits_ge32
    omega
  simp only [hlt, ↓reduceIte]
  exact ⟨_, rfl⟩

private theorem usize_zero_shl8 : (0#usize : Usize) <<< 8#i32 = Result.ok 0#usize := by
  change UScalar.shiftLeft_IScalar 0#usize 8#i32 = Result.ok 0#usize
  unfold UScalar.shiftLeft_IScalar
  have hge : (8#i32 : I32).val ≥ 0 := by decide
  simp only [hge, ↓reduceIte]
  unfold UScalar.shiftLeft
  have hlt : (8#i32 : I32).toNat < UScalarTy.Usize.numBits := by
    have : (8#i32 : I32).toNat = 8 := by decide
    have := usize_bits_ge32
    omega
  simp only [hlt, ↓reduceIte]
  rfl

private theorem sys_close_run_preserves (s : ChildState) (hRun : s.status = .running) (fd : I32) :
    ∃ r s', sys.close s fd = Result.ok (r, s') ∧
      SameChildConfig s' s ∧
      s'.pgid = s.pgid ∧ s'.cwd = s.cwd ∧ s'.sig = s.sig ∧
      s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
      s.trace.length ≤ s'.trace.length ∧
      (∀ k : Int, k ≠ fd.val → s'.getFd k = s.getFd k) ∧
      (∀ k : Int, s'.isOpen k = true → s.isOpen k = true) ∧
      ((∀ rawE, currentFault s ≠ .seccomp rawE) →
        ∀ k : Int, s'.getFd k = if k == fd.val then none else s.getFd k) := by
  rcases sys_close_running s hRun fd with ⟨r, s', hEq, hCfg, hPgid, hCwd, hSig, hDescs, hWl, hTr, hFds, _⟩
  refine ⟨r, s', hEq, hCfg, hPgid, hCwd, hSig, hDescs, hWl, by rw [hTr]; omega, ?_, ?_, ?_⟩
  · intro k hne
    cases hf : currentFault s with
    | seccomp _ =>
      simp only [hf] at hFds
      simp [ChildState.getFd, hFds]
    | normal | fail _ | partialWrite _ | dentsBatch _ =>
      simp only [hf] at hFds
      rw [show s'.getFd k = (s.closeSlot fd.val).getFd k from by simp [ChildState.getFd, hFds]]
      exact getFd_closeSlot_ne s hne
  · intro k hk
    cases hf : currentFault s with
    | seccomp _ =>
      simp only [hf] at hFds
      simpa [ChildState.isOpen, ChildState.getFd, hFds] using hk
    | normal | fail _ | partialWrite _ | dentsBatch _ =>
      simp only [hf] at hFds
      simp only [ChildState.isOpen, ChildState.getFd, hFds] at hk ⊢
      change ((s.closeSlot fd.val).getFd k).isSome = true at hk
      by_cases hkf : k = fd.val
      · subst hkf; rw [getFd_closeSlot_self] at hk; cases hk
      · rw [getFd_closeSlot_ne s hkf] at hk; exact hk
  · intro hNoSec k
    cases hf : currentFault s with
    | seccomp rawE' => exact absurd hf (hNoSec rawE')
    | normal | fail _ | partialWrite _ | dentsBatch _ =>
      simp only [hf] at hFds
      rw [show s'.getFd k = (s.closeSlot fd.val).getFd k from by simp [ChildState.getFd, hFds]]
      by_cases hkf : k == fd.val
      · have hEqk : k = fd.val := beq_iff_eq.mp hkf
        subst hEqk
        simp only [beq_self_eq_true, ↓reduceIte]
        exact getFd_closeSlot_self s fd.val
      · have hNek : k ≠ fd.val := fun h => hkf (beq_iff_eq.mpr h)
        simp only [hkf, Bool.false_eq_true, ↓reduceIte]
        exact getFd_closeSlot_ne s hNek

private theorem sys_close_total_loc (s : sys.Sys) (fd : I32) :
    ∃ r s', sys.close s fd = Result.ok (r, s') ∧
      SameChildConfig s' s ∧
      s'.pgid = s.pgid ∧ s'.cwd = s.cwd ∧ s'.sig = s.sig ∧
      s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
      s.trace.length ≤ s'.trace.length ∧
      (∀ k : Int, k ≠ fd.val → s'.getFd k = s.getFd k) ∧
      (∀ k : Int, s'.isOpen k = true → s.isOpen k = true) := by
  by_cases hRun : s.status = .running
  · rcases sys_close_run_preserves s hRun fd with
      ⟨r, s', hEq, hCfg, hPgid, hCwd, hSig, hDescs, hWl, hTr, hNe, hOpen, _⟩
    exact ⟨r, s', hEq, hCfg, hPgid, hCwd, hSig, hDescs, hWl, hTr, hNe, hOpen⟩
  · rw [sys_close_not_running s hRun fd]
    exact ⟨.Ok (), s, rfl, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl,
      Nat.le_refl _, fun _ _ => rfl, fun _ h => h⟩

private theorem sys_close_running_exact (s : ChildState) (hs : s.status = Status.running) (fd : I32) :
    ∃ r s', sys.close s fd = Result.ok (r, s') ∧
      SameChildConfig s' s ∧
      s'.pgid = s.pgid ∧ s'.cwd = s.cwd ∧ s'.sig = s.sig ∧
      s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
      s'.trace.length = s.trace.length + 1 ∧
      s'.fds = (match currentFault s with
        | StepFault.seccomp _ => s.fds
        | _ => (s.closeSlot fd.val).fds) ∧
      (r = .Ok () → ∀ rawE, currentFault s ≠ .seccomp rawE ∧ currentFault s ≠ .fail rawE) ∧
      ((∀ rawE, currentFault s ≠ .seccomp rawE ∧ currentFault s ≠ .fail rawE) →
        s.isOpen fd.val = true → r = .Ok ()) := by
  rcases sys_close_running s hs fd with
    ⟨r, s', hEq, hCfg, hPgid, hCwd, hSig, hDescs, hWl, hTr, hFds, _⟩
  refine ⟨r, s', hEq, hCfg, hPgid, hCwd, hSig, hDescs, hWl, hTr, hFds, ?_, ?_⟩
  · intro hr rawE
    unfold sys.close LeanSwe.PostFork.Aeneas.Internal.Sys.close runUnitSyscall at hEq
    simp only [hs] at hEq
    cases hf : currentFault s with
    | seccomp e =>
      simp only [hf, Result.ok.injEq, Prod.mk.injEq] at hEq
      rcases hEq with ⟨rfl, _⟩
      cases hr
    | fail e =>
      simp only [hf] at hEq
      cases hOpen : s.isOpen fd.val <;>
        simp only [hOpen, ↓reduceIte, Bool.false_eq_true, Result.ok.injEq, Prod.mk.injEq] at hEq <;>
        rcases hEq with ⟨rfl, _⟩ <;> cases hr
    | normal | partialWrite _ | dentsBatch _ =>
      exact ⟨(fun h => (by cases h)), (fun h => (by cases h))⟩
  · intro hNF hOpen
    unfold sys.close LeanSwe.PostFork.Aeneas.Internal.Sys.close runUnitSyscall at hEq
    simp only [hs, hOpen, ↓reduceIte] at hEq
    cases hf : currentFault s with
    | seccomp e => exact absurd hf (hNF e).1
    | fail e => exact absurd hf (hNF e).2
    | normal | partialWrite _ | dentsBatch _ =>
      simp only [hf, Result.ok.injEq, Prod.mk.injEq] at hEq
      exact hEq.1.symm

private theorem close_dirent_batch_loop_total (buf : Array U8 256#usize) (n : Usize)
    (hn : n.val ≤ 256) (dirfd extra_keep_fd : I32) (keep_fds : Slice I32)
    (s0 : sys.Sys) (pos0 : Usize) (err : I32) (hpos0 : pos0.val ≤ n.val) :
    OkPost (postfork.fd_ops.close_dirent_batch_loop s0 buf n dirfd extra_keep_fd keep_fds pos0 err)
      fun p => SameChildConfig p.1 s0 ∧ p.1.pgid = s0.pgid ∧ p.1.cwd = s0.cwd ∧
        p.1.sig = s0.sig ∧ p.1.descs = s0.descs ∧ p.1.writeLog = s0.writeLog ∧
        s0.trace.length ≤ p.1.trace.length ∧
        p.1.getFd dirfd.val = s0.getFd dirfd.val ∧
        (∀ k : Int, p.1.isOpen k = true → s0.isOpen k = true) := by
  unfold postfork.fd_ops.close_dirent_batch_loop
  refine okPost_loop_decr_nat
    (fun p : sys.Sys × Usize => n.val - p.2.val)
    (fun p : sys.Sys × Usize => p.2.val ≤ n.val ∧ SameChildConfig p.1 s0 ∧
      p.1.pgid = s0.pgid ∧ p.1.cwd = s0.cwd ∧ p.1.sig = s0.sig ∧
      p.1.descs = s0.descs ∧ p.1.writeLog = s0.writeLog ∧
      s0.trace.length ≤ p.1.trace.length ∧
      p.1.getFd dirfd.val = s0.getFd dirfd.val ∧
      (∀ k : Int, p.1.isOpen k = true → s0.isOpen k = true))
    (fun r => SameChildConfig r.1 s0 ∧ r.1.pgid = s0.pgid ∧ r.1.cwd = s0.cwd ∧
      r.1.sig = s0.sig ∧ r.1.descs = s0.descs ∧ r.1.writeLog = s0.writeLog ∧
      s0.trace.length ≤ r.1.trace.length ∧
      r.1.getFd dirfd.val = s0.getFd dirfd.val ∧
      (∀ k : Int, r.1.isOpen k = true → s0.isOpen k = true))
    (fun p => postfork.fd_ops.close_dirent_batch_loop.body buf n dirfd extra_keep_fd keep_fds err p.1 p.2)
    (s0, pos0) ?_ ⟨hpos0, SameChildConfig.refl s0, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, rfl, fun _ h => h⟩
  intro ⟨s, pos⟩ ⟨hposLe, hCfg, hPgid, hCwd, hSig, hDescs, hWl, hTr, hDir, hSub⟩
  unfold postfork.fd_ops.close_dirent_batch_loop.body
  by_cases hlt : pos < n
  · simp only [hlt, ↓reduceIte]
    have hposLt : pos.val < n.val := hlt
    obtain ⟨i, hiEq, hiVal⟩ := (okPost_iff_wp_spec _ _).mpr (Usize.sub_spec (x := n) (y := pos) (by omega))
    rw [hiEq, bind_ok]
    by_cases hilt20 : i < 20#usize
    · simp only [hilt20, ↓reduceIte]
      exact okPost_ok _ _ ⟨hCfg, hPgid, hCwd, hSig, hDescs, hWl, hTr, hDir, hSub⟩
    · simp only [hilt20, ↓reduceIte]
      have hiGe20 : 20 ≤ i.val := by change ¬(i.val < 20) at hilt20; omega
      by_cases hposGt : pos > 236#usize
      · simp only [hposGt, ↓reduceIte]
        exact okPost_ok _ _ ⟨hCfg, hPgid, hCwd, hSig, hDescs, hWl, hTr, hDir, hSub⟩
      · simp only [hposGt, ↓reduceIte]
        have hposLe236 : pos.val ≤ 236 := by change ¬(pos.val > 236) at hposGt; omega
        have hMax := usize_max_ge_close
        have hBufLen : buf.length = 256 := by simp
        obtain ⟨i1, hi1Eq, hi1Val⟩ := (okPost_iff_wp_spec _ _).mpr
          (Usize.add_spec (x := pos) (y := 16#usize) (by change pos.val + 16 ≤ Usize.max; omega))
        rw [hi1Eq, bind_ok]
        have hi1Bound : i1.val < buf.length := by
          have h16 : (16#usize : Usize).val = 16 := rfl
          omega
        obtain ⟨i2, hi2Eq, _⟩ := (okPost_iff_wp_spec _ _).mpr (Array.index_usize_spec buf i1 hi1Bound)
        rw [hi2Eq, bind_ok]
        simp only [lift, bind_ok]
        obtain ⟨i3, hi3Eq, hi3Val⟩ := (okPost_iff_wp_spec _ _).mpr
          (Usize.add_spec (x := pos) (y := 17#usize) (by change pos.val + 17 ≤ Usize.max; omega))
        rw [hi3Eq, bind_ok]
        have hi3Bound : i3.val < buf.length := by
          have h17 : (17#usize : Usize).val = 17 := rfl
          omega
        obtain ⟨i4, hi4Eq, _⟩ := (okPost_iff_wp_spec _ _).mpr (Array.index_usize_spec buf i3 hi3Bound)
        rw [hi4Eq, bind_ok]
        rcases usize_shl8_ok (UScalar.cast .Usize i4) with ⟨sh, hSh⟩
        rw [hSh, bind_ok]
        set reclen : Usize := (UScalar.cast .Usize i2 : Usize) ||| sh
        by_cases hRecLt : reclen < 20#usize
        · simp only [hRecLt, ↓reduceIte]
          exact okPost_ok _ _ ⟨hCfg, hPgid, hCwd, hSig, hDescs, hWl, hTr, hDir, hSub⟩
        · simp only [hRecLt, ↓reduceIte]
          have hRecGe20 : 20 ≤ reclen.val := by change ¬(reclen.val < 20) at hRecLt; omega
          by_cases hRecGt : reclen > i
          · simp only [hRecGt, ↓reduceIte]
            exact okPost_ok _ _ ⟨hCfg, hPgid, hCwd, hSig, hDescs, hWl, hTr, hDir, hSub⟩
          · simp only [hRecGt, ↓reduceIte]
            have hRecLeI : reclen.val ≤ i.val := by change ¬(reclen.val > i.val) at hRecGt; omega
            obtain ⟨i6, hi6Eq, hi6Val⟩ := (okPost_iff_wp_spec _ _).mpr
              (Usize.add_spec (x := pos) (y := 19#usize) (by change pos.val + 19 ≤ Usize.max; omega))
            obtain ⟨i7, hi7Eq, hi7Val⟩ := (okPost_iff_wp_spec _ _).mpr
              (Usize.add_spec (x := pos) (y := reclen) (by omega))
            rw [hi6Eq, bind_ok, hi7Eq, bind_ok, parse_dirent_name_eq_expected, bind_ok]
            by_cases hMal : expectedDirentParse buf i6 i7 = postfork.fd_ops.DIRENT_MALFORMED
            · simp only [hMal, ↓reduceIte]
              exact okPost_ok _ _ ⟨hCfg, hPgid, hCwd, hSig, hDescs, hWl, hTr, hDir, hSub⟩
            · simp only [hMal, ↓reduceIte]
              have hRetRefl :
                  (i7.val ≤ n.val ∧ SameChildConfig s s0 ∧ s.pgid = s0.pgid ∧
                    s.cwd = s0.cwd ∧ s.sig = s0.sig ∧ s.descs = s0.descs ∧ s.writeLog = s0.writeLog ∧
                    s0.trace.length ≤ s.trace.length ∧ s.getFd dirfd.val = s0.getFd dirfd.val ∧
                    (∀ k : Int, s.isOpen k = true → s0.isOpen k = true)) ∧ n.val - i7.val < n.val - pos.val :=
                ⟨⟨by omega, hCfg, hPgid, hCwd, hSig, hDescs, hWl, hTr, hDir, hSub⟩,
                  by omega⟩
              by_cases hGt2 : expectedDirentParse buf i6 i7 > 2#i32
              · simp only [hGt2, ↓reduceIte]
                by_cases hNeDir : expectedDirentParse buf i6 i7 != dirfd
                · simp only [hNeDir, ↓reduceIte]
                  by_cases hNeExt : expectedDirentParse buf i6 i7 != extra_keep_fd
                  · simp only [hNeExt, ↓reduceIte]
                    refine okPost_bind (slice_contains_nonneg_spec keep_fds (expectedDirentParse buf i6 i7))
                      fun b _ => ?_
                    cases b
                    · simp only [Bool.false_eq_true, ↓reduceIte]
                      rcases sys_close_total_loc s (expectedDirentParse buf i6 i7) with
                        ⟨rCl, s2, hCl, hCfg2, hPgid2, hCwd2, hSig2, hDescs2, hWl2, hTr2, hGet2, hSub2⟩
                      rw [hCl, bind_ok]
                      have hNeFd : dirfd.val ≠ (expectedDirentParse buf i6 i7).val := by
                        intro hEq
                        exact absurd (IScalar.eq_of_val_eq hEq.symm) (bne_iff_ne.mp hNeDir)
                      cases rCl with
                      | Ok _ =>
                        exact okPost_ok _ _
                          ⟨⟨by dsimp only; omega, hCfg2.trans hCfg, hPgid2.trans hPgid,
                            hCwd2.trans hCwd, hSig2.trans hSig, hDescs2.trans hDescs,
                            hWl2.trans hWl, Nat.le_trans hTr hTr2, (hGet2 _ hNeFd).trans hDir,
                            fun k hk => hSub k (hSub2 k hk)⟩,
                           by dsimp only; omega⟩
                      | Err errCl =>
                        exact okPost_ok _ _ ⟨hCfg2.trans hCfg, hPgid2.trans hPgid,
                          hCwd2.trans hCwd, hSig2.trans hSig, hDescs2.trans hDescs,
                          hWl2.trans hWl, Nat.le_trans hTr hTr2, (hGet2 _ hNeFd).trans hDir,
                          fun k hk => hSub k (hSub2 k hk)⟩
                    · simp only [↓reduceIte]
                      exact okPost_ok _ _ hRetRefl
                  · simp only [hNeExt, Bool.false_eq_true, ↓reduceIte]
                    exact okPost_ok _ _ hRetRefl
                · simp only [hNeDir, Bool.false_eq_true, ↓reduceIte]
                  exact okPost_ok _ _ hRetRefl
              · simp only [hGt2, ↓reduceIte]
                exact okPost_ok _ _ hRetRefl
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok _ _ ⟨hCfg, hPgid, hCwd, hSig, hDescs, hWl, hTr, hDir, hSub⟩

/-- Totalness of `postfork.fd_ops.close_dirent_batch` for arbitrary `sys.Sys` and 256-byte buffers. -/
theorem close_dirent_batch_total (s : sys.Sys) (buf : Array U8 256#usize) (n : Usize)
    (dirfd extra_keep_fd : I32) (keep_fds : Slice I32) :
    OkPost (postfork.fd_ops.close_dirent_batch s buf n dirfd extra_keep_fd keep_fds) fun p =>
      SameChildConfig p.2 s ∧ p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧
      p.2.sig = s.sig ∧ p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
      s.trace.length ≤ p.2.trace.length ∧
      p.2.getFd dirfd.val = s.getFd dirfd.val ∧
      (∀ k : Int, p.2.isOpen k = true → s.isOpen k = true) := by
  unfold postfork.fd_ops.close_dirent_batch
  by_cases hGt : n > 256#usize
  · simp only [hGt, ↓reduceIte]
    exact okPost_ok _ _ ⟨SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, rfl, fun _ h => h⟩
  · simp only [hGt, ↓reduceIte]
    have hLe : n.val ≤ 256 := by change ¬(n.val > 256) at hGt; omega
    have h0Le : (0#usize : Usize).val ≤ n.val := by
      have : (0#usize : Usize).val = 0 := rfl
      omega
    refine okPost_bind
      (close_dirent_batch_loop_total buf n hLe dirfd extra_keep_fd keep_fds s 0#usize postfork.fd_ops.EIO h0Le)
      fun p hp => ?_
    rcases p with ⟨s1, err, bad⟩
    dsimp only at hp
    change OkPost (if bad then ok (core.result.Result.Err err, s1) else ok (core.result.Result.Ok (), s1)) _
    cases bad
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact okPost_ok _ _ hp
    · simp only [↓reduceIte]; exact okPost_ok _ _ hp

private theorem natDigitsFuel_len_le (fuel n : Nat) (acc : Bytes) :
    (natDigitsFuel fuel n acc).length ≤ fuel + acc.length := by
  induction fuel generalizing n acc with
  | zero => simp [natDigitsFuel]
  | succ f ih =>
    rw [natDigitsFuel]
    split
    · simp
    · exact Nat.le_trans (ih _ _) (by simp; omega)

private theorem natToAsciiBytes_len_le (n : Nat) : (natToAsciiBytes n).length ≤ 12 :=
  natDigitsFuel_len_le 12 n []

private theorem insertSortedInt_bounds (x : Int) (xs : List Int) (hx1 : 0 ≤ x) (hx2 : x ≤ 2147483647)
    (hxs : ∀ y ∈ xs, 0 ≤ y ∧ y ≤ 2147483647) :
    ∀ y ∈ insertSortedInt x xs, 0 ≤ y ∧ y ≤ 2147483647 := by
  induction xs with
  | nil =>
    intro y hy
    simp only [insertSortedInt, List.mem_singleton] at hy
    subst hy
    exact ⟨hx1, hx2⟩
  | cons a tail ih =>
    intro y hy
    unfold insertSortedInt at hy
    by_cases heq : (x == a) = true
    · simp only [heq, ↓reduceIte] at hy
      exact hxs y hy
    · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hy
      by_cases hlt : x < a
      · simp only [hlt, ↓reduceIte, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact ⟨hx1, hx2⟩
        · exact hxs y (by simp [hy])
      · simp only [hlt, ↓reduceIte, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hxs _ (by simp)
        · exact ih (fun z hz => hxs z (by simp [hz])) y hy

private theorem sortedOpenFds32_bounds (s : ChildState) :
    ∀ y ∈ sortedOpenFds32 s, 0 ≤ y ∧ y ≤ 2147483647 := by
  unfold sortedOpenFds32
  suffices h : ∀ (l : List (Int × FdEntry)) (acc : List Int),
      (∀ y ∈ acc, 0 ≤ y ∧ y ≤ 2147483647) →
      ∀ y ∈ l.foldl (fun a p => if 0 ≤ p.1 && p.1 ≤ 2147483647 then insertSortedInt p.1 a else a) acc,
        0 ≤ y ∧ y ≤ 2147483647 from h s.fds [] (fun _ h0 => nomatch h0)
  intro l
  induction l with
  | nil => intro acc hacc y hy; exact hacc y hy
  | cons p ps ih =>
    intro acc hacc y hy
    dsimp only [List.foldl] at hy
    apply ih _ _ y hy
    split
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact insertSortedInt_bounds p.1 acc hc.1 hc.2 hacc
    · exact hacc

private theorem procSelfFdEntriesFrom_bounds (s : ChildState) (cursor : Int) :
    ∀ p ∈ procSelfFdEntriesFrom s cursor,
      cursor ≤ p.1 ∧ -2 ≤ p.1 ∧ p.1 ≤ 2147483647 ∧ p.2.length ≤ 12 := by
  intro p hp
  unfold procSelfFdEntriesFrom at hp
  simp only [List.mem_filter, decide_eq_true_eq, List.mem_append, List.mem_cons,
    List.mem_nil_iff, or_false, List.mem_map] at hp
  rcases hp with ⟨hmem, hcur⟩
  rcases hmem with (rfl | rfl) | ⟨fd, hfd, rfl⟩
  · exact ⟨hcur, by decide, by decide, by decide⟩
  · exact ⟨hcur, by decide, by decide, by decide⟩
  · have hb := sortedOpenFds32_bounds s fd hfd
    exact ⟨hcur, by omega, hb.2, natToAsciiBytes_len_le fd.toNat⟩

private theorem insertSortedInt_mem_iff (x : Int) (xs : List Int) (y : Int) :
    y ∈ insertSortedInt x xs ↔ y = x ∨ y ∈ xs := by
  induction xs with
  | nil => simp [insertSortedInt]
  | cons a tail ih =>
    unfold insertSortedInt
    by_cases heq : (x == a) = true
    · have hxa : x = a := beq_iff_eq.mp heq
      simp only [heq, ↓reduceIte]
      constructor
      · intro hy; exact Or.inr hy
      · rintro (rfl | hy)
        · rw [hxa]; simp
        · exact hy
    · simp only [heq, Bool.false_eq_true, ↓reduceIte]
      by_cases hlt : x < a
      · simp only [hlt, ↓reduceIte, List.mem_cons]
      · simp only [hlt, ↓reduceIte, List.mem_cons, ih]; tauto

private theorem insertSortedInt_strictSorted (x : Int) (xs : List Int)
    (hxs : List.Pairwise (· < ·) xs) :
    List.Pairwise (· < ·) (insertSortedInt x xs) := by
  induction xs with
  | nil => simp [insertSortedInt]
  | cons a tail ih =>
    unfold insertSortedInt
    by_cases heq : (x == a) = true
    · simp [heq, hxs]
    · simp only [heq, Bool.false_eq_true, ↓reduceIte]
      have hne : x ≠ a := fun h => heq (beq_iff_eq.mpr h)
      by_cases hlt : x < a
      · simp only [hlt, ↓reduceIte]
        rcases List.pairwise_cons.mp hxs with ⟨ha, htail⟩
        exact List.pairwise_cons.mpr ⟨fun y hy => by
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact hlt
          · exact Int.lt_trans hlt (ha y hy), hxs⟩
      · simp only [hlt, ↓reduceIte]
        have hax : a < x := by omega
        rcases List.pairwise_cons.mp hxs with ⟨ha, htail⟩
        exact List.pairwise_cons.mpr ⟨fun y hy => by
          rw [insertSortedInt_mem_iff] at hy
          rcases hy with rfl | hy
          · exact hax
          · exact ha y hy, ih htail⟩

private theorem sortedOpenFds32_strictSorted (s : ChildState) :
    List.Pairwise (· < ·) (sortedOpenFds32 s) := by
  unfold sortedOpenFds32
  suffices h : ∀ (l : List (Int × FdEntry)) (acc : List Int),
      List.Pairwise (· < ·) acc →
      List.Pairwise (· < ·)
        (l.foldl (fun a p => if 0 ≤ p.1 && p.1 ≤ 2147483647 then insertSortedInt p.1 a else a) acc) from
    h s.fds [] List.Pairwise.nil
  intro l
  induction l with
  | nil => intro acc hacc; exact hacc
  | cons p ps ih =>
    intro acc hacc
    dsimp only [List.foldl]
    apply ih
    split
    · exact insertSortedInt_strictSorted p.1 acc hacc
    · exact hacc

private theorem sortedOpenFds32_mem_iff (s : ChildState) (fd : Int)
    (h0 : 0 ≤ fd) (hMax : fd ≤ 2147483647) :
    fd ∈ sortedOpenFds32 s ↔ s.isOpen fd = true := by
  unfold sortedOpenFds32
  suffices h : ∀ (l : List (Int × FdEntry)) (acc : List Int),
      fd ∈ l.foldl (fun a p => if 0 ≤ p.1 && p.1 ≤ 2147483647 then insertSortedInt p.1 a else a) acc ↔
        (fd ∈ acc ∨ (l.find? (fun p => p.1 == fd)).isSome = true) by
    rw [ChildState.isOpen, ChildState.getFd]
    cases hF : s.fds.find? (fun p => p.1 == fd) with
    | none => simpa [hF] using h s.fds []
    | some p => simpa [hF] using h s.fds []
  intro l
  induction l with
  | nil => intro acc; simp
  | cons p ps ih =>
    intro acc
    dsimp only [List.foldl, List.find?]
    rw [ih]
    by_cases hp : p.1 == fd
    · have hpEq : p.1 = fd := beq_iff_eq.mp hp
      have hCond : (0 ≤ p.1 && p.1 ≤ 2147483647) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega
      simp only [hCond, ↓reduceIte, insertSortedInt_mem_iff, hp, Option.isSome_some]
      tauto
    · simp only [hp]
      split
      · rw [insertSortedInt_mem_iff]
        have hne : fd ≠ p.1 := fun he => hp (beq_iff_eq.mpr he.symm)
        tauto
      · tauto

private theorem procSelfFdEntriesFrom_strictSorted (s : ChildState) (cursor : Int) :
    List.Pairwise (fun a b : Int × Bytes => a.1 < b.1) (procSelfFdEntriesFrom s cursor) := by
  unfold procSelfFdEntriesFrom
  apply List.Pairwise.filter
  have h1 : List.Pairwise (fun a b : Int × Bytes => a.1 < b.1)
      [((-2 : Int), [46#u8]), ((-1 : Int), [46#u8, 46#u8])] := by decide
  have h2 : List.Pairwise (fun a b : Int × Bytes => a.1 < b.1)
      ((sortedOpenFds32 s).map (fun fd => (fd, natToAsciiBytes fd.toNat))) := by
    rw [List.pairwise_map]
    exact sortedOpenFds32_strictSorted s
  rw [List.pairwise_append]
  refine ⟨h1, h2, ?_⟩
  intro a ha b hb
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
  simp only [List.mem_map] at hb
  rcases hb with ⟨fd, hfd, rfl⟩
  have hBnd := sortedOpenFds32_bounds s fd hfd
  rcases ha with rfl | rfl <;> (dsimp only; omega)

private theorem procSelfFdEntriesFrom_mem_fd_iff (s : ChildState) (cursor fd : Int)
    (h0 : 0 ≤ fd) (hMax : fd ≤ 2147483647) (hCur : cursor ≤ fd) :
    (∃ nm, (fd, nm) ∈ procSelfFdEntriesFrom s cursor) ↔ s.isOpen fd = true := by
  unfold procSelfFdEntriesFrom
  constructor
  · rintro ⟨nm, hmem⟩
    simp only [List.mem_filter, decide_eq_true_eq, List.mem_append, List.mem_cons,
      List.mem_nil_iff, or_false, List.mem_map] at hmem
    rcases hmem with ⟨hleft, _⟩
    rcases hleft with hdot | ⟨fd', hfd', heq⟩
    · rcases hdot with h | h <;> cases h <;> omega
    · cases heq
      exact (sortedOpenFds32_mem_iff s fd h0 hMax).mp hfd'
  · intro hopen
    have hfd := (sortedOpenFds32_mem_iff s fd h0 hMax).mpr hopen
    refine ⟨natToAsciiBytes fd.toNat, ?_⟩
    simp only [List.mem_filter, decide_eq_true_eq, List.mem_append, List.mem_cons,
      List.mem_nil_iff, or_false, List.mem_map]
    exact ⟨Or.inr ⟨fd, hfd, rfl⟩, hCur⟩

private def ValidProcEntry (p : Int × Bytes) : Prop :=
  p = (-2, [46#u8]) ∨ p = (-1, [46#u8, 46#u8]) ∨
    (0 ≤ p.1 ∧ p.1 ≤ 2147483647 ∧ p.2 = natToAsciiBytes p.1.toNat)

private theorem procSelfFdEntriesFrom_valid (s : ChildState) (cursor : Int) :
    ∀ p ∈ procSelfFdEntriesFrom s cursor, ValidProcEntry p := by
  intro p hp
  unfold procSelfFdEntriesFrom at hp
  simp only [List.mem_filter, decide_eq_true_eq, List.mem_append, List.mem_cons,
    List.mem_nil_iff, or_false, List.mem_map] at hp
  rcases hp.1 with (rfl | rfl) | ⟨fd, hfd, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · have hb := sortedOpenFds32_bounds s fd hfd
    exact Or.inr (Or.inr ⟨hb.1, hb.2, rfl⟩)

private theorem foldl_maxOpenFd32_ge_init (xs : List (Int × FdEntry)) (init : Int) :
    init ≤ xs.foldl (fun acc p => if 0 ≤ p.1 && p.1 ≤ 2147483647 then max acc p.1 else acc) init := by
  induction xs generalizing init with
  | nil => exact Int.le_refl _
  | cons p ps ih =>
    simp only [List.foldl_cons]
    split
    · exact Int.le_trans (Int.le_max_left init p.1) (ih _)
    · exact ih init

private theorem foldl_maxOpenFd32_mem (xs : List (Int × FdEntry)) (init : Int)
    {p : Int × FdEntry} (hp : p ∈ xs) (h0 : 0 ≤ p.1) (hMax : p.1 ≤ 2147483647) :
    p.1 ≤ xs.foldl (fun acc q => if 0 ≤ q.1 && q.1 ≤ 2147483647 then max acc q.1 else acc) init := by
  induction xs generalizing init with
  | nil => cases hp
  | cons q qs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hmem
    · have hCond : (0 ≤ p.1 && p.1 ≤ 2147483647) = true := by simp [h0, hMax]
      simp only [hCond, ↓reduceIte]
      exact Int.le_trans (Int.le_max_right init p.1) (foldl_maxOpenFd32_ge_init qs _)
    · split <;> exact ih _ hmem

private theorem maxOpenFd32_ge_zero (s : ChildState) : 0 ≤ s.maxOpenFd32 :=
  foldl_maxOpenFd32_ge_init s.fds 0

private theorem procEofCursor_bounds (s : ChildState) :
    1 ≤ procEofCursor s ∧ procEofCursor s ≤ 2147483648 := by
  have h0 := maxOpenFd32_ge_zero s
  unfold procEofCursor
  omega

private theorem procSelfFdEntriesFrom_lt_procEofCursor (s : ChildState) (cursor : Int) :
    ∀ p ∈ procSelfFdEntriesFrom s cursor, p.1 < procEofCursor s := by
  intro p hp
  have hBnd := procSelfFdEntriesFrom_bounds s cursor p hp
  have hEof := procEofCursor_bounds s
  by_cases hNeg : p.1 < 0
  · omega
  · have h0 : 0 ≤ p.1 := by omega
    have hOpen := (procSelfFdEntriesFrom_mem_fd_iff s cursor p.1 h0 hBnd.2.2.1 hBnd.1).mp ⟨p.2, hp⟩
    simp only [ChildState.isOpen, ChildState.getFd, Option.isSome_iff_exists] at hOpen
    rcases hOpen with ⟨e, he⟩
    cases hFind : s.fds.find? (fun q => q.1 == p.1) with
    | none => simp [hFind] at he
    | some q =>
      have hqMem := List.mem_of_find?_eq_some hFind
      have hqEq : q.1 = p.1 := beq_iff_eq.mp (List.find?_eq_some_iff_append.mp hFind).1
      have hLeMax : p.1 ≤ s.maxOpenFd32 := by
        rw [← hqEq]
        exact foldl_maxOpenFd32_mem s.fds 0 hqMem (hqEq ▸ h0) (hqEq ▸ hBnd.2.2.1)
      unfold procEofCursor
      omega

private def nextCurFor (eofCur : Int) : List (Int × Bytes) → Int
  | (nk, _) :: _ => nk
  | [] => eofCur

private theorem packProcDirents_nonempty_of_ne_nil (cursor eofCur : Int) (xs : List (Int × Bytes)) (cap : Nat)
    (acc : Bytes) (last? : Option Int) (hcap : 0 < cap) (hne : xs ≠ [])
    (hacc : acc.length ≤ 224)
    (hb : ∀ p ∈ xs, p.2.length ≤ 12)
    (hSorted : List.Pairwise (fun a b : Int × Bytes => a.1 < b.1) xs)
    (hCurs : ∀ p ∈ xs, cursor ≤ p.1)
    (hLtEof : ∀ p ∈ xs, p.1 < eofCur) :
    let res := packProcDirents eofCur xs cap acc last?
    0 < res.1.length ∧ res.1.length ≤ 256 ∧ ∃ nc, res.2 = some nc ∧ cursor < nc ∧ nc ≤ eofCur := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons p ps =>
    cases cap with
    | zero => omega
    | succ c =>
      rcases p with ⟨key, nm⟩
      have hnm : nm.length ≤ 12 := hb (key, nm) (by simp)
      have hCurKey : cursor ≤ key := hCurs (key, nm) (by simp)
      have hKeyEof : key < eofCur := hLtEof (key, nm) (by simp)
      rcases List.pairwise_cons.mp hSorted with ⟨hKeyPs, hPsSorted⟩
      let nc0 := nextCurFor eofCur ps
      have hNc0Bounds : key < nc0 ∧ nc0 ≤ eofCur ∧ ∀ q ∈ ps, nc0 ≤ q.1 := by
        cases ps with
        | nil => exact ⟨hKeyEof, Int.le_refl _, fun _ h => nomatch h⟩
        | cons q qs =>
          have hKq : key < q.1 := hKeyPs q (by simp)
          have hqEof : q.1 < eofCur := hLtEof q (by simp)
          refine ⟨hKq, Int.le_of_lt hqEof, fun r hr => ?_⟩
          rcases List.mem_cons.mp hr with rfl | hrm
          · exact Int.le_refl _
          · exact Int.le_of_lt ((List.pairwise_cons.mp hPsSorted).1 r hrm)
      have hrec : (encodeDirent64 (key + 3).toNat (nc0 + 2).toNat (if key < 0 then 4#u8 else 10#u8) nm).length ≤ 32 := by
        unfold encodeDirent64
        dsimp only
        have h8 : (encodeU64Le (key + 3).toNat).length = 8 := by simp [encodeU64Le]
        have h8' : (encodeU64Le (nc0 + 2).toNat).length = 8 := by simp [encodeU64Le]
        simp only [List.length_append, h8, h8', List.length_cons, List.length_nil, List.length_replicate]
        omega
      have hrecPos : 0 < (encodeDirent64 (key + 3).toNat (nc0 + 2).toNat (if key < 0 then 4#u8 else 10#u8) nm).length := by
        unfold encodeDirent64
        dsimp only
        have h8 : (encodeU64Le (key + 3).toNat).length = 8 := by simp [encodeU64Le]
        have h8' : (encodeU64Le (nc0 + 2).toNat).length = 8 := by simp [encodeU64Le]
        simp only [List.length_append, h8, h8', List.length_cons, List.length_nil, List.length_replicate]
        omega
      have hfit : ¬ (acc.length + (encodeDirent64 (key + 3).toNat (nc0 + 2).toNat (if key < 0 then 4#u8 else 10#u8) nm).length > 256) := by
        omega
      have hPackStep :
          packProcDirents eofCur ((key, nm) :: ps) (c + 1) acc last? =
            if acc.length + (encodeDirent64 (key + 3).toNat (nc0 + 2).toNat (if key < 0 then 4#u8 else 10#u8) nm).length > 256
            then (acc, last?)
            else packProcDirents eofCur ps c
              (acc ++ encodeDirent64 (key + 3).toNat (nc0 + 2).toNat (if key < 0 then 4#u8 else 10#u8) nm)
              (some nc0) := by
        cases ps <;> rfl
      rw [hPackStep, ite_eq_right_of_eq_false _ _ (eq_false hfit)]
      clear hne
      suffices hgen : ∀ (ys : List (Int × Bytes)) (cap1 : Nat) (acc1 : Bytes) (lk1 : Int),
          0 < acc1.length → acc1.length ≤ 256 →
          (∀ q ∈ ys, q.2.length ≤ 12) →
          List.Pairwise (fun a b : Int × Bytes => a.1 < b.1) ys →
          (∀ q ∈ ys, lk1 ≤ q.1) →
          (∀ q ∈ ys, q.1 < eofCur) →
          cursor < lk1 → lk1 ≤ eofCur →
          let res := packProcDirents eofCur ys cap1 acc1 (some lk1)
          0 < res.1.length ∧ res.1.length ≤ 256 ∧ ∃ nc, res.2 = some nc ∧ cursor < nc ∧ nc ≤ eofCur by
        apply hgen ps c (acc ++ encodeDirent64 (key + 3).toNat (nc0 + 2).toNat (if key < 0 then 4#u8 else 10#u8) nm) nc0
        · rw [List.length_append]; omega
        · rw [List.length_append]; omega
        · intro q hq; exact hb q (by simp [hq])
        · exact hPsSorted
        · exact hNc0Bounds.2.2
        · intro q hq; exact hLtEof q (by simp [hq])
        · omega
        · exact hNc0Bounds.2.1
      intro ys
      induction ys with
      | nil =>
        intro cap1 acc1 lk1 hpos hle _ _ _ _ hLkCur hLkEof
        cases cap1 <;> exact ⟨hpos, hle, lk1, rfl, hLkCur, hLkEof⟩
      | cons y ys ih =>
        intro cap1 acc1 lk1 hpos hle hyb hyS hyGe hyEof hLkCur hLkEof
        cases cap1 with
        | zero => exact ⟨hpos, hle, lk1, rfl, hLkCur, hLkEof⟩
        | succ c1 =>
          rcases y with ⟨k1, nm1⟩
          rcases List.pairwise_cons.mp hyS with ⟨hK1Ys, hYsSorted⟩
          have hLkK1 : lk1 ≤ k1 := hyGe (k1, nm1) (by simp)
          have hK1Eof : k1 < eofCur := hyEof (k1, nm1) (by simp)
          let nc1 := nextCurFor eofCur ys
          have hNc1Bounds : k1 < nc1 ∧ nc1 ≤ eofCur ∧ ∀ q ∈ ys, nc1 ≤ q.1 := by
            cases ys with
            | nil => exact ⟨hK1Eof, Int.le_refl _, fun _ h => nomatch h⟩
            | cons z zs =>
              have hKz : k1 < z.1 := hK1Ys z (by simp)
              have hzEof : z.1 < eofCur := hyEof z (by simp)
              refine ⟨hKz, Int.le_of_lt hzEof, fun r hr => ?_⟩
              rcases List.mem_cons.mp hr with rfl | hrm
              · exact Int.le_refl _
              · exact Int.le_of_lt ((List.pairwise_cons.mp hYsSorted).1 r hrm)
          have hPackStep1 :
              packProcDirents eofCur ((k1, nm1) :: ys) (c1 + 1) acc1 (some lk1) =
                if acc1.length + (encodeDirent64 (k1 + 3).toNat (nc1 + 2).toNat (if k1 < 0 then 4#u8 else 10#u8) nm1).length > 256
                then (acc1, some lk1)
                else packProcDirents eofCur ys c1
                  (acc1 ++ encodeDirent64 (k1 + 3).toNat (nc1 + 2).toNat (if k1 < 0 then 4#u8 else 10#u8) nm1)
                  (some nc1) := by
            cases ys <;> rfl
          rw [hPackStep1]
          by_cases hOver :
              acc1.length + (encodeDirent64 (k1 + 3).toNat (nc1 + 2).toNat (if k1 < 0 then 4#u8 else 10#u8) nm1).length > 256
          · rw [ite_eq_left_of_eq_true _ _ (eq_true hOver)]
            exact ⟨hpos, hle, lk1, rfl, hLkCur, hLkEof⟩
          · rw [ite_eq_right_of_eq_false _ _ (eq_false hOver)]
            apply ih c1 _ nc1
            · rw [List.length_append]; omega
            · rw [List.length_append]; omega
            · intro q hq; exact hyb q (by simp [hq])
            · exact hYsSorted
            · exact hNc1Bounds.2.2
            · intro q hq; exact hyEof q (by simp [hq])
            · omega
            · exact hNc1Bounds.2.1

private theorem trace_le_of_putDesc (s : ChildState) (d : Desc) (st : DescState) :
    (s.putDesc d st).trace = s.trace := rfl

private def procCloseMeas (dirfd : I32) (cur : sys.Sys) : Nat :=
  (cur.oracle.length - cur.trace.length) +
    match cur.status with
    | .running =>
      match cur.getFd dirfd.val with
      | some e =>
        match cur.getDesc e.desc with
        | .procSelfFd cursor => (2147483648 - cursor).toNat
        | .directory cursor => (2 - cursor).toNat
        | _ => 0
      | none => 0
    | _ => 0

private theorem sys_getdents64_not_running (s : sys.Sys) (h : s.status ≠ .running)
    (dirfd : I32) (buf : Array U8 256#usize) :
    sys.getdents64 s dirfd buf = ok (.Ok 0#usize, s, buf) := by
  unfold sys.getdents64 LeanSwe.PostFork.Aeneas.Internal.Sys.getdents64
  cases hSt : s.status <;> simp_all

private theorem sys_getdents64_seccomp (s : sys.Sys) (hRun : s.status = .running)
    (dirfd : I32) (rawE : I32) (hS : currentFault s = .seccomp rawE)
    (buf : Array U8 256#usize) :
    sys.getdents64 s dirfd buf =
      ok (.Err (sanitizeErrno rawE),
        { s with trace := s.trace ++ [⟨.getdents64 dirfd, .err (sanitizeErrno rawE)⟩] }, buf) := by
  simp [sys.getdents64, LeanSwe.PostFork.Aeneas.Internal.Sys.getdents64, hRun, hS]

private theorem sys_getdents64_none (s : sys.Sys) (hRun : s.status = .running)
    (hNoSec : ∀ rawE, currentFault s ≠ .seccomp rawE)
    (dirfd : I32) (hFd : s.getFd dirfd.val = none) (buf : Array U8 256#usize) :
    sys.getdents64 s dirfd buf =
      ok (.Err EBADF, { s with trace := s.trace ++ [⟨.getdents64 dirfd, .err EBADF⟩] }, buf) := by
  cases hCur : currentFault s with
  | seccomp rawE => exact absurd hCur (hNoSec rawE)
  | normal | fail _ | partialWrite _ | dentsBatch _ => simp [sys.getdents64, LeanSwe.PostFork.Aeneas.Internal.Sys.getdents64, hRun, hCur, hFd]

private theorem sys_getdents64_stream (s : sys.Sys) (hRun : s.status = .running)
    (hNoSec : ∀ rawE, currentFault s ≠ .seccomp rawE)
    (dirfd : I32) (e : FdEntry) (hFd : s.getFd dirfd.val = some e)
    (r w b : Bool) (bs : Bytes) (hDesc : s.getDesc e.desc = .stream r w b bs)
    (buf : Array U8 256#usize) :
    sys.getdents64 s dirfd buf =
      ok (.Err ENOTDIR, { s with trace := s.trace ++ [⟨.getdents64 dirfd, .err ENOTDIR⟩] }, buf) := by
  cases hCur : currentFault s with
  | seccomp rawE => exact absurd hCur (hNoSec rawE)
  | normal | fail _ | partialWrite _ | dentsBatch _ => simp [sys.getdents64, LeanSwe.PostFork.Aeneas.Internal.Sys.getdents64, hRun, hCur, hFd, hDesc]

private theorem sys_getdents64_dir_fail (s : sys.Sys) (hRun : s.status = .running)
    (dirfd : I32) (e : FdEntry) (hFd : s.getFd dirfd.val = some e)
    (cursor : Int) (hDesc : s.getDesc e.desc = .directory cursor) (rawE : I32) (hF : currentFault s = .fail rawE)
    (buf : Array U8 256#usize) :
    sys.getdents64 s dirfd buf =
      ok (.Err (sanitizeErrno rawE),
        { s with trace := s.trace ++ [⟨.getdents64 dirfd, .err (sanitizeErrno rawE)⟩] }, buf) := by
  simp [sys.getdents64, LeanSwe.PostFork.Aeneas.Internal.Sys.getdents64, hRun, hFd, hDesc, hF]

private theorem sys_getdents64_dir_ok (s : sys.Sys) (hRun : s.status = .running)
    (dirfd : I32) (e : FdEntry) (hFd : s.getFd dirfd.val = some e)
    (cursor : Int) (hDesc : s.getDesc e.desc = .directory cursor) (hF : ∀ rawE, currentFault s ≠ .fail rawE)
    (hNoSec : ∀ rawE, currentFault s ≠ .seccomp rawE)
    (buf : Array U8 256#usize) :
    let maxEnt := match currentFault s with | .dentsBatch k => k + 1 | _ => 64
    let cands := ([(0, [46#u8]), (1, [46#u8, 46#u8])]).filter (fun p => decide (cursor ≤ p.1))
    let (payload, nextCur?) := packDirDotEntries cands maxEnt [] none
    let s1 := match nextCur? with | some nc => s.putDesc e.desc (.directory nc) | none => s
    let buf' := overlayBuf256 payload buf
    let n := payload.length
    let s2 := { s1 with trace := s1.trace ++ [⟨.getdents64 dirfd, .okVal (Int.ofNat n)⟩] }
    sys.getdents64 s dirfd buf = ok (.Ok (mkUsize n), s2, buf') := by
  cases hCur : currentFault s with
  | seccomp rawE => exact absurd hCur (hNoSec rawE)
  | fail rawE => exact absurd hCur (hF rawE)
  | normal | partialWrite _ | dentsBatch _ =>
    simp only [sys.getdents64, LeanSwe.PostFork.Aeneas.Internal.Sys.getdents64, hRun, hFd, hDesc, hCur]
    rfl

private theorem sys_getdents64_proc_fail (s : sys.Sys) (hRun : s.status = .running)
    (dirfd : I32) (e : FdEntry) (hFd : s.getFd dirfd.val = some e)
    (cursor : Int) (hDesc : s.getDesc e.desc = .procSelfFd cursor)
    (rawE : I32) (hF : currentFault s = .fail rawE)
    (buf : Array U8 256#usize) :
    sys.getdents64 s dirfd buf =
      ok (.Err (sanitizeErrno rawE),
        { s with trace := s.trace ++ [⟨.getdents64 dirfd, .err (sanitizeErrno rawE)⟩] }, buf) := by
  simp [sys.getdents64, LeanSwe.PostFork.Aeneas.Internal.Sys.getdents64, hRun, hFd, hDesc, hF]

private theorem sys_getdents64_proc_ok (s : sys.Sys) (hRun : s.status = .running)
    (dirfd : I32) (e : FdEntry) (hFd : s.getFd dirfd.val = some e)
    (cursor : Int) (hDesc : s.getDesc e.desc = .procSelfFd cursor)
    (hF : ∀ rawE, currentFault s ≠ .fail rawE)
    (hNoSec : ∀ rawE, currentFault s ≠ .seccomp rawE)
    (buf : Array U8 256#usize) :
    let maxEnt := match currentFault s with | .dentsBatch k => k + 1 | _ => 64
    let (payload, lastKey?) := packProcDirents (procEofCursor s) (procSelfFdEntriesFrom s cursor) maxEnt [] none
    let s1 := match lastKey? with
      | some lastKey => s.putDesc e.desc (.procSelfFd lastKey)
      | none => s
    let buf' := overlayBuf256 payload buf
    let n := payload.length
    let s2 := { s1 with trace := s1.trace ++ [⟨.getdents64 dirfd, .okVal (Int.ofNat n)⟩] }
    sys.getdents64 s dirfd buf = ok (.Ok (mkUsize n), s2, buf') := by
  cases hCur : currentFault s with
  | seccomp rawE => exact absurd hCur (hNoSec rawE)
  | fail rawE => exact absurd hCur (hF rawE)
  | normal | partialWrite _ | dentsBatch _ =>
    simp only [sys.getdents64, LeanSwe.PostFork.Aeneas.Internal.Sys.getdents64, hRun, hFd, hDesc, hCur]
    rfl

private def procLoopCont (extra_keep_fd : I32) (keep_fds : Slice I32) (dirfd : I32)
    (res : core.result.Result Usize I32 × sys.Sys × Array U8 256#usize) :
    Result (ControlFlow sys.Sys (sys.Sys × I32 × Bool)) :=
  let (r, s1, buf1) := res
  match r with
  | core.result.Result.Ok n =>
    match n.val with
    | 0 => ok (done (s1, 0#i32, false))
    | _ =>
      Std.bind (postfork.fd_ops.close_dirent_batch s1 buf1 n dirfd extra_keep_fd keep_fds) fun p =>
        let (r1, s2) := p
        match r1 with
        | core.result.Result.Ok _ => ok (cont s2)
        | core.result.Result.Err e => ok (done (s2, e, true))
  | core.result.Result.Err e =>
    if e != postfork.fd_ops.EINTR
    then ok (done (s1, e, true))
    else ok (cont s1)

private theorem close_proc_body_rw (extra_keep_fd : I32) (keep_fds : Slice I32)
    (dirfd : I32) (s : sys.Sys) :
    postfork.fd_ops.close_via_proc_self_fd_loop.body extra_keep_fd keep_fds dirfd s =
      Std.bind (sys.getdents64 s dirfd (Array.repeat 256#usize 0#u8))
        (procLoopCont extra_keep_fd keep_fds dirfd) := by
  unfold postfork.fd_ops.close_via_proc_self_fd_loop.body procLoopCont
  rfl

private theorem proc_step_bind_ok {r : core.result.Result Usize I32} {s1 : sys.Sys}
    {buf1 : Array U8 256#usize} {extra_keep_fd : I32} {keep_fds : Slice I32} {dirfd : I32} :
    Std.bind (ok (r, s1, buf1)) (procLoopCont extra_keep_fd keep_fds dirfd) =
      procLoopCont extra_keep_fd keep_fds dirfd (r, s1, buf1) :=
  bind_ok (r, s1, buf1) (procLoopCont extra_keep_fd keep_fds dirfd)

private theorem procLoopCont_ok_zero (extra_keep_fd : I32) (keep_fds : Slice I32) (dirfd : I32)
    (n : Usize) (s1 : sys.Sys) (buf1 : Array U8 256#usize) (hn : n.val = 0) :
    procLoopCont extra_keep_fd keep_fds dirfd (core.result.Result.Ok n, s1, buf1) =
      ok (done (s1, 0#i32, false)) := by
  change (match n.val with
    | 0 => ok (done (s1, 0#i32, false))
    | _ => do
      let (r1, s2) ←
        postfork.fd_ops.close_dirent_batch s1 buf1 n dirfd extra_keep_fd keep_fds
      match r1 with
      | core.result.Result.Ok _ => ok (cont s2)
      | core.result.Result.Err e => ok (done (s2, e, true))) = _
  rw [hn]
  rfl

private theorem procLoopCont_ok_succ (extra_keep_fd : I32) (keep_fds : Slice I32) (dirfd : I32)
    (n : Usize) (s1 : sys.Sys) (buf1 : Array U8 256#usize) (m : Nat) (hn : n.val = m + 1) :
    procLoopCont extra_keep_fd keep_fds dirfd (core.result.Result.Ok n, s1, buf1) =
      (do
        let (r1, s2) ←
          postfork.fd_ops.close_dirent_batch s1 buf1 n dirfd extra_keep_fd keep_fds
        match r1 with
        | core.result.Result.Ok _ => ok (cont s2)
        | core.result.Result.Err e => ok (done (s2, e, true))) := by
  change (match n.val with
    | 0 => ok (done (s1, 0#i32, false))
    | _ => do
      let (r1, s2) ←
        postfork.fd_ops.close_dirent_batch s1 buf1 n dirfd extra_keep_fd keep_fds
      match r1 with
      | core.result.Result.Ok _ => ok (cont s2)
      | core.result.Result.Err e => ok (done (s2, e, true))) = _
  rw [hn]
  rfl

private theorem procLoopCont_err_ne (extra_keep_fd : I32) (keep_fds : Slice I32) (dirfd : I32)
    (e : I32) (s1 : sys.Sys) (buf1 : Array U8 256#usize)
    (hne : (e != postfork.fd_ops.EINTR) = true) :
    procLoopCont extra_keep_fd keep_fds dirfd (core.result.Result.Err e, s1, buf1) =
      ok (done (s1, e, true)) := by
  unfold procLoopCont
  exact ite_eq_left_iff.mpr (fun h => absurd hne h)

private theorem procLoopCont_err_eq (extra_keep_fd : I32) (keep_fds : Slice I32) (dirfd : I32)
    (e : I32) (s1 : sys.Sys) (buf1 : Array U8 256#usize)
    (heq : ¬((e != postfork.fd_ops.EINTR) = true)) :
    procLoopCont extra_keep_fd keep_fds dirfd (core.result.Result.Err e, s1, buf1) =
      ok (cont s1) := by
  unfold procLoopCont
  exact ite_eq_right_iff.mpr (fun h => absurd h heq)

private theorem fd_ops_eintr_eq_loc : postfork.fd_ops.EINTR = EINTR := by
  unfold postfork.fd_ops.EINTR EINTR
  rfl

private theorem close_via_proc_self_fd_step (extra_keep_fd : I32) (keep_fds : Slice I32)
    (dirfd : I32) (s : sys.Sys) :
    OkPost
      (postfork.fd_ops.close_via_proc_self_fd_loop.body extra_keep_fd keep_fds dirfd s)
      fun r =>
        match r with
        | done _ => True
        | cont a' => True ∧ procCloseMeas dirfd a' < procCloseMeas dirfd s := by
  rw [close_proc_body_rw]
  by_cases hRun : s.status = .running
  swap
  · rw [sys_getdents64_not_running s hRun, proc_step_bind_ok]
    have hZ : (0#usize : Usize).val = 0 := by decide
    rw [procLoopCont_ok_zero extra_keep_fd keep_fds dirfd 0#usize s (Array.repeat 256#usize 0#u8) hZ]
    exact okPost_ok _ _ trivial
  · by_cases hSec : ∃ rawE, currentFault s = .seccomp rawE
    · rcases hSec with ⟨rawE, hS⟩
      rw [sys_getdents64_seccomp s hRun dirfd rawE hS, proc_step_bind_ok]
      by_cases hEintr : (sanitizeErrno rawE != postfork.fd_ops.EINTR) = true
      · rw [procLoopCont_err_ne extra_keep_fd keep_fds dirfd (sanitizeErrno rawE) _
          (Array.repeat 256#usize 0#u8) hEintr]
        exact okPost_ok _ _ trivial
      · rw [procLoopCont_err_eq extra_keep_fd keep_fds dirfd (sanitizeErrno rawE) _
          (Array.repeat 256#usize 0#u8) hEintr]
        have hLt : s.trace.length < s.oracle.length := by
          unfold currentFault at hS
          cases hGet : s.oracle[s.trace.length]? with
          | none => simp [hGet] at hS
          | some _ => exact (List.getElem?_eq_some_iff.mp hGet).1
        refine okPost_ok _ _ ⟨trivial, ?_⟩
        simp only [procCloseMeas, ChildState.getFd, ChildState.getDesc, hRun]
        cases hFd : s.getFd dirfd.val with
        | none =>
          simp only [ChildState.getFd] at hFd
          simp only [hFd, List.length_append, List.length_cons, List.length_nil]
          omega
        | some e =>
          simp only [ChildState.getFd] at hFd
          cases hDesc : s.getDesc e.desc with
          | directory _ | stream _ _ _ _ =>
            simp only [ChildState.getDesc] at hDesc
            simp only [hFd, hDesc, List.length_append, List.length_cons, List.length_nil]
            omega
          | procSelfFd _ =>
            simp only [ChildState.getDesc] at hDesc
            simp only [hFd, hDesc, List.length_append, List.length_cons, List.length_nil]
            omega
    · have hNoSec : ∀ rawE, currentFault s ≠ .seccomp rawE := fun rawE h => hSec ⟨rawE, h⟩
      cases hFd : s.getFd dirfd.val with
      | none =>
        rw [sys_getdents64_none s hRun hNoSec dirfd hFd, proc_step_bind_ok]
        have hNe : (EBADF != postfork.fd_ops.EINTR) = true := by
          rw [fd_ops_eintr_eq_loc]; unfold EBADF EINTR; decide
        rw [procLoopCont_err_ne extra_keep_fd keep_fds dirfd EBADF _ (Array.repeat 256#usize 0#u8) hNe]
        exact okPost_ok _ _ trivial
      | some e =>
        cases hDesc : s.getDesc e.desc with
        | stream r w b bs =>
          rw [sys_getdents64_stream s hRun hNoSec dirfd e hFd r w b bs hDesc, proc_step_bind_ok]
          have hNe : (ENOTDIR != postfork.fd_ops.EINTR) = true := by
            rw [fd_ops_eintr_eq_loc]; unfold ENOTDIR EINTR; decide
          rw [procLoopCont_err_ne extra_keep_fd keep_fds dirfd ENOTDIR _ (Array.repeat 256#usize 0#u8) hNe]
          exact okPost_ok _ _ trivial
        | directory cursor =>
          cases hFault : currentFault s with
          | seccomp rawE => exact absurd hFault (hNoSec rawE)
          | fail rawE =>
            rw [sys_getdents64_dir_fail s hRun dirfd e hFd cursor hDesc rawE hFault, proc_step_bind_ok]
            by_cases hEintr : (sanitizeErrno rawE != postfork.fd_ops.EINTR) = true
            · rw [procLoopCont_err_ne extra_keep_fd keep_fds dirfd (sanitizeErrno rawE) _
                (Array.repeat 256#usize 0#u8) hEintr]
              exact okPost_ok _ _ trivial
            · rw [procLoopCont_err_eq extra_keep_fd keep_fds dirfd (sanitizeErrno rawE) _
                (Array.repeat 256#usize 0#u8) hEintr]
              have hLt : s.trace.length < s.oracle.length := lt_oracle_of_currentFault_fail hFault
              refine okPost_ok _ _ ⟨trivial, ?_⟩
              simp only [procCloseMeas, ChildState.getFd, ChildState.getDesc] at hFd hDesc ⊢
              simp only [hRun, hFd, hDesc, List.length_append, List.length_cons, List.length_nil]
              omega
          | normal | partialWrite _ | dentsBatch _ =>
            have hNF : ∀ rawE, currentFault s ≠ .fail rawE := by intro rawE h; rw [hFault] at h; cases h
            rw [sys_getdents64_dir_ok s hRun dirfd e hFd cursor hDesc hNF hNoSec, proc_step_bind_ok]
            set cap := match currentFault s with | StepFault.dentsBatch k => k + 1 | _ => 64
            let cands := ([(0, [46#u8]), (1, [46#u8, 46#u8])]).filter (fun p => decide (cursor ≤ p.1))
            by_cases hGt1 : cursor > 1
            · have hCandsNil : cands = [] := by
                simp only [cands, List.filter_cons, List.filter_nil]
                simp [show ¬ (cursor ≤ 0) by omega, show ¬ (cursor ≤ 1) by omega]
              have hPackNil : packDirDotEntries cands cap [] none = ([], none) := by
                rw [hCandsNil]; cases cap <;> rfl
              rw [hPackNil]
              have hZ : (mkUsize ([] : Bytes).length).val = 0 := by decide
              rw [procLoopCont_ok_zero extra_keep_fd keep_fds dirfd (mkUsize ([] : Bytes).length) _
                (overlayBuf256 [] (Array.repeat 256#usize 0#u8)) hZ]
              exact okPost_ok _ _ trivial
            · have hCapPos : 0 < cap := by simp [cap, hFault]
              have hDotCases :
                  let res := packDirDotEntries cands cap [] none
                  0 < res.1.length ∧ res.1.length ≤ 256 ∧ ∃ nc, res.2 = some nc ∧ cursor < nc ∧ nc ≤ 2 := by
                have hLen24_1 : (encodeDirent64 1 1 4#u8 [46#u8]).length = 24 := by decide
                have hLen24_2 : (encodeDirent64 2 2 4#u8 [46#u8, 46#u8]).length = 24 := by decide
                have hLen24_3 : (encodeDirent64 1 2 4#u8 [46#u8]).length = 24 := by decide
                by_cases hLe0 : cursor ≤ 0
                · have hCands2 : cands = [(0, [46#u8]), (1, [46#u8, 46#u8])] := by
                    simp [cands, hLe0, show cursor ≤ 1 by omega]
                  rw [hCands2]
                  rcases Nat.lt_trichotomy cap 2 with hC0 | hC1 | hC2
                  · have hCap1 : cap = 1 := by omega
                    rw [hCap1]
                    simp [packDirDotEntries, hLen24_1]
                    omega
                  · rw [hC1]
                    simp [packDirDotEntries, hLen24_1]
                    omega
                  · obtain ⟨m, hm⟩ : ∃ m, cap = m + 1 + 1 := ⟨cap - 2, by omega⟩
                    rw [hm]
                    simp [packDirDotEntries, hLen24_1, hLen24_2]
                    omega
                · have hCur1 : cursor = 1 := by omega
                  have hCands1 : cands = [(1, [46#u8, 46#u8])] := by
                    simp [cands, hCur1]
                  rw [hCands1]
                  obtain ⟨m, hm⟩ : ∃ m, cap = m + 1 := ⟨cap - 1, by omega⟩
                  rw [hm]
                  simp [packDirDotEntries, hLen24_2]
                  omega
              rcases hDotCases with ⟨hLenPos, hLenLe, nc, hNcEq, hCurLt, hNcLe⟩
              let resD := packDirDotEntries cands cap [] none
              have hLenPos' : 0 < resD.1.length := hLenPos
              have hResEq : packDirDotEntries cands cap [] none = (resD.1, some nc) :=
                Prod.ext rfl hNcEq
              rw [hResEq]
              have h256 : (256#usize : Usize).val = 256 := by decide
              have hNVal : (mkUsize resD.1.length).val = resD.1.length :=
                mkUsize_val_le_scalar 256#usize (by rw [h256]; omega)
              have hNNe : (mkUsize resD.1.length).val ≠ 0 := by rw [hNVal]; exact Nat.ne_of_gt hLenPos'
              cases hNV : (mkUsize resD.1.length).val with
              | zero => exact absurd hNV hNNe
              | succ m =>
                rw [procLoopCont_ok_succ extra_keep_fd keep_fds dirfd (mkUsize resD.1.length) _
                  (overlayBuf256 resD.1 (Array.repeat 256#usize 0#u8)) m hNV]
                set s1 : ChildState :=
                  { s.putDesc e.desc (.directory nc) with
                    trace := (s.putDesc e.desc (.directory nc)).trace ++
                      [⟨Req.getdents64 dirfd, .okVal (Int.ofNat resD.1.length)⟩] }
                refine okPost_bind
                  (close_dirent_batch_total s1
                    (overlayBuf256 resD.1 (Array.repeat 256#usize 0#u8))
                    (mkUsize resD.1.length) dirfd extra_keep_fd keep_fds)
                  fun p2 hp2 => ?_
                rcases p2 with ⟨r1, s2⟩
                rcases hp2 with ⟨hCfg2, _, _, _, hDescs2, _, hTr2, hGetDir2, _⟩
                dsimp only at hCfg2 hDescs2 hTr2 hGetDir2
                cases r1 with
                | Err err => exact okPost_ok _ _ trivial
                | Ok u =>
                  refine okPost_ok _ _ ⟨trivial, ?_⟩
                  have hs2Run : s2.status = .running := hCfg2.status.trans (by simp [s1, ChildState.putDesc, hRun])
                  have hs2Or : s2.oracle = s.oracle := hCfg2.oracle.trans (by simp [s1, ChildState.putDesc])
                  have hs2Tr : s.trace.length ≤ s2.trace.length := by
                    have h1 : s1.trace.length = s.trace.length + 1 := by simp [s1, ChildState.putDesc]
                    omega
                  have hs2Dir : s2.getFd dirfd.val = some e := by
                    rw [hGetDir2]
                    simp [s1, ChildState.putDesc, ChildState.getFd] at hFd ⊢
                    exact hFd
                  have hs2Desc : s2.getDesc e.desc = .directory nc := by
                    simp only [ChildState.getDesc, hDescs2]
                    change (s.putDesc e.desc (.directory nc)).getDesc e.desc = .directory nc
                    exact getDesc_putDesc_self s e.desc (.directory nc)
                  simp only [procCloseMeas, hs2Run, hs2Dir, hs2Desc, hs2Or, hRun, hFd, hDesc]
                  omega
        | procSelfFd cursor =>
          cases hFault : currentFault s with
          | seccomp rawE => exact absurd hFault (hNoSec rawE)
          | fail rawE =>
            rw [sys_getdents64_proc_fail s hRun dirfd e hFd cursor hDesc rawE hFault, proc_step_bind_ok]
            by_cases hEintr : (sanitizeErrno rawE != postfork.fd_ops.EINTR) = true
            · rw [procLoopCont_err_ne extra_keep_fd keep_fds dirfd (sanitizeErrno rawE) _
                (Array.repeat 256#usize 0#u8) hEintr]
              exact okPost_ok _ _ trivial
            · rw [procLoopCont_err_eq extra_keep_fd keep_fds dirfd (sanitizeErrno rawE) _
                (Array.repeat 256#usize 0#u8) hEintr]
              have hLt : s.trace.length < s.oracle.length := lt_oracle_of_currentFault_fail hFault
              refine okPost_ok _ _ ⟨trivial, ?_⟩
              simp only [procCloseMeas, ChildState.getFd, ChildState.getDesc] at hFd hDesc ⊢
              simp only [hRun, hFd, hDesc, List.length_append, List.length_cons, List.length_nil]
              omega
          | normal | partialWrite _ | dentsBatch _ =>
            have hNF : ∀ rawE, currentFault s ≠ .fail rawE := by intro rawE h; rw [hFault] at h; cases h
            rw [sys_getdents64_proc_ok s hRun dirfd e hFd cursor hDesc hNF hNoSec, proc_step_bind_ok]
            set cap := match currentFault s with | StepFault.dentsBatch k => k + 1 | _ => 64
            have hCapDef : cap = match currentFault s with | StepFault.dentsBatch k => k + 1 | _ => 64 := rfl
            have hCapPos : 0 < cap := by
              rw [hCapDef, hFault]
              simp
            cases hCands : procSelfFdEntriesFrom s cursor with
            | nil =>
              have hPackNil : packProcDirents (procEofCursor s) [] cap [] none = ([], none) := by
                cases cap <;> rfl
              rw [hPackNil]
              have h256 : (256#usize : Usize).val = 256 := by decide
              have hZero : (mkUsize ([] : Bytes).length).val = 0 := by
                rw [List.length_nil]
                exact mkUsize_val_le_scalar 256#usize (by rw [h256]; omega)
              rw [procLoopCont_ok_zero extra_keep_fd keep_fds dirfd (mkUsize ([] : Bytes).length) _
                (overlayBuf256 [] (Array.repeat 256#usize 0#u8)) hZero]
              exact okPost_ok _ _ trivial
            | cons hd tl =>
              have hNeNil : procSelfFdEntriesFrom s cursor ≠ [] := by rw [hCands]; simp
              have hPack := packProcDirents_nonempty_of_ne_nil cursor (procEofCursor s)
                (procSelfFdEntriesFrom s cursor) cap [] none
                hCapPos hNeNil (by simp)
                (fun p hp => (procSelfFdEntriesFrom_bounds s cursor p hp).2.2.2)
                (procSelfFdEntriesFrom_strictSorted s cursor)
                (fun p hp => (procSelfFdEntriesFrom_bounds s cursor p hp).1)
                (procSelfFdEntriesFrom_lt_procEofCursor s cursor)
              dsimp only at hPack
              rcases hPack with ⟨hLenPos, hLenLe, nc, hLastEq, hCurLtNc, hNcLeEof⟩
              have hEofBnd := procEofCursor_bounds s
              set resPack := packProcDirents (procEofCursor s) (procSelfFdEntriesFrom s cursor) cap [] none
              have hCapRw :
                  packProcDirents (procEofCursor s) (hd :: tl) cap [] none = (resPack.1, some nc) := by
                calc
                  packProcDirents (procEofCursor s) (hd :: tl) cap [] none
                      = packProcDirents (procEofCursor s) (procSelfFdEntriesFrom s cursor) cap [] none := by rw [← hCands]
                  _   = (resPack.1, some nc) := Prod.ext rfl hLastEq
              rw [hCapRw]
              have h256 : (256#usize : Usize).val = 256 := by decide
              have hNVal : (mkUsize resPack.1.length).val = resPack.1.length :=
                mkUsize_val_le_scalar 256#usize (by rw [h256]; omega)
              have hNNe : (mkUsize resPack.1.length).val ≠ 0 := by rw [hNVal]; omega
              cases hNV : (mkUsize resPack.1.length).val with
              | zero => exact absurd hNV hNNe
              | succ m =>
                rw [procLoopCont_ok_succ extra_keep_fd keep_fds dirfd (mkUsize resPack.1.length) _
                  (overlayBuf256 resPack.1 (Array.repeat 256#usize 0#u8)) m hNV]
                set s1 : ChildState :=
                  { s.putDesc e.desc (.procSelfFd nc) with
                    trace := (s.putDesc e.desc (.procSelfFd nc)).trace ++
                      [⟨Req.getdents64 dirfd, .okVal (Int.ofNat resPack.1.length)⟩] }
                refine okPost_bind
                  (close_dirent_batch_total s1
                    (overlayBuf256 resPack.1 (Array.repeat 256#usize 0#u8))
                    (mkUsize resPack.1.length) dirfd extra_keep_fd keep_fds)
                  fun p2 hp2 => ?_
                rcases p2 with ⟨r1, s2⟩
                rcases hp2 with ⟨hCfg2, _, _, _, hDescs2, _, hTr2, hGetDir2, _⟩
                dsimp only at hCfg2 hDescs2 hTr2 hGetDir2
                cases r1 with
                | Err err => exact okPost_ok _ _ trivial
                | Ok u =>
                  refine okPost_ok _ _ ⟨trivial, ?_⟩
                  have hs2Run : s2.status = .running := hCfg2.status.trans (by simp [s1, ChildState.putDesc, hRun])
                  have hs2Or : s2.oracle = s.oracle := hCfg2.oracle.trans (by simp [s1, ChildState.putDesc])
                  have hs2Tr : s.trace.length ≤ s2.trace.length := by
                    have h1 : s1.trace.length = s.trace.length + 1 := by simp [s1, ChildState.putDesc]
                    omega
                  have hs2Dir : s2.getFd dirfd.val = some e := by
                    rw [hGetDir2]
                    simp [s1, ChildState.putDesc, ChildState.getFd] at hFd ⊢
                    exact hFd
                  have hs2Desc : s2.getDesc e.desc = .procSelfFd nc := by
                    simp only [ChildState.getDesc, hDescs2]
                    change (s.putDesc e.desc (.procSelfFd nc)).getDesc e.desc = .procSelfFd nc
                    exact getDesc_putDesc_self s e.desc (.procSelfFd nc)
                  simp only [procCloseMeas, hs2Run, hs2Dir, hs2Desc, hs2Or, hRun, hFd, hDesc]
                  omega

private theorem close_via_proc_self_fd_loop_total (s0 : sys.Sys) (extra_keep_fd : I32)
    (keep_fds : Slice I32) (dirfd : I32) :
    OkPost (postfork.fd_ops.close_via_proc_self_fd_loop s0 extra_keep_fd keep_fds dirfd)
      fun _ => True := by
  unfold postfork.fd_ops.close_via_proc_self_fd_loop
  refine okPost_loop_decr_nat (procCloseMeas dirfd) (fun _ => True) (fun _ => True)
    (fun s1 => postfork.fd_ops.close_via_proc_self_fd_loop.body extra_keep_fd keep_fds dirfd s1)
    s0 ?_ trivial
  intro s _
  rcases close_via_proc_self_fd_step extra_keep_fd keep_fds dirfd s with ⟨r, hEq, hPost⟩
  refine ⟨r, hEq, ?_⟩
  cases r with
  | done y => trivial
  | cont a' => exact hPost

private theorem sys_open_proc_self_fd_total (s : sys.Sys) :
    OkPost (sys.open_proc_self_fd s) fun _ => True := by
  unfold sys.open_proc_self_fd LeanSwe.PostFork.Aeneas.Internal.Sys.open_proc_self_fd
  by_cases hRun : s.status = .running
  · cases findLowestFreeFd s 0 with
    | none =>
      rcases runI32Syscall_running s hRun .openProcSelfFd (some EMFILE) (fun s => (0#i32, s)) with
        ⟨r, s', hEq, _⟩
      exact ⟨(r, s'), hEq, trivial⟩
    | some dirfd =>
      by_cases hAvail : (!s.procSelfFdAvailable) = true
      · simp only [hAvail, ↓reduceIte]
        rcases runI32Syscall_running s hRun .openProcSelfFd (some (sanitizeErrno s.procOpenErrno))
            (fun s => (0#i32, s)) with
          ⟨r, s', hEq, _⟩
        exact ⟨(r, s'), hEq, trivial⟩
      · simp only [hAvail, Bool.false_eq_true, ↓reduceIte]
        rcases runI32Syscall_running s hRun .openProcSelfFd none _ with ⟨r, s', hEq, _⟩
        exact ⟨(r, s'), hEq, trivial⟩
  · cases findLowestFreeFd s 0 with
    | none =>
      dsimp only
      rw [runI32Syscall_not_running s hRun]
      exact okPost_ok _ _ trivial
    | some dirfd =>
      by_cases hAvail : (!s.procSelfFdAvailable) = true
      · simp only [hAvail, ↓reduceIte, runI32Syscall_not_running s hRun]
        exact okPost_ok _ _ trivial
      · simp only [hAvail, Bool.false_eq_true, ↓reduceIte, runI32Syscall_not_running s hRun]
        exact okPost_ok _ _ trivial

/-- Unconditional totality of `postfork.fd_ops.close_via_proc_self_fd` on any `sys.Sys`. -/
theorem close_via_proc_self_fd_total (s : sys.Sys) (extra_keep_fd : I32) (keep_fds : Slice I32) :
    OkPost (postfork.fd_ops.close_via_proc_self_fd s extra_keep_fd keep_fds) fun _ => True := by
  unfold postfork.fd_ops.close_via_proc_self_fd
  refine okPost_bind (sys_open_proc_self_fd_total s) fun ⟨r, s1⟩ _ => ?_
  cases r with
  | Err e => exact okPost_ok _ _ trivial
  | Ok dirfd =>
    refine okPost_bind (close_via_proc_self_fd_loop_total s1 extra_keep_fd keep_fds dirfd) fun p _ => ?_
    rcases p with ⟨s2, err, failed⟩
    rcases sys_close_total_loc s2 dirfd with ⟨rCl, s3, hCl, _⟩
    change OkPost (do
      let (r1, s3) ← sys.close s2 dirfd
      let (s4, err1, failed1) ←
        match r1 with
        | core.result.Result.Ok _ => ok (s3, err, failed)
        | core.result.Result.Err ce => do
          let (i, b) ← if failed then ok (err, failed) else ok (ce, true)
          ok (s3, i, b)
      if failed1 then ok (core.result.Result.Err err1, s4) else ok (core.result.Result.Ok (), s4)) _
    rw [hCl, bind_ok]
    cases rCl <;> cases failed <;> simp <;> exact okPost_ok _ _ trivial

/-- Unconditional totality of `postfork.fd_ops.close_fds_above2_except` on any `sys.Sys`. -/
theorem close_fds_above2_except_total (s : sys.Sys) (extra_keep_fd : I32) (keep_fds : Slice I32) :
    OkPost (postfork.fd_ops.close_fds_above2_except s extra_keep_fd keep_fds) fun _ => True := by
  unfold postfork.fd_ops.close_fds_above2_except
  refine okPost_bind (try_close_range_except_total s extra_keep_fd keep_fds) fun ⟨r, s1⟩ _ => ?_
  cases r with
  | Ok _ => exact okPost_ok _ _ trivial
  | Err _ => exact close_via_proc_self_fd_total s1 extra_keep_fd keep_fds

private theorem findLowestFreeFd_zero_some_of_lt (s : ChildState)
    (hLim : min s.fdLimit 2147483648 ≥ 1 + Int.ofNat s.fds.length) :
    ∃ dst, findLowestFreeFd s 0 = some dst := by
  refine findLowestFreeFd_some_of_card_lt s 0 (s.fds.map Prod.fst) (le_refl 0) ?_ ?_
  · simp only [List.length_map]; omega
  · intro x _ hx
    simp only [ChildState.isOpen, ChildState.getFd, Option.isSome_iff_exists] at hx
    rcases hx with ⟨e, he⟩
    cases hFind : s.fds.find? (fun p => p.1 == x) with
    | none => simp [hFind] at he
    | some p =>
      have hMem : p ∈ s.fds := List.mem_of_find?_eq_some hFind
      have hPred := (List.find?_eq_some_iff_append.mp hFind).1
      have hxEq : p.1 = x := beq_iff_eq.mp hPred
      exact List.mem_map.mpr ⟨p, hMem, hxEq⟩

private theorem sys_open_proc_self_fd_ok_spec (s : sys.Sys) (hRun : s.status = .running)
    (hCur : currentFault s = .normal) (hAvail : s.procSelfFdAvailable = true)
    (dirfd : Int) (hLow : findLowestFreeFd s 0 = some dirfd) :
    let d := freshDescId s
    let s1 := s.putDesc d (.procSelfFd (-2))
    let s2 := s1.putSlot dirfd { desc := d, cloexec := true, extraFdFlags := 0#i32 }
    let s3 := { s2 with trace := s2.trace ++ [⟨.openProcSelfFd, .okVal (mkI32 dirfd).val⟩] }
    sys.open_proc_self_fd s = ok (.Ok (mkI32 dirfd), s3) := by
  unfold sys.open_proc_self_fd LeanSwe.PostFork.Aeneas.Internal.Sys.open_proc_self_fd
  rw [hLow]
  have hNA : (!s.procSelfFdAvailable) = false := by simp [hAvail]
  unfold runI32Syscall
  simp only [hNA, Bool.false_eq_true, ↓reduceIte, hRun, hCur]

private theorem sys_open_proc_self_fd_err_spec (s : sys.Sys) (hRun : s.status = .running)
    (hNoSec : ∀ rawE, currentFault s ≠ .seccomp rawE)
    (hNotAvail : s.procSelfFdAvailable = false)
    (dirfd : Int) (hLow : findLowestFreeFd s 0 = some dirfd) :
    let e := sanitizeErrno s.procOpenErrno
    let s1 := { s with trace := s.trace ++ [⟨.openProcSelfFd, .err e⟩] }
    sys.open_proc_self_fd s = ok (.Err e, s1) := by
  unfold sys.open_proc_self_fd LeanSwe.PostFork.Aeneas.Internal.Sys.open_proc_self_fd
  rw [hLow]
  have hA : (!s.procSelfFdAvailable) = true := by simp [hNotAvail]
  unfold runI32Syscall
  cases hCur : currentFault s with
  | seccomp rawE => exact absurd hCur (hNoSec rawE)
    | normal | fail _ | partialWrite _ | dentsBatch _ =>
    simp only [hA, ↓reduceIte, hRun]

private def direntEntryBytesWith (nc : Int) (p : Int × Bytes) : Bytes :=
  encodeDirent64 (p.1 + 3).toNat (nc + 2).toNat (if p.1 < 0 then 4#u8 else 10#u8) p.2

private def encodeDirentList : List ((Int × Bytes) × Int) → Bytes
  | [] => []
  | (p, nc) :: ps => direntEntryBytesWith nc p ++ encodeDirentList ps

private theorem encodeDirentList_append (xs ys : List ((Int × Bytes) × Int)) :
    encodeDirentList (xs ++ ys) = encodeDirentList xs ++ encodeDirentList ys := by
  induction xs with
  | nil => simp [encodeDirentList]
  | cons x xs ih => simp [encodeDirentList, ih, List.append_assoc]

private def packTaken (eofCur : Int) : List (Int × Bytes) → Nat → Nat → List ((Int × Bytes) × Int)
  | [], _, _ => []
  | _, 0, _ => []
  | p :: ps, c + 1, used =>
    let nc := nextCurFor eofCur ps
    let rlen := (direntEntryBytesWith nc p).length
    if used + rlen > 256 then []
    else (p, nc) :: packTaken eofCur ps c (used + rlen)

private theorem direntEntryBytesWith_len (nc : Int) (p : Int × Bytes) (hp : ValidProcEntry p) :
    (direntEntryBytesWith nc p).length = (20 + p.2.length + 7) / 8 * 8 ∧
    24 ≤ (direntEntryBytesWith nc p).length ∧ (direntEntryBytesWith nc p).length ≤ 32 := by
  have hLen8 : ∀ n, (encodeU64Le n).length = 8 := fun _ => rfl
  have hLenGen : ∀ (q : Int × Bytes), q.2.length ≤ 12 →
      (direntEntryBytesWith nc q).length = (20 + q.2.length + 7) / 8 * 8 ∧
      24 ≤ (direntEntryBytesWith nc q).length ∧ (direntEntryBytesWith nc q).length ≤ 32 := by
    intro q hq
    unfold direntEntryBytesWith encodeDirent64
    dsimp only
    simp only [List.length_append, hLen8, List.length_cons, List.length_nil, List.length_replicate]
    omega
  rcases hp with rfl | rfl | ⟨_, _, hNm⟩
  · exact hLenGen (-2, [46#u8]) (by decide)
  · exact hLenGen (-1, [46#u8, 46#u8]) (by decide)
  · have hnm : (natToAsciiBytes p.1.toNat).length ≤ 12 := natToAsciiBytes_len_le p.1.toNat
    exact hLenGen p (by rw [hNm]; exact hnm)

private theorem packTaken_prefix (eofCur : Int) (xs : List (Int × Bytes)) (cap used : Nat) :
    ∃ rest, xs = (packTaken eofCur xs cap used).map Prod.fst ++ rest ∧
      ∀ last, (packTaken eofCur xs cap used).getLast? = some last →
        (rest = [] → last.2 = eofCur) ∧
        (∀ nk nm r, rest = (nk, nm) :: r → last.2 = nk) := by
  induction xs generalizing cap used with
  | nil => exact ⟨[], by simp [packTaken]⟩
  | cons p ps ih =>
    cases cap with
    | zero => exact ⟨p :: ps, by simp [packTaken]⟩
    | succ c =>
      unfold packTaken
      dsimp only
      by_cases hOver : used + (direntEntryBytesWith (nextCurFor eofCur ps) p).length > 256
      · simp only [hOver, ↓reduceIte]
        exact ⟨p :: ps, by simp⟩
      · simp only [hOver, ↓reduceIte]
        rcases ih c (used + (direntEntryBytesWith (nextCurFor eofCur ps) p).length) with ⟨rest, hrest, hlast⟩
        refine ⟨rest, by simp [List.map_cons, ← hrest], ?_⟩
        intro last hG
        cases hTail : packTaken eofCur ps c (used + (direntEntryBytesWith (nextCurFor eofCur ps) p).length) with
        | nil =>
          simp only [hTail, List.getLast?_singleton, Option.some.injEq] at hG
          subst hG
          have hRestPs : rest = ps := by
            rw [hTail] at hrest
            simpa using hrest.symm
          rw [hRestPs]
          cases ps with
          | nil => exact ⟨fun _ => rfl, fun _ _ _ h => (by cases h)⟩
          | cons q qs => exact ⟨fun h => (by cases h), fun nk nm r h => (by cases h; rfl)⟩
        | cons q qs =>
          have hG' : (q :: qs).getLast? = some last := by
            rw [hTail] at hG
            simpa [List.getLast?_cons_cons] using hG
          exact hlast last (by rw [hTail]; exact hG')

private theorem packProcDirents_eq_packTaken (eofCur : Int) (xs : List (Int × Bytes)) (cap : Nat)
    (acc : Bytes) (last? : Option Int) :
    let taken := packTaken eofCur xs cap acc.length
    packProcDirents eofCur xs cap acc last? =
      (acc ++ encodeDirentList taken,
        match taken.getLast? with | some p => some p.2 | none => last?) := by
  induction xs generalizing cap acc last? with
  | nil => simp [packProcDirents, packTaken, encodeDirentList]
  | cons p ps ih =>
    cases cap with
    | zero => simp [packProcDirents, packTaken, encodeDirentList]
    | succ c =>
      let nc := nextCurFor eofCur ps
      have hPackEq : packProcDirents eofCur (p :: ps) (c + 1) acc last? =
          (if acc.length + (direntEntryBytesWith nc p).length > 256 then (acc, last?)
           else packProcDirents eofCur ps c (acc ++ direntEntryBytesWith nc p) (some nc)) := by
        cases ps <;> rfl
      have hTakenEq : packTaken eofCur (p :: ps) (c + 1) acc.length =
          (if acc.length + (direntEntryBytesWith nc p).length > 256 then []
           else (p, nc) :: packTaken eofCur ps c (acc.length + (direntEntryBytesWith nc p).length)) := rfl
      rw [hPackEq, hTakenEq]
      by_cases hOver : acc.length + (direntEntryBytesWith nc p).length > 256
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hOver), ite_eq_left_of_eq_true _ _ (eq_true hOver)]
        simp [encodeDirentList]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hOver), ite_eq_right_of_eq_false _ _ (eq_false hOver)]
        have hStep := ih c (acc ++ direntEntryBytesWith nc p) (some nc)
        rw [List.length_append] at hStep
        rw [hStep]
        simp only [List.append_assoc]
        cases packTaken eofCur ps c (acc.length + (direntEntryBytesWith nc p).length) with
        | nil => simp [encodeDirentList]
        | cons q qs => simp [encodeDirentList, List.getLast?_cons]

private theorem foldDigits_eq_eval_loc (acc : Nat) (xs : List U8) :
    List.foldl (fun a (b : U8) => a * 10 + (b.val - 48)) acc xs =
      acc * 10 ^ xs.length + List.foldl (fun a (b : U8) => a * 10 + (b.val - 48)) 0 xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [ih (acc * 10 + (x.val - 48)), ih (x.val - 48)]
    rw [Nat.pow_succ']
    ring

private theorem natDigitsFuel_spec_loc (fuel n : Nat) (acc : Bytes)
    (hf : 0 < fuel) (hBound : n < 10 ^ fuel)
    (hAccDig : ∀ b ∈ acc, 48#u8 ≤ b ∧ b ≤ 57#u8)
    (hAccZero : n = 0 → acc = []) :
    let out := natDigitsFuel fuel n acc
    1 ≤ out.length ∧ out.length ≤ fuel + acc.length ∧
    (∀ b ∈ out, 48#u8 ≤ b ∧ b ≤ 57#u8) ∧
    (out.length > 1 → out.head? ≠ some 48#u8) ∧
    List.foldl (fun a (b : U8) => a * 10 + (b.val - 48)) 0 out =
      n * 10 ^ acc.length + List.foldl (fun a (b : U8) => a * 10 + (b.val - 48)) 0 acc := by
  induction fuel generalizing n acc with
  | zero => omega
  | succ f ih =>
    cases f with
    | zero =>
      have hn : n < 10 := by simpa using hBound
      have hq : (n / 10 == 0) = true := beq_iff_eq.mpr (Nat.div_eq_of_lt hn)
      rw [natDigitsFuel.eq_def]
      dsimp only
      have hdVal : (mkU8 (48 + n % 10)).val = 48 + n % 10 := mkU8_val (n := 48 + n % 10) (by omega)
      have hd48 : 48#u8 ≤ mkU8 (48 + n % 10) := by
        change (48 : Nat) ≤ (mkU8 (48 + n % 10)).val; rw [hdVal]; omega
      have hd57 : mkU8 (48 + n % 10) ≤ 57#u8 := by
        change (mkU8 (48 + n % 10)).val ≤ 57; rw [hdVal]; omega
      simp only [hq, ↓reduceIte]
      refine ⟨by simp, by simp, ?_, ?_, ?_⟩
      · intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hbAcc
        · exact ⟨hd48, hd57⟩
        · exact hAccDig b hbAcc
      · intro hLenGt
        by_cases hn0 : n = 0
        · have := hAccZero hn0
          subst this
          simp at hLenGt
        · simp only [List.head?_cons, ne_eq, Option.some.injEq]
          intro hEq
          have hVal := congrArg UScalar.val hEq
          rw [hdVal] at hVal
          have h48 : (48#u8).val = 48 := rfl
          rw [h48] at hVal
          omega
      · rw [List.foldl_cons, foldDigits_eq_eval_loc]
        have hMod : n % 10 = n := Nat.mod_eq_of_lt hn
        rw [hdVal, hMod]
        simp
    | succ f' =>
      rw [natDigitsFuel.eq_def]
      dsimp only
      have hdVal : (mkU8 (48 + n % 10)).val = 48 + n % 10 := mkU8_val (n := 48 + n % 10) (by omega)
      have hd48 : 48#u8 ≤ mkU8 (48 + n % 10) := by
        change (48 : Nat) ≤ (mkU8 (48 + n % 10)).val; rw [hdVal]; omega
      have hd57 : mkU8 (48 + n % 10) ≤ 57#u8 := by
        change (mkU8 (48 + n % 10)).val ≤ 57; rw [hdVal]; have : n % 10 < 10 := Nat.mod_lt _ (by decide); omega
      by_cases hq : n / 10 == 0
      · have hq0 : n / 10 = 0 := beq_iff_eq.mp hq
        have hn : n < 10 := Nat.lt_of_div_eq_zero (by decide) hq0
        simp only [hq, ↓reduceIte]
        refine ⟨by simp, by simp, ?_, ?_, ?_⟩
        · intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hbAcc
          · exact ⟨hd48, hd57⟩
          · exact hAccDig b hbAcc
        · intro hLenGt
          by_cases hn0 : n = 0
          · have := hAccZero hn0
            subst this
            simp at hLenGt
          · simp only [List.head?_cons, ne_eq, Option.some.injEq]
            intro hEq
            have hVal := congrArg UScalar.val hEq
            rw [hdVal] at hVal
            have h48 : (48#u8).val = 48 := rfl
            rw [h48] at hVal
            omega
        · rw [List.foldl_cons, foldDigits_eq_eval_loc]
          have hMod : n % 10 = n := Nat.mod_eq_of_lt hn
          rw [hdVal, hMod]
          simp
      · have hqNe : n / 10 ≠ 0 := fun h => hq (beq_iff_eq.mpr h)
        have hqPos : 0 < n / 10 := Nat.pos_of_ne_zero hqNe
        have hqBound : n / 10 < 10 ^ (f' + 1) := by rw [Nat.pow_succ'] at hBound; exact Nat.div_lt_of_lt_mul hBound
        have hSub := ih (n / 10) (mkU8 (48 + n % 10) :: acc) (Nat.zero_lt_succ f') hqBound
          (fun b hb => by
            simp only [List.mem_cons] at hb
            rcases hb with rfl | hbAcc
            · exact ⟨hd48, hd57⟩
            · exact hAccDig b hbAcc)
          (fun h => False.elim (by omega))
        simp only [beq_false_of_ne hqNe, Bool.false_eq_true, ↓reduceIte]
        rcases hSub with ⟨hL1, hL2, hDig, hHead, hEval⟩
        refine ⟨hL1, by simp at hL2; omega, hDig, hHead, ?_⟩
        rw [hEval, List.foldl_cons, foldDigits_eq_eval_loc]
        simp only [List.length_cons, hdVal, Nat.zero_mul, Nat.zero_add]
        have hSub48 : 48 + n % 10 - 48 = n % 10 := by omega
        rw [hSub48]
        have hDivMod : (n / 10) * 10 + n % 10 = n := Nat.div_add_mod' n 10
        have hCalc :
            (n / 10) * 10 ^ (acc.length + 1) +
              (n % 10 * 10 ^ acc.length + List.foldl (fun a (b : U8) => a * 10 + (b.val - 48)) 0 acc) =
            ((n / 10) * 10 + n % 10) * 10 ^ acc.length +
              List.foldl (fun a (b : U8) => a * 10 + (b.val - 48)) 0 acc := by
          rw [Nat.pow_succ]; ring
        rw [hCalc, hDivMod]

private theorem list_findIdx?_go_eq_some_loc {α : Type} (p : α → Bool) (xs : List α)
    (idx k : Nat) (hk : k < xs.length)
    (hprev : ∀ j (hj : j < k), p (xs[j]'(Nat.lt_trans hj hk)) = false)
    (hkTrue : p (xs[k]'hk) = true) :
    List.findIdx?.go p xs idx = some (idx + k) := by
  induction xs generalizing idx k with
  | nil => simp at hk
  | cons a tail ih =>
    cases k with
    | zero =>
      have ha : p a = true := by simpa using hkTrue
      simp [List.findIdx?.go, ha]
    | succ k' =>
      have hk0 : 0 < Nat.succ k' := Nat.zero_lt_succ k'
      have haFalse : p a = false := by simpa using hprev 0 hk0
      have ihCall := ih (idx + 1) k' (by simpa using hk)
        (fun j hj => by simpa using hprev (j + 1) (Nat.succ_lt_succ hj))
        (by simpa using hkTrue)
      rw [List.findIdx?.go]
      simp only [haFalse, Bool.false_eq_true, ↓reduceIte]
      rw [ihCall, Nat.add_assoc, Nat.add_comm 1 k']

private theorem list_findIdx?_eq_some_loc {α : Type} (p : α → Bool) (xs : List α)
    (k : Nat) (hk : k < xs.length)
    (hprev : ∀ j (hj : j < k), p (xs[j]'(Nat.lt_trans hj hk)) = false)
    (hkTrue : p (xs[k]'hk) = true) :
    xs.findIdx? p = some k := by
  simpa [List.findIdx?] using list_findIdx?_go_eq_some_loc p xs 0 k hk hprev hkTrue

private theorem overlayBuf256_getElem (payload : Bytes) (hp : payload.length ≤ 256)
    (z : Array U8 256#usize) (idx : Nat) (hi : idx < payload.length) :
    (overlayBuf256 payload z).val[idx]'(by simp [World.overlayBuf256]; omega) = payload[idx] := by
  have hTake : List.take payload.length (overlayBuf256 payload z).val = payload := by
    simp [World.overlayBuf256, List.take_of_length_le hp]
  have h1 : (List.take payload.length (overlayBuf256 payload z).val)[idx]'(by rw [hTake]; exact hi) =
      payload[idx] := by simp [hTake]
  simpa [List.getElem_take] using h1

private theorem overlayBuf256_slice (payload : Bytes) (hp : payload.length ≤ 256)
    (z : Array U8 256#usize) (pref mid suf : Bytes)
    (heq : payload = pref ++ mid ++ suf) :
    List.drop pref.length (List.take (pref.length + mid.length) (overlayBuf256 payload z).val) = mid := by
  have hTakeAll : List.take payload.length (overlayBuf256 payload z).val = payload := by
    simp [World.overlayBuf256, List.take_of_length_le hp]
  have hle : pref.length + mid.length ≤ payload.length := by
    rw [heq]; simp only [List.length_append]; omega
  have hTakeSub : List.take (pref.length + mid.length) (overlayBuf256 payload z).val = pref ++ mid := by
    calc
      List.take (pref.length + mid.length) (overlayBuf256 payload z).val
          = List.take (pref.length + mid.length) (List.take payload.length (overlayBuf256 payload z).val) := by
            rw [List.take_take, Nat.min_eq_left hle]
      _ = List.take (pref.length + mid.length) ((pref ++ mid) ++ suf) := by rw [hTakeAll, heq]
      _ = pref ++ mid := by
            rw [List.take_append_of_le_length (by simp only [List.length_append]; omega),
              List.take_of_length_le (by simp only [List.length_append]; omega)]
  rw [hTakeSub]
  exact List.drop_left' rfl

private theorem direntEntryBytesWith_reclen_bytes (nc : Int) (p : Int × Bytes) (hp : ValidProcEntry p) :
    let recBytes := direntEntryBytesWith nc p
    let rlen := recBytes.length
    rlen ≤ 40 ∧
    recBytes[16]'(by have := (direntEntryBytesWith_len nc p hp).2.1; change 16 < (direntEntryBytesWith nc p).length; omega) =
      mkU8 (rlen % 256) ∧
    recBytes[17]'(by have := (direntEntryBytesWith_len nc p hp).2.1; change 17 < (direntEntryBytesWith nc p).length; omega) =
      mkU8 (rlen / 256) := by
  have hLen := direntEntryBytesWith_len nc p hp
  have h8 : ∀ n, (encodeU64Le n).length = 8 := fun _ => rfl
  have h16 : (encodeU64Le (p.1 + 3).toNat ++ encodeU64Le (nc + 2).toNat).length = 16 := by simp [h8]
  have hGet : ∀ (l1 l2 : Bytes), l1 = l2 → ∀ (i : Nat) (hi1 : i < l1.length) (hi2 : i < l2.length),
      l1[i]'hi1 = l2[i]'hi2 := by
    rintro l1 l2 rfl i hi1 hi2; rfl
  have hSplit : direntEntryBytesWith nc p =
      (encodeU64Le (p.1 + 3).toNat ++ encodeU64Le (nc + 2).toNat) ++
        ([mkU8 ((20 + p.2.length + 7) / 8 * 8 % 256), mkU8 ((20 + p.2.length + 7) / 8 * 8 / 256 % 256),
          if p.1 < 0 then 4#u8 else 10#u8] ++ (p.2 ++
         List.replicate ((20 + p.2.length + 7) / 8 * 8 - 19 - p.2.length) 0#u8)) := by
    unfold direntEntryBytesWith encodeDirent64
    dsimp only
    simp only [List.append_assoc]
  refine ⟨by omega, ?_, ?_⟩
  · calc (direntEntryBytesWith nc p)[16]'(by omega)
        = ((encodeU64Le (p.1 + 3).toNat ++ encodeU64Le (nc + 2).toNat) ++
            ([mkU8 ((20 + p.2.length + 7) / 8 * 8 % 256), mkU8 ((20 + p.2.length + 7) / 8 * 8 / 256 % 256),
              if p.1 < 0 then 4#u8 else 10#u8] ++ (p.2 ++
             List.replicate ((20 + p.2.length + 7) / 8 * 8 - 19 - p.2.length) 0#u8)))[16]'(by rw [← hSplit]; omega) :=
          hGet _ _ hSplit 16 _ _
      _ = mkU8 ((20 + p.2.length + 7) / 8 * 8 % 256) := by
          rw [List.getElem_append_right (by omega)]
          simp [h16]
      _ = mkU8 ((direntEntryBytesWith nc p).length % 256) := by congr 2; exact hLen.1.symm
  · calc (direntEntryBytesWith nc p)[17]'(by omega)
        = ((encodeU64Le (p.1 + 3).toNat ++ encodeU64Le (nc + 2).toNat) ++
            ([mkU8 ((20 + p.2.length + 7) / 8 * 8 % 256), mkU8 ((20 + p.2.length + 7) / 8 * 8 / 256 % 256),
              if p.1 < 0 then 4#u8 else 10#u8] ++ (p.2 ++
             List.replicate ((20 + p.2.length + 7) / 8 * 8 - 19 - p.2.length) 0#u8)))[17]'(by rw [← hSplit]; omega) :=
          hGet _ _ hSplit 17 _ _
      _ = mkU8 ((20 + p.2.length + 7) / 8 * 8 / 256 % 256) := by
          rw [List.getElem_append_right (by omega)]
          simp [h16]
      _ = mkU8 ((direntEntryBytesWith nc p).length / 256) := by
          congr 2
          rw [← hLen.1]
          exact Nat.mod_eq_of_lt (by omega)

private theorem getElem_split_payload (pref mid suf : Bytes) (idx : Nat) (hidx : idx < mid.length) :
    (pref ++ mid ++ suf)[pref.length + idx]'(by simp [List.length_append]; omega) = mid[idx]'hidx := by
  simp only [List.append_assoc]
  simp only [List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem_append_left hidx]

private theorem expectedDirentParse_in_payload (payload pref suf : Bytes) (z : Array U8 256#usize)
    (hpLen : payload.length ≤ 256) (p : Int × Bytes) (nc : Int) (hp : ValidProcEntry p)
    (hSplit : payload = pref ++ direntEntryBytesWith nc p ++ suf)
    (pos start stop : Usize) (hPos : pos.val = pref.length)
    (hStart : start.val = pos.val + 19)
    (hStop : stop.val = pos.val + (direntEntryBytesWith nc p).length) :
    expectedDirentParse (overlayBuf256 payload z) start stop =
      if p.1 < 0 then (-1)#i32 else mkI32 p.1 := by
  have hRecLen := direntEntryBytesWith_len nc p hp
  have hBufStop : stop.val ≤ 256 := by
    have : pref.length + (direntEntryBytesWith nc p).length ≤ payload.length := by
      rw [hSplit]; simp [List.length_append]
    omega
  have hNotBad : (decide (stop.val > 256) || decide (start.val ≥ stop.val)) = false := by
    simp; omega
  unfold expectedDirentParse
  simp only [hNotBad, Bool.false_eq_true, ↓reduceIte]
  have hMid : List.drop start.val (List.take stop.val (overlayBuf256 payload z).val) =
      List.drop 19 (direntEntryBytesWith nc p) := by
    have hSlice := overlayBuf256_slice payload hpLen z pref (direntEntryBytesWith nc p) suf hSplit
    have hSub : List.drop (pref.length + 19) (List.take (pref.length + (direntEntryBytesWith nc p).length) (overlayBuf256 payload z).val) =
        List.drop 19 (List.drop pref.length (List.take (pref.length + (direntEntryBytesWith nc p).length) (overlayBuf256 payload z).val)) := by
      rw [List.drop_drop, Nat.add_comm pref.length 19]
    rw [show start.val = pref.length + 19 by omega, show stop.val = pref.length + (direntEntryBytesWith nc p).length by omega]
    rw [hSub, hSlice]
  rw [hMid]
  have h8 : ∀ n, (encodeU64Le n).length = 8 := fun _ => rfl
  rcases hp with rfl | rfl | ⟨h0, hMax, hNm⟩
  · have hDrop : List.drop 19 (direntEntryBytesWith nc (-2, [46#u8])) = [46#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
      unfold direntEntryBytesWith encodeDirent64
      dsimp only
      rw [List.append_assoc]
      rw [List.drop_left' (by simp [h8])]
      decide
    rw [hDrop]; decide
  · have hDrop : List.drop 19 (direntEntryBytesWith nc (-1, [46#u8, 46#u8])) = [46#u8, 46#u8, 0#u8, 0#u8, 0#u8] := by
      unfold direntEntryBytesWith encodeDirent64
      dsimp only
      rw [List.append_assoc]
      rw [List.drop_left' (by simp [h8])]
      decide
    rw [hDrop]; decide
  · have hNotLt : ¬ (p.1 < 0) := by omega
    simp only [hNotLt, ↓reduceIte]
    set fdNat := p.1.toNat
    set nm := natToAsciiBytes fdNat
    have hNmDef : nm = natDigitsFuel 12 fdNat [] := rfl
    have hBound : fdNat < 10 ^ 12 := by omega
    have hSpec := natDigitsFuel_spec_loc 12 fdNat [] (by decide) hBound
      (fun _ h => nomatch h) (fun _ => rfl)
    dsimp only at hSpec
    rcases hSpec with ⟨hNmGe1, hNmLe12, hNmDig, hNmHead, hNmEval⟩
    simp only [List.length_nil, Nat.add_zero, Nat.pow_zero] at hNmLe12 hNmEval
    have hNmLen12 : nm.length ≤ 12 := by simpa [← hNmDef] using hNmLe12
    have hNmLenGe1 : 1 ≤ nm.length := by simpa [← hNmDef] using hNmGe1
    let reclen := (20 + nm.length + 7) / 8 * 8
    let padLen := reclen - 19 - nm.length
    have hPadGe1 : 1 ≤ padLen := by dsimp only [padLen, reclen]; omega
    have hDrop19 : List.drop 19 (direntEntryBytesWith nc p) = nm ++ List.replicate padLen 0#u8 := by
      unfold direntEntryBytesWith encodeDirent64
      dsimp only
      rw [hNm]
      have h19 : (encodeU64Le (p.1 + 3).toNat ++ encodeU64Le (nc + 2).toNat ++
          [mkU8 (((20 + nm.length + 7) / 8 * 8) % 256), mkU8 (((20 + nm.length + 7) / 8 * 8) / 256),
           if p.1 < 0 then 4#u8 else 10#u8]).length = 19 := by
        simp [h8, nm]
      rw [List.append_assoc]
      exact List.drop_left' h19
    rw [hDrop19]
    have hNoZeroInNm : ∀ b ∈ nm, (b == 0#u8) = false := by
      intro b hb
      have hbD := hNmDig b hb
      cases hEq : (b == 0#u8)
      · rfl
      · exfalso
        have hVal : b.val = 0 := congrArg UScalar.val (beq_iff_eq.mp hEq)
        have h48 : (48#u8).val ≤ b.val := hbD.1
        change 48 ≤ b.val at h48
        omega
    have hFindNm : (nm ++ List.replicate padLen 0#u8).findIdx? (fun b => b == 0#u8) = some nm.length := by
      have hIdx : nm.length < (nm ++ List.replicate padLen 0#u8).length := by simp; omega
      refine list_findIdx?_eq_some_loc _ _ nm.length hIdx ?_ ?_
      · intro j hj
        rw [List.getElem_append_left hj]
        exact hNoZeroInNm _ (List.getElem_mem _)
      · rw [List.getElem_append_right (Nat.le_refl _)]
        simp
    have hNmSucc : nm.length = Nat.succ (nm.length - 1) := by omega
    rw [hFindNm, hNmSucc]
    simp only
    rw [← hNmSucc]
    have hNotGeLen : ¬ (nm.length ≥ (nm ++ List.replicate padLen 0#u8).length) := by simp; omega
    simp only [hNotGeLen, ↓reduceIte]
    have hTakeNm : List.take nm.length (nm ++ List.replicate padLen 0#u8) = nm := by simp
    rw [hTakeNm]
    have hAllTrue : nm.all (fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8)) = true := by
      rw [List.all_eq_true]
      intro b hb
      have hbD := hNmDig b hb
      simp [hbD.1, hbD.2]
    have hNotLead : (decide (nm.length > 1) && nm.head? == some 48#u8) = false := by
      by_cases h1 : nm.length > 1
      · simp only [h1, decide_true, Bool.true_and]
        exact beq_false_of_ne (hNmHead (by rwa [← hNmDef]))
      · simp [h1]
    have hFoldNat : List.foldl (fun acc (b : U8) => acc * 10 + ((↑b : Nat) - 48)) 0 nm = fdNat := by
      simpa [← hNmDef] using hNmEval
    have hNotGtNat : ¬ (fdNat > 2147483647) := by omega
    simp only [hAllTrue, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hNotLead, hFoldNat, hNotGtNat]
    rw [show Int.ofNat fdNat = p.1 from Int.toNat_of_nonneg h0]

private theorem usize_cast_u8_val (b : U8) : (UScalar.cast .Usize b : Usize).val = b.val := by
  have h1 : (UScalar.cast .Usize b : Usize).val = (BitVec.setWidth UScalarTy.Usize.numBits b.bv).toNat := rfl
  rw [h1, BitVec.toNat_setWidth]
  have hb : b.val < 256 := b.bv.isLt
  have hpow : 256 < 2 ^ UScalarTy.Usize.numBits := by
    have := usize_bits_ge32
    exact Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) this)
  exact Nat.mod_eq_of_lt (Nat.lt_trans hb hpow)

private def OracleNoCloseFault (s : ChildState) (fromIdx : Nat) : Prop :=
  ∀ k ≥ fromIdx, match (s.oracle[k]?).getD .normal with
    | .fail _ => False
    | .seccomp _ => False
    | _ => True

private theorem oracleNoCloseFault_mono {s s' : ChildState} {a b : Nat}
    (hOr : s'.oracle = s.oracle) (hLe : a ≤ b) (h : OracleNoCloseFault s a) :
    OracleNoCloseFault s' b := by
  intro k hk
  rw [hOr]
  exact h k (Nat.le_trans hLe hk)

theorem close_dirent_batch_spec (s0 : sys.Sys) (hRun0 : s0.status = .running)
    (taken : List ((Int × Bytes) × Int))
    (hValid : ∀ p ∈ taken, ValidProcEntry p.1)
    (hLen : (encodeDirentList taken).length ≤ 256)
    (dirfd extra_keep_fd : I32) (keep_fds : Slice I32)
    (buf0 : Array U8 256#usize) :
    let payload := encodeDirentList taken
    let buf := overlayBuf256 payload buf0
    let n := mkUsize payload.length
    OkPost (postfork.fd_ops.close_dirent_batch s0 buf n dirfd extra_keep_fd keep_fds) fun res =>
      res.2.status = .running ∧
      SameChildConfig res.2 s0 ∧
      res.2.pgid = s0.pgid ∧ res.2.cwd = s0.cwd ∧ res.2.sig = s0.sig ∧
      res.2.descs = s0.descs ∧ res.2.writeLog = s0.writeLog ∧
      res.2.oracle = s0.oracle ∧
      s0.trace.length ≤ res.2.trace.length ∧
      (∀ fd : Int,
        fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true →
        res.2.getFd fd = s0.getFd fd) ∧
      (res.1 = .Ok () →
        ∀ fd : Int,
          if fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true then
            res.2.getFd fd = s0.getFd fd
          else if ∃ p ∈ taken, p.1.1 = fd then
            res.2.getFd fd = none
          else
            res.2.getFd fd = s0.getFd fd) ∧
      ((OracleNoCloseFault s0 s0.trace.length ∧
        List.Pairwise (fun a b : (Int × Bytes) × Int => a.1.1 < b.1.1) taken ∧
        ∀ p ∈ taken, 2 < p.1.1 → p.1.1 ≠ dirfd.val →
          Model.isKeptAbove2 extra_keep_fd keep_fds.val p.1.1 = false → s0.isOpen p.1.1 = true) →
        res.1 = .Ok ()) := by
  intro payload buf n
  have hPayLen : payload.length ≤ 256 := hLen
  have hMax0 := usize_max_ge_close
  have hPow256 : 256 < 2 ^ UScalarTy.Usize.numBits := by
    have := usize_bits_ge32
    exact Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) this)
  have hnVal : n.val = payload.length := by
    dsimp only [payload, n] at hPayLen ⊢
    exact mkUsize_val_of_lt (by omega)
  have hNotGt : ¬ (n > 256#usize) := by change ¬ (n.val > 256); omega
  unfold postfork.fd_ops.close_dirent_batch
  simp only [hNotGt, ↓reduceIte]
  let inv : sys.Sys × Usize → Prop := fun p =>
    ∃ k, k ≤ taken.length ∧
      p.2.val = (encodeDirentList (taken.take k)).length ∧
      p.1.status = .running ∧
      SameChildConfig p.1 s0 ∧
      p.1.pgid = s0.pgid ∧ p.1.cwd = s0.cwd ∧ p.1.sig = s0.sig ∧
      p.1.descs = s0.descs ∧ p.1.writeLog = s0.writeLog ∧
      p.1.oracle = s0.oracle ∧
      s0.trace.length ≤ p.1.trace.length ∧
      (∀ fd : Int,
        if fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true then
          p.1.getFd fd = s0.getFd fd
        else if ∃ q ∈ taken.take k, q.1.1 = fd then
          p.1.getFd fd = none
        else
          p.1.getFd fd = s0.getFd fd)
  let postLoop : sys.Sys × I32 × Bool → Prop := fun res =>
    res.1.status = .running ∧
    SameChildConfig res.1 s0 ∧
    res.1.pgid = s0.pgid ∧ res.1.cwd = s0.cwd ∧ res.1.sig = s0.sig ∧
    res.1.descs = s0.descs ∧ res.1.writeLog = s0.writeLog ∧
    res.1.oracle = s0.oracle ∧
    s0.trace.length ≤ res.1.trace.length ∧
    (∀ fd : Int,
      fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true →
      res.1.getFd fd = s0.getFd fd) ∧
    (res.2.2 = false →
      ∀ fd : Int,
        if fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true then
          res.1.getFd fd = s0.getFd fd
        else if ∃ q ∈ taken, q.1.1 = fd then
          res.1.getFd fd = none
        else
          res.1.getFd fd = s0.getFd fd) ∧
    ((OracleNoCloseFault s0 s0.trace.length ∧
      List.Pairwise (fun a b : (Int × Bytes) × Int => a.1.1 < b.1.1) taken ∧
      ∀ p ∈ taken, 2 < p.1.1 → p.1.1 ≠ dirfd.val →
        Model.isKeptAbove2 extra_keep_fd keep_fds.val p.1.1 = false → s0.isOpen p.1.1 = true) →
      res.2.2 = false)
  refine okPost_bind (okPost_loop_decr_nat
    (fun p : sys.Sys × Usize => n.val - p.2.val) inv postLoop
    (fun p => postfork.fd_ops.close_dirent_batch_loop.body buf n dirfd extra_keep_fd keep_fds postfork.fd_ops.EIO p.1 p.2)
    (s0, 0#usize) ?_ ⟨0, Nat.zero_le _, by simp [encodeDirentList], hRun0, SameChildConfig.refl s0,
      rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, fun fd => by simp⟩) fun ⟨s1, err, bad⟩ hPost => ?_
  · intro ⟨s, pos⟩ ⟨k, hkLe, hPosEq, hRunS, hCfgS, hPgidS, hCwdS, hSigS, hDescsS, hWlS, hOrS, hTrS, hFdsS⟩
    unfold postfork.fd_ops.close_dirent_batch_loop.body
    by_cases hkEq : k = taken.length
    · subst hkEq
      have hPosEnd : pos.val = n.val := by rw [hPosEq, List.take_length, hnVal]
      have hNotLt : ¬ (pos < n) := by change ¬ (pos.val < n.val); omega
      simp only [hNotLt, ↓reduceIte]
      refine okPost_ok _ _ ⟨hRunS, hCfgS, hPgidS, hCwdS, hSigS, hDescsS, hWlS, hOrS, hTrS,
        fun fd hK => by have h0 := hFdsS fd; rw [ite_eq_left_of_eq_true _ _ (eq_true hK)] at h0; exact h0,
        fun _ fd => by simpa only [List.take_length] using hFdsS fd,
        fun _ => rfl⟩
    · have hkLt : k < taken.length := Nat.lt_of_le_of_ne hkLe hkEq
      have hSplitTaken : taken = taken.take k ++ taken[k] :: taken.drop (k + 1) := by
        have h1 := List.take_append_drop k taken
        rw [← List.cons_getElem_drop_succ (l := taken) (n := k)] at h1
        exact h1.symm
      have hSplitPayload : payload = encodeDirentList (taken.take k) ++
          direntEntryBytesWith taken[k].2 taken[k].1 ++ encodeDirentList (taken.drop (k + 1)) := by
        dsimp only [payload]
        conv_lhs => rw [hSplitTaken]
        rw [encodeDirentList_append, encodeDirentList]
        simp [List.append_assoc]
      have hkMem : taken[k] ∈ taken := List.getElem_mem hkLt
      have hkValid : ValidProcEntry taken[k].1 := hValid taken[k] hkMem
      have hkLen := direntEntryBytesWith_len taken[k].2 taken[k].1 hkValid
      have hRec24 : 24 ≤ (direntEntryBytesWith taken[k].2 taken[k].1).length := hkLen.2.1
      have hRec32 : (direntEntryBytesWith taken[k].2 taken[k].1).length ≤ 32 := hkLen.2.2
      have hkReclen := direntEntryBytesWith_reclen_bytes taken[k].2 taken[k].1 hkValid
      have hPrefPlusRec : pos.val + (direntEntryBytesWith taken[k].2 taken[k].1).length ≤ n.val := by
        rw [hPosEq, hnVal]
        have : payload.length = (encodeDirentList (taken.take k)).length +
            (direntEntryBytesWith taken[k].2 taken[k].1).length + (encodeDirentList (taken.drop (k + 1))).length := by
          rw [hSplitPayload, List.length_append, List.length_append]
        omega
      have hPosLtN : pos.val < n.val := by omega
      have hPosLt : pos < n := hPosLtN
      simp only [hPosLt, ↓reduceIte]
      obtain ⟨i, hiEq, hiVal, _⟩ := (okPost_iff_wp_spec _ _).mpr
        (Usize.sub_spec (x := n) (y := pos) (by omega))
      rw [hiEq, bind_ok]
      have hiEqVal : i.val = n.val - pos.val := hiVal
      have hiGe20 : 20 ≤ i.val := by omega
      have hNotILt20 : ¬ (i < 20#usize) := by change ¬ (i.val < 20); omega
      have hPosLe236 : pos.val ≤ 236 := by omega
      have hNotPosGt : ¬ (pos > 236#usize) := by change ¬ (pos.val > 236); omega
      simp only [hNotILt20, hNotPosGt, ↓reduceIte]
      have hMax := usize_max_ge_close
      have hBufLen : buf.length = 256 := by simp
      obtain ⟨i1, hi1Eq, hi1Val⟩ := (okPost_iff_wp_spec _ _).mpr
        (Usize.add_spec (x := pos) (y := 16#usize) (by change pos.val + 16 ≤ Usize.max; omega))
      rw [hi1Eq, bind_ok]
      have hi1V : i1.val = pos.val + 16 := by have h16 : (16#usize : Usize).val = 16 := rfl; omega
      have hi1Bound : i1.val < buf.length := by omega
      obtain ⟨i2, hi2Eq, hi2Val⟩ := (okPost_iff_wp_spec _ _).mpr (Array.index_usize_spec buf i1 hi1Bound)
      rw [hi2Eq, bind_ok]
      simp only [lift, bind_ok]
      obtain ⟨i3, hi3Eq, hi3Val⟩ := (okPost_iff_wp_spec _ _).mpr
        (Usize.add_spec (x := pos) (y := 17#usize) (by change pos.val + 17 ≤ Usize.max; omega))
      rw [hi3Eq, bind_ok]
      have hi3V : i3.val = pos.val + 17 := by have h17 : (17#usize : Usize).val = 17 := rfl; omega
      have hi3Bound : i3.val < buf.length := by omega
      obtain ⟨i4, hi4Eq, hi4Val⟩ := (okPost_iff_wp_spec _ _).mpr (Array.index_usize_spec buf i3 hi3Bound)
      rw [hi4Eq, bind_ok]
      have hIdx16 : pos.val + 16 < payload.length := by omega
      have hIdx17 : pos.val + 17 < payload.length := by omega
      have hi2EqByte : i2 = (direntEntryBytesWith taken[k].2 taken[k].1)[16]'(by omega) := by
        have hB : i2 = buf.val[i1.val] := hi2Val
        have hCon : buf.val[i1.val] = buf.val[pos.val + 16]'(by simp [hBufLen]; omega) := by
          congr 1
        rw [hB, hCon, overlayBuf256_getElem payload hPayLen buf0 (pos.val + 16) hIdx16]
        have h16eq := getElem_split_payload (encodeDirentList (taken.take k)) (direntEntryBytesWith taken[k].2 taken[k].1)
          (encodeDirentList (taken.drop (k + 1))) 16 (by omega)
        simp only [← hSplitPayload, ← hPosEq] at h16eq
        exact h16eq
      have hi4EqByte : i4 = (direntEntryBytesWith taken[k].2 taken[k].1)[17]'(by omega) := by
        have hB : i4 = buf.val[i3.val] := hi4Val
        have hCon : buf.val[i3.val] = buf.val[pos.val + 17]'(by simp [hBufLen]; omega) := by
          congr 1
        rw [hB, hCon, overlayBuf256_getElem payload hPayLen buf0 (pos.val + 17) hIdx17]
        have h17eq := getElem_split_payload (encodeDirentList (taken.take k)) (direntEntryBytesWith taken[k].2 taken[k].1)
          (encodeDirentList (taken.drop (k + 1))) 17 (by omega)
        simp only [← hSplitPayload, ← hPosEq] at h17eq
        exact h17eq
      have hi2Mod : i2 = mkU8 ((direntEntryBytesWith taken[k].2 taken[k].1).length % 256) := by
        rw [hi2EqByte]; exact hkReclen.2.1
      have hi4Zero : i4 = 0#u8 := by
        rw [hi4EqByte, hkReclen.2.2]
        have hDiv0 : (direntEntryBytesWith taken[k].2 taken[k].1).length / 256 = 0 := Nat.div_eq_of_lt (by omega)
        rw [hDiv0]
        rfl
      have hi4Cast : (UScalar.cast .Usize i4 : Usize) = 0#usize := by
        rw [hi4Zero]
        apply UScalar.eq_of_val_eq
        rw [usize_cast_u8_val 0#u8]
        rfl
      rw [hi4Cast, usize_zero_shl8, bind_ok]
      have hRecEqVal : ((UScalar.cast .Usize i2 : Usize) ||| 0#usize).val = (direntEntryBytesWith taken[k].2 taken[k].1).length := by
        rw [hi2Mod]
        have hModEq : (direntEntryBytesWith taken[k].2 taken[k].1).length % 256 = (direntEntryBytesWith taken[k].2 taken[k].1).length :=
          Nat.mod_eq_of_lt (by omega)
        rw [hModEq]
        have hU8v : (mkU8 (direntEntryBytesWith taken[k].2 taken[k].1).length).val = (direntEntryBytesWith taken[k].2 taken[k].1).length :=
          mkU8_val (by omega)
        have hCastv : (UScalar.cast .Usize (mkU8 (direntEntryBytesWith taken[k].2 taken[k].1).length) : Usize).val =
            (direntEntryBytesWith taken[k].2 taken[k].1).length := by
          rw [usize_cast_u8_val, hU8v]
        have hOrBv : ((UScalar.cast .Usize (mkU8 (direntEntryBytesWith taken[k].2 taken[k].1).length) : Usize) ||| 0#usize).bv =
            (UScalar.cast .Usize (mkU8 (direntEntryBytesWith taken[k].2 taken[k].1).length) : Usize).bv := by
          change _ ||| (0#usize).bv = _
          simp [BitVec.or_zero]
        change ((UScalar.cast .Usize (mkU8 (direntEntryBytesWith taken[k].2 taken[k].1).length) : Usize) ||| 0#usize).bv.toNat = _
        rw [hOrBv]
        exact hCastv
      set reclen : Usize := (UScalar.cast .Usize i2 : Usize) ||| 0#usize
      have hNotRecLt : ¬ (reclen < 20#usize) := by change ¬ (reclen.val < 20); omega
      have hNotRecGt : ¬ (reclen > i) := by change ¬ (reclen.val > i.val); omega
      simp only [hNotRecLt, hNotRecGt, ↓reduceIte]
      obtain ⟨i6, hi6Eq, hi6Val⟩ := (okPost_iff_wp_spec _ _).mpr
        (Usize.add_spec (x := pos) (y := 19#usize) (by change pos.val + 19 ≤ Usize.max; omega))
      obtain ⟨i7, hi7Eq, hi7Val⟩ := (okPost_iff_wp_spec _ _).mpr
        (Usize.add_spec (x := pos) (y := reclen) (by omega))
      rw [hi6Eq, bind_ok, hi7Eq, bind_ok, parse_dirent_name_eq_expected, bind_ok]
      have hExpParsed := expectedDirentParse_in_payload payload (encodeDirentList (taken.take k))
        (encodeDirentList (taken.drop (k + 1))) buf0 hLen taken[k].1 taken[k].2 hkValid hSplitPayload
        pos i6 i7 hPosEq (by have h19 : (19#usize : Usize).val = 19 := rfl; omega)
        (by rw [hi7Val, hRecEqVal])
      have hParsedNeMal : expectedDirentParse buf i6 i7 ≠ postfork.fd_ops.DIRENT_MALFORMED := by
        dsimp only [buf, payload]
        rw [hExpParsed]
        unfold postfork.fd_ops.DIRENT_MALFORMED
        rcases hkValid with h | h | ⟨h0, hM, _⟩
        · rw [h]; decide
        · rw [h]; decide
        · have hNLt : ¬ (taken[k].1.1 < 0) := by omega
          simp only [hNLt, ↓reduceIte]
          intro hEq
          have hv := congrArg BitVec.toInt (congrArg IScalar.bv hEq)
          change (mkI32 taken[k].1.1).val = ((-2)#i32).val at hv
          rw [mkI32_val (by omega) (by omega)] at hv
          have : ((-2)#i32).val = -2 := by decide
          omega
      simp only [hParsedNeMal, ↓reduceIte]
      have hParsedVal : expectedDirentParse buf i6 i7 =
          if taken[k].1.1 < 0 then (-1)#i32 else mkI32 taken[k].1.1 := hExpParsed
      have hPvInt : (expectedDirentParse buf i6 i7).val =
          if taken[k].1.1 < 0 then -1 else taken[k].1.1 := by
        rw [hParsedVal]
        split
        · decide
        · next hNLt =>
          rcases hkValid with h | h | ⟨h0, hM, _⟩
          · rw [h] at hNLt; omega
          · rw [h] at hNLt; omega
          · exact mkI32_val (by omega) (by omega)
      have hStepCont : ∀ (s1 : sys.Sys),
          s1.status = .running → SameChildConfig s1 s →
          s1.pgid = s.pgid → s1.cwd = s.cwd → s1.sig = s.sig →
          s1.descs = s.descs → s1.writeLog = s.writeLog →
          s1.oracle = s.oracle → s.trace.length ≤ s1.trace.length →
          (∀ fd : Int,
            if fd = taken[k].1.1 ∧ 2 < fd ∧ fd ≠ dirfd.val ∧
                Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = false then
              s1.getFd fd = none
            else
              s1.getFd fd = s.getFd fd) →
          inv (s1, i7) ∧ n.val - i7.val < n.val - pos.val := by
        intro s1 hRun1 hCfg1 hPgid1 hCwd1 hSig1 hDescs1 hWl1 hOr1 hTr1 hFds1
        have hTakeSucc : taken.take (k + 1) = taken.take k ++ [taken[k]] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hkLt]; rfl
        refine ⟨⟨k + 1, hkLt, ?_, hRun1, hCfg1.trans hCfgS, hPgid1.trans hPgidS,
            hCwd1.trans hCwdS, hSig1.trans hSigS, hDescs1.trans hDescsS, hWl1.trans hWlS,
            hOr1.trans hOrS, Nat.le_trans hTrS hTr1, fun fd => ?_⟩, by omega⟩
        · rw [hi7Val, hPosEq, hRecEqVal, hTakeSucc, encodeDirentList_append, encodeDirentList, encodeDirentList]
          simp [List.length_append]
        · have hMemTake : ∀ q, q ∈ taken.take (k + 1) ↔ q ∈ taken.take k ∨ q = taken[k] := by
            intro q; rw [hTakeSucc, List.mem_append, List.mem_singleton]
          by_cases hKeepOrLow : fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true
          · rw [ite_eq_left_of_eq_true _ _ (eq_true hKeepOrLow)]
            have hNotCond : ¬ (fd = taken[k].1.1 ∧ 2 < fd ∧ fd ≠ dirfd.val ∧
                Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = false) := by
              rcases hKeepOrLow with h | h | h
              · rintro ⟨_, h2, _⟩; omega
              · rintro ⟨_, _, hnd, _⟩; exact hnd h
              · rintro ⟨_, _, _, hnk⟩; exact Bool.false_ne_true (hnk.symm.trans h)
            have h1 := hFds1 fd
            rw [ite_eq_right_of_eq_false _ _ (eq_false hNotCond)] at h1
            have h0 := hFdsS fd
            rw [ite_eq_left_of_eq_true _ _ (eq_true hKeepOrLow)] at h0
            exact h1.trans h0
          · rw [ite_eq_right_of_eq_false _ _ (eq_false hKeepOrLow)]
            have hGt2Fd : 2 < fd := by
              by_contra hle
              exact hKeepOrLow (Or.inl (by omega))
            have hNeDirFd : fd ≠ dirfd.val := by intro h; exact hKeepOrLow (Or.inr (Or.inl h))
            have hNotKeepFd : Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = false := by
              cases hm : Model.isKeptAbove2 extra_keep_fd keep_fds.val fd
              · rfl
              · exfalso; exact hKeepOrLow (Or.inr (Or.inr hm))
            by_cases hNew : fd = taken[k].1.1
            · have hEx : ∃ q ∈ taken.take (k + 1), q.1.1 = fd :=
                ⟨taken[k], (hMemTake _).mpr (Or.inr rfl), hNew.symm⟩
              have h1 := hFds1 fd
              have hCond : fd = taken[k].1.1 ∧ 2 < fd ∧ fd ≠ dirfd.val ∧
                  Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = false :=
                ⟨hNew, hGt2Fd, hNeDirFd, hNotKeepFd⟩
              rw [ite_eq_left_of_eq_true _ _ (eq_true hCond)] at h1
              rw [ite_eq_left_of_eq_true _ _ (eq_true hEx)]
              exact h1
            · have h1 := hFds1 fd
              have hNotCond : ¬ (fd = taken[k].1.1 ∧ 2 < fd ∧ fd ≠ dirfd.val ∧
                  Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = false) := by
                rintro ⟨h, _⟩; exact hNew h
              rw [ite_eq_right_of_eq_false _ _ (eq_false hNotCond)] at h1
              rw [h1]
              have hExIff : (∃ q ∈ taken.take (k + 1), q.1.1 = fd) ↔ (∃ q ∈ taken.take k, q.1.1 = fd) := by
                constructor
                · rintro ⟨q, hq, hqEq⟩
                  rcases (hMemTake q).mp hq with hq | rfl
                  · exact ⟨q, hq, hqEq⟩
                  · exact absurd hqEq.symm hNew
                · rintro ⟨q, hq, hqEq⟩; exact ⟨q, (hMemTake q).mpr (Or.inl hq), hqEq⟩
              have h0 := hFdsS fd
              rw [ite_eq_right_of_eq_false _ _ (eq_false hKeepOrLow)] at h0
              by_cases hOld : ∃ q ∈ taken.take k, q.1.1 = fd
              · rw [ite_eq_left_of_eq_true _ _ (eq_true (hExIff.mpr hOld))]
                rw [ite_eq_left_of_eq_true _ _ (eq_true hOld)] at h0
                exact h0
              · have hNotEx : ¬ (∃ q ∈ taken.take (k + 1), q.1.1 = fd) := fun hx => hOld (hExIff.mp hx)
                rw [ite_eq_right_of_eq_false _ _ (eq_false hNotEx)]
                rw [ite_eq_right_of_eq_false _ _ (eq_false hOld)] at h0
                exact h0
      by_cases hGt2 : taken[k].1.1 > 2
      · have hGt2B : expectedDirentParse buf i6 i7 > 2#i32 := by
          change (2#i32).val < (expectedDirentParse buf i6 i7).val
          rw [hPvInt]
          have : ¬ (taken[k].1.1 < 0) := by omega
          simp only [this, ↓reduceIte]
          exact hGt2
        simp only [hGt2B, ↓reduceIte]
        by_cases hDir : taken[k].1.1 = dirfd.val
        · have hDirB : (expectedDirentParse buf i6 i7 != dirfd) = false := by
            rw [bne_eq_false_iff_eq]
            apply IScalar.eq_of_val_eq
            rw [hPvInt]
            have hN : ¬ (taken[k].1.1 < 0) := by omega
            simp only [hN, ↓reduceIte]
            exact hDir
          simp only [hDirB, Bool.false_eq_true, ↓reduceIte]
          refine okPost_ok _ _ (hStepCont s hRunS (SameChildConfig.refl s) rfl rfl rfl rfl rfl rfl (Nat.le_refl _)
            fun fd => by
              by_cases hCond : fd = taken[k].1.1 ∧ 2 < fd ∧ fd ≠ dirfd.val ∧
                  Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = false
              · exact False.elim (hCond.2.2.1 (hCond.1 ▸ hDir))
              · simp only [hCond, ↓reduceIte])
        · have hNeDirB : (expectedDirentParse buf i6 i7 != dirfd) = true := by
            simp only [bne_iff_ne, ne_eq]
            intro hEq
            have hv := congrArg IScalar.val hEq
            rw [hPvInt] at hv
            have : ¬ (taken[k].1.1 < 0) := by omega
            simp only [this, ↓reduceIte] at hv
            exact hDir hv
          simp only [hNeDirB, ↓reduceIte]
          by_cases hExtra : taken[k].1.1 = extra_keep_fd.val
          · have hExtraB : (expectedDirentParse buf i6 i7 != extra_keep_fd) = false := by
              rw [bne_eq_false_iff_eq]
              apply IScalar.eq_of_val_eq
              rw [hPvInt]
              have hN : ¬ (taken[k].1.1 < 0) := by omega
              simp only [hN, ↓reduceIte]
              exact hExtra
            simp only [hExtraB, Bool.false_eq_true, ↓reduceIte]
            refine okPost_ok _ _ (hStepCont s hRunS (SameChildConfig.refl s) rfl rfl rfl rfl rfl rfl (Nat.le_refl _)
              fun fd => by
                have hExtraGt2 : extra_keep_fd.val > 2 := by omega
                have hKeptTrue : Model.isKeptAbove2 extra_keep_fd keep_fds.val taken[k].1.1 = true := by
                  simp [Model.isKeptAbove2, hExtra, hExtraGt2]
                by_cases hCond : fd = taken[k].1.1 ∧ 2 < fd ∧ fd ≠ dirfd.val ∧
                    Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = false
                · rcases hCond with ⟨rfl, _, _, hc⟩
                  exact False.elim (Bool.false_ne_true (hc.symm.trans hKeptTrue))
                · simp only [hCond, ↓reduceIte])
          · have hNeExtraB : (expectedDirentParse buf i6 i7 != extra_keep_fd) = true := by
              simp only [bne_iff_ne, ne_eq]
              intro hEq
              have hv := congrArg IScalar.val hEq
              rw [hPvInt] at hv
              have : ¬ (taken[k].1.1 < 0) := by omega
              simp only [this, ↓reduceIte] at hv
              exact hExtra hv
            simp only [hNeExtraB, ↓reduceIte]
            refine okPost_bind (slice_contains_nonneg_spec keep_fds (expectedDirentParse buf i6 i7))
              fun b hb => ?_
            have hbEq : b = sliceContainsNonnegSpec keep_fds.val taken[k].1.1 := by
              rw [hb, hPvInt]
              have : ¬ (taken[k].1.1 < 0) := by omega
              simp [this]
            rw [hbEq]
            by_cases hKeep : sliceContainsNonnegSpec keep_fds.val taken[k].1.1 = true
            · simp only [hKeep, ↓reduceIte]
              refine okPost_ok _ _ (hStepCont s hRunS (SameChildConfig.refl s) rfl rfl rfl rfl rfl rfl (Nat.le_refl _)
                fun fd => by
                  have hKeptTrue : Model.isKeptAbove2 extra_keep_fd keep_fds.val taken[k].1.1 = true := by
                    simp [Model.isKeptAbove2, hGt2, hKeep]
                  have hNotC : ¬ (fd = taken[k].1.1 ∧ 2 < fd ∧ fd ≠ dirfd.val ∧
                      Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = false) := by
                    rintro ⟨rfl, _, _, hc⟩; rw [hKeptTrue] at hc; cases hc
                  simp only [hNotC, ↓reduceIte])
            · simp only [hKeep, Bool.false_eq_true, ↓reduceIte]
              have hKeepFalse : sliceContainsNonnegSpec keep_fds.val taken[k].1.1 = false := by
                cases hm : sliceContainsNonnegSpec keep_fds.val taken[k].1.1 with
                | false => rfl
                | true => exact absurd hm hKeep
              have hNotKept : Model.isKeptAbove2 extra_keep_fd keep_fds.val taken[k].1.1 = false := by
                have hNeE : (extra_keep_fd.val == taken[k].1.1) = false := by
                  cases hc : (extra_keep_fd.val == taken[k].1.1) with
                  | false => rfl
                  | true => exact absurd (beq_iff_eq.mp hc).symm hExtra
                simp [Model.isKeptAbove2, hKeepFalse, hNeE]
              have hPvTk : (expectedDirentParse buf i6 i7).val = taken[k].1.1 := by
                rw [hPvInt]
                have : ¬ (taken[k].1.1 < 0) := by omega
                simp [this]
              rcases sys_close_running_exact s hRunS (expectedDirentParse buf i6 i7) with
                ⟨rCl, sCl, hClEq, hClCfg, hClPgid, hClCwd, hClSig, hClDescs, hClWl, hClTr, hClFds, hClOkIf, hClIfOk⟩
              rw [hClEq, bind_ok]
              cases rCl with
              | Ok u =>
                have hNoSecFail : ∀ rawE, currentFault s ≠ .seccomp rawE ∧ currentFault s ≠ .fail rawE :=
                  hClOkIf rfl
                have hGetClAll : ∀ fd, sCl.getFd fd = (s.closeSlot taken[k].1.1).getFd fd := by
                  intro fd
                  cases hf : currentFault s with
                  | seccomp rawE => exact absurd hf (hNoSecFail rawE).1
                  | fail rawE => exact absurd hf (hNoSecFail rawE).2
                  | normal | partialWrite _ | dentsBatch _ =>
                    simp only [hf, hPvTk] at hClFds
                    simp only [ChildState.getFd, hClFds]
                exact okPost_ok _ _ (hStepCont sCl (hClCfg.status.trans hRunS) hClCfg
                  hClPgid hClCwd hClSig hClDescs hClWl hClCfg.oracle (by rw [hClTr]; omega)
                  fun fd => by
                    by_cases hfdEq : fd = taken[k].1.1
                    · subst hfdEq
                      have hCondT : taken[k].1.1 = taken[k].1.1 ∧ 2 < taken[k].1.1 ∧ taken[k].1.1 ≠ dirfd.val ∧
                          Model.isKeptAbove2 extra_keep_fd keep_fds.val taken[k].1.1 = false :=
                        ⟨rfl, hGt2, hDir, hNotKept⟩
                      rw [ite_eq_left_of_eq_true _ _ (eq_true hCondT), hGetClAll taken[k].1.1]
                      exact getFd_closeSlot_self s taken[k].1.1
                    · simp only [hfdEq, false_and, ↓reduceIte, hGetClAll fd]
                      exact getFd_closeSlot_ne s hfdEq)
              | Err errCl =>
                refine okPost_ok _ _ ⟨hClCfg.status.trans hRunS, hClCfg.trans hCfgS,
                  hClPgid.trans hPgidS, hClCwd.trans hCwdS, hClSig.trans hSigS,
                  hClDescs.trans hDescsS, hClWl.trans hWlS, hClCfg.oracle.trans hOrS,
                  Nat.le_trans hTrS (by dsimp only; rw [hClTr]; omega), ?_, (fun h => by cases h), ?_⟩
                · intro fd hK
                  have hNeFd : fd ≠ taken[k].1.1 := by
                    intro hEq
                    subst hEq
                    rcases hK with h2 | hD | hKt
                    · omega
                    · exact hDir hD
                    · rw [hNotKept] at hKt; cases hKt
                  have hNotIn : ∀ rawE, currentFault s = .seccomp rawE → sCl.getFd fd = s.getFd fd := by
                    intro rawE hf
                    simp only [hf] at hClFds
                    simp [ChildState.getFd, hClFds]
                  have hGetCl : sCl.getFd fd = s.getFd fd := by
                    cases hf : currentFault s with
                    | seccomp rawE => exact hNotIn rawE hf
                    | normal | fail _ | partialWrite _ | dentsBatch _ =>
                      simp only [hf, hPvTk] at hClFds
                      rw [show sCl.getFd fd = (s.closeSlot taken[k].1.1).getFd fd from by simp [ChildState.getFd, hClFds]]
                      exact getFd_closeSlot_ne s hNeFd
                  have h0 := hFdsS fd
                  rw [ite_eq_left_of_eq_true _ _ (eq_true hK)] at h0
                  exact hGetCl.trans h0
                · rintro ⟨hNoCl, hSorted, hOpenTaken⟩
                  exfalso
                  have hNotTaken : ¬ (∃ q ∈ taken.take k, q.1.1 = taken[k].1.1) := by
                    rintro ⟨q, hq, hqEq⟩
                    obtain ⟨j, hj, hjEq⟩ := List.mem_iff_getElem.mp hq
                    have hjLen : j < (taken.take k).length := hj
                    have hjK : j < k := by rw [List.length_take] at hjLen; omega
                    rw [List.getElem_take] at hjEq
                    have hjLt := List.pairwise_iff_getElem.mp hSorted j k (Nat.lt_trans hjK hkLt) hkLt hjK
                    rw [hjEq] at hjLt
                    omega
                  have h0 := hFdsS taken[k].1.1
                  have hNotK : ¬ (taken[k].1.1 ≤ 2 ∨ taken[k].1.1 = dirfd.val ∨
                      Model.isKeptAbove2 extra_keep_fd keep_fds.val taken[k].1.1 = true) := by
                    simp [show ¬ taken[k].1.1 ≤ 2 by omega, hDir, hNotKept]
                  rw [ite_eq_right_of_eq_false _ _ (eq_false hNotK),
                    ite_eq_right_of_eq_false _ _ (eq_false hNotTaken)] at h0
                  have hIsOpen0 := hOpenTaken taken[k] hkMem hGt2 hDir hNotKept
                  have hIsOpenS : s.isOpen taken[k].1.1 = true := by
                    simpa [ChildState.isOpen, h0] using hIsOpen0
                  have hAt : match (s.oracle[s.trace.length]?).getD .normal with
                      | .fail _ => False | .seccomp _ => False | _ => True := by
                    rw [hOrS]
                    exact hNoCl s.trace.length hTrS
                  have hNoSecFail : ∀ rawE, currentFault s ≠ .seccomp rawE ∧ currentFault s ≠ .fail rawE := by
                    intro rawE
                    constructor
                    · intro hF; unfold currentFault at hF; rw [hF] at hAt; exact hAt
                    · intro hF; unfold currentFault at hF; rw [hF] at hAt; exact hAt
                  have hWasOk := hClIfOk hNoSecFail (by rw [hPvTk]; exact hIsOpenS)
                  cases hWasOk
      · have hNotGt2B : ¬ (expectedDirentParse buf i6 i7 > 2#i32) := by
          change ¬ ((2#i32).val < (expectedDirentParse buf i6 i7).val)
          have h2v : (2#i32 : I32).val = 2 := rfl
          rw [hPvInt, h2v]
          by_cases hNeg : taken[k].1.1 < 0
          · simp only [hNeg, ↓reduceIte]; omega
          · simp only [hNeg, ↓reduceIte]; omega
        simp only [hNotGt2B, ↓reduceIte]
        refine okPost_ok _ _ (hStepCont s hRunS (SameChildConfig.refl s) rfl rfl rfl rfl rfl rfl (Nat.le_refl _)
          fun fd => by
            have : ¬ (fd = taken[k].1.1 ∧ 2 < fd ∧ fd ≠ dirfd.val ∧
                Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = false) := by
              rintro ⟨rfl, h⟩; omega
            simp [this])
  · rcases hPost with ⟨hRun1, hCfg1, hPgid1, hCwd1, hSig1, hDescs1, hWl1, hOr1, hTr1, hKept1, hOkFds, hNoFail⟩
    dsimp only at hRun1 hCfg1 hPgid1 hCwd1 hSig1 hDescs1 hWl1 hOr1 hTr1
    change OkPost (if bad then ok (core.result.Result.Err err, s1) else ok (core.result.Result.Ok (), s1)) _
    cases bad
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact okPost_ok _ _ ⟨hRun1, hCfg1, hPgid1, hCwd1, hSig1, hDescs1, hWl1, hOr1, hTr1,
        hKept1, (fun _ => hOkFds rfl), (fun _ => rfl)⟩
    · simp only [↓reduceIte]
      exact okPost_ok _ _ ⟨hRun1, hCfg1, hPgid1, hCwd1, hSig1, hDescs1, hWl1, hOr1, hTr1,
        hKept1, (fun h => by cases h), fun hg => absurd (hNoFail hg) (by simp)⟩

private theorem foldl_max_ge_init {α : Type} (f : α → Nat) (xs : List α) (acc : Nat) :
    acc ≤ xs.foldl (fun a x => Nat.max a (f x)) acc := by
  induction xs generalizing acc with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    dsimp only [List.foldl]
    exact Nat.le_trans (Nat.le_max_left acc (f x)) (ih (Nat.max acc (f x)))

private theorem foldl_max_mem_le {α : Type} (f : α → Nat) (xs : List α) (acc : Nat)
    {x : α} (hx : x ∈ xs) :
    f x ≤ xs.foldl (fun a y => Nat.max a (f y)) acc := by
  induction xs generalizing acc with
  | nil => cases hx
  | cons y ys ih =>
    dsimp only [List.foldl]
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hys
    · exact Nat.le_trans (Nat.le_max_right acc (f x)) (foldl_max_ge_init f ys _)
    · exact ih (Nat.max acc (f y)) hys

private theorem desc_lt_freshDescId_of_getFd (s : ChildState) {fd : Int} {e : FdEntry}
    (h : s.getFd fd = some e) :
    e.desc < freshDescId s := by
  unfold ChildState.getFd at h
  cases hFind : s.fds.find? (fun p => p.1 == fd) with
  | none => simp [hFind] at h
  | some p =>
    simp only [hFind] at h
    injection h with he
    subst he
    have hMem : p ∈ s.fds := List.mem_of_find?_eq_some hFind
    have hLe1 : p.2.desc ≤ s.fds.foldl (fun acc q => Nat.max acc q.2.desc) 0 :=
      foldl_max_mem_le (fun q : Int × FdEntry => q.2.desc) s.fds 0 hMem
    have hLe2 : s.fds.foldl (fun acc q => Nat.max acc q.2.desc) 0 ≤
        s.descs.foldl (fun acc q => Nat.max acc q.1)
          (s.fds.foldl (fun acc q => Nat.max acc q.2.desc) 0) :=
      foldl_max_ge_init (fun q : Desc × DescState => q.1) s.descs _
    have hLe := Nat.le_trans hLe1 hLe2
    unfold freshDescId
    exact Nat.lt_succ_of_le hLe

private theorem mem_of_getLast?_eq_some_loc {α : Type} :
    ∀ {xs : List α} {x : α}, xs.getLast? = some x → x ∈ xs
  | [], _, h => by cases h
  | [a], _, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    exact List.mem_singleton_self _
  | a :: b :: bs, x, h => by
    have hTail : (b :: bs).getLast? = some x := by simpa [List.getLast?_cons_cons] using h
    exact List.mem_cons_of_mem a (mem_of_getLast?_eq_some_loc hTail)

private theorem taken_getLast_le_all (taken : List (Int × Bytes))
    (hSorted : List.Pairwise (fun a b : Int × Bytes => a.1 < b.1) taken)
    (pLk : Int × Bytes) (hLast : taken.getLast? = some pLk) :
    ∀ p ∈ taken, p.1 ≤ pLk.1 := by
  induction taken with
  | nil => simp at hLast
  | cons a tail ih =>
    rcases List.pairwise_cons.mp hSorted with ⟨ha, htail⟩
    cases tail with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hLast
      subst hLast
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      subst hp
      exact Int.le_refl _
    | cons b bs =>
      have hLastTail : (b :: bs).getLast? = some pLk := by
        simpa [List.getLast?_cons_cons] using hLast
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hmem
      · have hLkMem : pLk ∈ b :: bs := mem_of_getLast?_eq_some_loc hLastTail
        exact Int.le_of_lt (ha pLk hLkMem)
      · exact ih htail hLastTail p (by simpa using hmem)

private theorem rest_gt_taken_getLast (taken rest : List (Int × Bytes))
    (hSorted : List.Pairwise (fun a b : Int × Bytes => a.1 < b.1) (taken ++ rest))
    (pLk : Int × Bytes) (hLast : taken.getLast? = some pLk) :
    ∀ r ∈ rest, pLk.1 < r.1 := by
  have hApp := (List.pairwise_append).mp hSorted
  have hLkMem : pLk ∈ taken := mem_of_getLast?_eq_some_loc hLast
  intro r hr
  exact hApp.2.2 pLk hLkMem r hr

private theorem close_dirent_batch_spec_wrapper (s0 : sys.Sys) (hRun0 : s0.status = .running)
    (taken : List ((Int × Bytes) × Int))
    (hValid : ∀ p ∈ taken, ValidProcEntry p.1)
    (hLen : (encodeDirentList taken).length ≤ 256)
    (dirfd extra_keep_fd : I32) (keep_fds : Slice I32)
    (buf0 : Array U8 256#usize) :
    OkPost
      (postfork.fd_ops.close_dirent_batch s0
        (overlayBuf256 (encodeDirentList taken) buf0)
        (mkUsize (encodeDirentList taken).length) dirfd extra_keep_fd keep_fds)
      fun res =>
        res.2.status = .running ∧
        SameChildConfig res.2 s0 ∧
        res.2.pgid = s0.pgid ∧ res.2.cwd = s0.cwd ∧ res.2.sig = s0.sig ∧
        res.2.descs = s0.descs ∧ res.2.writeLog = s0.writeLog ∧
        res.2.oracle = s0.oracle ∧
        s0.trace.length ≤ res.2.trace.length ∧
        (∀ fd : Int,
          fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true →
          res.2.getFd fd = s0.getFd fd) ∧
        (res.1 = .Ok () →
          ∀ fd : Int,
            if fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true then
              res.2.getFd fd = s0.getFd fd
            else if ∃ p ∈ taken, p.1.1 = fd then
              res.2.getFd fd = none
            else
              res.2.getFd fd = s0.getFd fd) ∧
        ((OracleNoCloseFault s0 s0.trace.length ∧
          List.Pairwise (fun a b : (Int × Bytes) × Int => a.1.1 < b.1.1) taken ∧
          ∀ p ∈ taken, 2 < p.1.1 → p.1.1 ≠ dirfd.val →
            Model.isKeptAbove2 extra_keep_fd keep_fds.val p.1.1 = false → s0.isOpen p.1.1 = true) →
          res.1 = .Ok ()) :=
  close_dirent_batch_spec s0 hRun0 taken hValid hLen dirfd extra_keep_fd keep_fds buf0

private theorem close_via_proc_self_fd_loop_nonfail_step (s0 : sys.Sys) (extra_keep_fd : I32)
    (keep_fds : Slice I32) (dirfd : I32) (eDir : FdEntry)
    (_hRun0 : s0.status = .running)
    (s : sys.Sys) (cursor : Int)
    (hCfg : SameChildConfig s s0)
    (hRun : s.status = .running)
    (hPgid : s.pgid = s0.pgid)
    (hCwd : s.cwd = s0.cwd)
    (hSig : s.sig = s0.sig)
    (hWl : s.writeLog = s0.writeLog)
    (hOr : s.oracle = s0.oracle)
    (hTr : s0.trace.length ≤ s.trace.length)
    (hDir : s.getFd dirfd.val = some eDir)
    (hDesc : s.getDesc eDir.desc = .procSelfFd cursor)
    (hDescsNe : ∀ d, d ≠ eDir.desc → s.getDesc d = s0.getDesc d)
    (hFds : ∀ fd : Int, 0 ≤ fd → fd ≤ 2147483647 →
      if fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true then
        s.getFd fd = s0.getFd fd
      else if fd < cursor then
        s.getFd fd = none
      else
        s.getFd fd = s0.getFd fd)
    (hNF : ∀ rawE, currentFault s ≠ .fail rawE)
    (hNoSec : ∀ rawE, currentFault s ≠ .seccomp rawE) :
    OkPost
      (postfork.fd_ops.close_via_proc_self_fd_loop.body extra_keep_fd keep_fds dirfd s)
      fun r =>
        match r with
        | done res =>
          res.1.status = .running ∧
          (OracleNoCloseFault s0 s0.trace.length → res.2.2 = false) ∧
          (res.2.2 = false →
            SameChildConfig res.1 s0 ∧
            res.1.pgid = s0.pgid ∧
            res.1.cwd = s0.cwd ∧
            res.1.sig = s0.sig ∧
            res.1.writeLog = s0.writeLog ∧
            res.1.oracle = s0.oracle ∧
            s0.trace.length ≤ res.1.trace.length ∧
            (∀ d, d ≠ eDir.desc → res.1.getDesc d = s0.getDesc d) ∧
            (∀ fd : Int, 0 ≤ fd → fd ≤ 2147483647 →
              if fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true then
                res.1.getFd fd = s0.getFd fd
              else
                res.1.getFd fd = none))
        | cont a' =>
          (∃ c',
            SameChildConfig a' s0 ∧
            a'.status = .running ∧
            a'.pgid = s0.pgid ∧
            a'.cwd = s0.cwd ∧
            a'.sig = s0.sig ∧
            a'.writeLog = s0.writeLog ∧
            a'.oracle = s0.oracle ∧
            s0.trace.length ≤ a'.trace.length ∧
            a'.getFd dirfd.val = some eDir ∧
            a'.getDesc eDir.desc = .procSelfFd c' ∧
            (∀ d, d ≠ eDir.desc → a'.getDesc d = s0.getDesc d) ∧
            (∀ fd : Int, 0 ≤ fd → fd ≤ 2147483647 →
              if fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true then
                a'.getFd fd = s0.getFd fd
              else if fd < c' then
                a'.getFd fd = none
              else
                a'.getFd fd = s0.getFd fd)) ∧
          procCloseMeas dirfd a' < procCloseMeas dirfd s := by
  rw [close_proc_body_rw]
  have hCapPos : 0 < (match currentFault s with | StepFault.dentsBatch k => k + 1 | _ => 64) := by
    cases currentFault s <;> simp
  set cap := match currentFault s with | StepFault.dentsBatch k => k + 1 | _ => 64
  rw [sys_getdents64_proc_ok s hRun dirfd eDir hDir cursor hDesc hNF hNoSec, proc_step_bind_ok]
  cases hCands : procSelfFdEntriesFrom s cursor with
    | nil =>
      have hPackNil : packProcDirents (procEofCursor s) [] cap [] none = ([], none) := by
        cases cap <;> rfl
      rw [hPackNil]
      have h256 : (256#usize : Usize).val = 256 := by decide
      have hZero : (mkUsize ([] : Bytes).length).val = 0 := by
        rw [List.length_nil]
        exact mkUsize_val_le_scalar 256#usize (by rw [h256]; omega)
      rw [procLoopCont_ok_zero extra_keep_fd keep_fds dirfd (mkUsize ([] : Bytes).length) _
        (overlayBuf256 [] (Array.repeat 256#usize 0#u8)) hZero]
      have hSameNil : SameChildConfig
          { s with trace := s.trace ++ [⟨Req.getdents64 dirfd, .okVal (Int.ofNat ([] : Bytes).length)⟩] } s :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      refine okPost_ok _ _ ⟨hRun, fun _ => rfl, fun _ => ⟨hSameNil.trans hCfg, by exact hPgid, by exact hCwd,
        by exact hSig, by exact hWl, by exact hOr, by simp; omega, by exact hDescsNe,
        fun fd h0 hMax => ?_⟩⟩
      change (if fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true then
        s.getFd fd = s0.getFd fd else s.getFd fd = none)
      have hFd := hFds fd h0 hMax
      split
      · next hKept =>
        rw [ite_eq_left_of_eq_true _ _ (eq_true hKept)] at hFd
        exact hFd
      · next hNotKept =>
        rw [ite_eq_right_of_eq_false _ _ (eq_false hNotKept)] at hFd
        by_cases hCur : fd < cursor
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hCur)] at hFd
          exact hFd
        · have hGeCur : cursor ≤ fd := by omega
          by_contra hNotNone
          cases hGet : s.getFd fd with
          | none => exact hNotNone hGet
          | some eFd =>
            have hOpen : s.isOpen fd = true := by simp [ChildState.isOpen, hGet]
            have hEx := (procSelfFdEntriesFrom_mem_fd_iff s cursor fd h0 hMax hGeCur).mpr hOpen
            rw [hCands] at hEx
            rcases hEx with ⟨nm, hMem⟩
            cases hMem
    | cons hd tl =>
      have hNeNil : procSelfFdEntriesFrom s cursor ≠ [] := by rw [hCands]; simp
      have hPack := packProcDirents_nonempty_of_ne_nil cursor (procEofCursor s)
        (procSelfFdEntriesFrom s cursor) cap [] none
        hCapPos hNeNil (by simp)
        (fun p hp => (procSelfFdEntriesFrom_bounds s cursor p hp).2.2.2)
        (procSelfFdEntriesFrom_strictSorted s cursor)
        (fun p hp => (procSelfFdEntriesFrom_bounds s cursor p hp).1)
        (procSelfFdEntriesFrom_lt_procEofCursor s cursor)
      dsimp only at hPack
      rcases hPack with ⟨hLenPos, hLenLe, nc, hLastEq, hCurLtNc, hNcLeEof⟩
      have hEofBnd := procEofCursor_bounds s
      set resPack := packProcDirents (procEofCursor s) (procSelfFdEntriesFrom s cursor) cap [] none
      have hCapRw : packProcDirents (procEofCursor s) (hd :: tl) cap [] none = (resPack.1, some nc) := by
        calc
          packProcDirents (procEofCursor s) (hd :: tl) cap [] none
              = packProcDirents (procEofCursor s) (procSelfFdEntriesFrom s cursor) cap [] none := by rw [← hCands]
          _   = (resPack.1, some nc) := Prod.ext rfl hLastEq
      rw [hCapRw]
      have h256 : (256#usize : Usize).val = 256 := by decide
      have hNVal : (mkUsize resPack.1.length).val = resPack.1.length :=
        mkUsize_val_le_scalar 256#usize (by rw [h256]; omega)
      have hNNe : (mkUsize resPack.1.length).val ≠ 0 := by rw [hNVal]; omega
      cases hNV : (mkUsize resPack.1.length).val with
      | zero => exact absurd hNV hNNe
      | succ m =>
        rw [procLoopCont_ok_succ extra_keep_fd keep_fds dirfd (mkUsize resPack.1.length) _
          (overlayBuf256 resPack.1 (Array.repeat 256#usize 0#u8)) m hNV]
        let taken := packTaken (procEofCursor s) (procSelfFdEntriesFrom s cursor) cap 0
        have hPackEq := packProcDirents_eq_packTaken (procEofCursor s) (procSelfFdEntriesFrom s cursor) cap [] none
        have hPayEq : resPack.1 = encodeDirentList taken := by
          have hFst := congrArg Prod.fst hPackEq
          simpa [resPack, taken] using hFst
        have hLastTaken : (match taken.getLast? with | some p => some p.2 | none => none) = some nc := by
          have hSnd := congrArg Prod.snd hPackEq
          change resPack.2 = _ at hSnd
          rw [hLastEq] at hSnd
          exact hSnd.symm
        obtain ⟨qLk, hqLkLast, hqLkSnd⟩ : ∃ qLk, taken.getLast? = some qLk ∧ qLk.2 = nc := by
          cases hG : taken.getLast? with
          | none => simp [hG] at hLastTaken
          | some q =>
            simp only [hG, Option.some.injEq] at hLastTaken
            exact ⟨q, rfl, hLastTaken⟩
        obtain ⟨rest, hPrefix, hLastPref⟩ := packTaken_prefix (procEofCursor s) (procSelfFdEntriesFrom s cursor) cap 0
        change procSelfFdEntriesFrom s cursor = taken.map Prod.fst ++ rest at hPrefix
        have hValidTaken : ∀ p ∈ taken, ValidProcEntry p.1 := by
          intro p hp
          apply procSelfFdEntriesFrom_valid s cursor
          rw [hPrefix]
          exact List.mem_append_left rest (List.mem_map_of_mem hp)
        have hLenTaken : (encodeDirentList taken).length ≤ 256 := by
          rw [← hPayEq]
          exact hLenLe
        have hSortedAll : List.Pairwise (fun a b : Int × Bytes => a.1 < b.1) (taken.map Prod.fst ++ rest) := by
          rw [← hPrefix]
          exact procSelfFdEntriesFrom_strictSorted s cursor
        have hSortedTaken : List.Pairwise (fun a b : (Int × Bytes) × Int => a.1.1 < b.1.1) taken := by
          have hMap := (List.pairwise_append.mp hSortedAll).1
          simpa using List.pairwise_map.mp hMap
        have hTakenLtNc : ∀ p ∈ taken, p.1.1 < nc := by
          intro p hp
          have hLastSpec := hLastPref qLk hqLkLast
          rw [← hqLkSnd]
          cases rest with
          | nil =>
            rw [hLastSpec.1 rfl]
            apply procSelfFdEntriesFrom_lt_procEofCursor s cursor
            rw [hPrefix]
            exact List.mem_append_left [] (List.mem_map_of_mem hp)
          | cons nkRest rRest =>
            rw [hLastSpec.2 nkRest.1 nkRest.2 rRest rfl]
            exact (List.pairwise_append.mp hSortedAll).2.2 p.1 (List.mem_map_of_mem hp) nkRest (by simp)
        have hRestGeNc : ∀ r ∈ rest, nc ≤ r.1 := by
          intro r hr
          have hLastSpec := hLastPref qLk hqLkLast
          rw [← hqLkSnd]
          cases rest with
          | nil => cases hr
          | cons nkRest rRest =>
            rw [hLastSpec.2 nkRest.1 nkRest.2 rRest rfl]
            rcases List.mem_cons.mp hr with rfl | hrm
            · exact Int.le_refl _
            · exact Int.le_of_lt ((List.pairwise_cons.mp (List.pairwise_append.mp hSortedAll).2.1).1 r hrm)
        set s1 : ChildState :=
          { s.putDesc eDir.desc (.procSelfFd nc) with
            trace := (s.putDesc eDir.desc (.procSelfFd nc)).trace ++
              [⟨Req.getdents64 dirfd, .okVal (Int.ofNat resPack.1.length)⟩] }
        have hBufEq : overlayBuf256 resPack.1 (Array.repeat 256#usize 0#u8) =
            overlayBuf256 (encodeDirentList taken) (Array.repeat 256#usize 0#u8) := by
          rw [hPayEq]
        have hNEq : mkUsize resPack.1.length = mkUsize (encodeDirentList taken).length := by
          rw [hPayEq]
        rw [hBufEq, hNEq]
        have hs1Run : s1.status = .running := by simp [s1, ChildState.putDesc, hRun]
        refine okPost_bind
          (close_dirent_batch_spec_wrapper s1 hs1Run taken hValidTaken hLenTaken dirfd extra_keep_fd
            keep_fds (Array.repeat 256#usize 0#u8))
          fun p2 hp2 => ?_
        rcases p2 with ⟨r1, s2⟩
        rcases hp2 with ⟨hs2Run, hCfg2, hPgid2, hCwd2, hSig2, hDescs2, hWl2, hOr2, hTr2, _, hOk2, hNoErr2⟩
        dsimp only at hs2Run hCfg2 hPgid2 hCwd2 hSig2 hDescs2 hWl2 hOr2 hTr2
        have hs1Cfg : SameChildConfig s1 s :=
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        have hs1Or : s1.oracle = s0.oracle := by simp [s1, ChildState.putDesc, hOr]
        have hs1Tr : s0.trace.length ≤ s1.trace.length := by
          have h1 : s1.trace.length = s.trace.length + 1 := by simp [s1, ChildState.putDesc]
          omega
        cases r1 with
        | Err errCl =>
          refine okPost_ok _ _ ⟨hs2Run, fun hNoCl0 => ?_, fun h => by cases h⟩
          have hNoCl1 : OracleNoCloseFault s1 s1.trace.length :=
            oracleNoCloseFault_mono hs1Or hs1Tr hNoCl0
          have hOpen1 : ∀ p ∈ taken, 2 < p.1.1 → p.1.1 ≠ dirfd.val →
              Model.isKeptAbove2 extra_keep_fd keep_fds.val p.1.1 = false → s1.isOpen p.1.1 = true := by
            intro p hp h2 _ _
            have hInEnt : p.1 ∈ procSelfFdEntriesFrom s cursor := by
              rw [hPrefix]; exact List.mem_append_left rest (List.mem_map_of_mem hp)
            have hBnd := procSelfFdEntriesFrom_bounds s cursor p.1 hInEnt
            have hOpenS := (procSelfFdEntriesFrom_mem_fd_iff s cursor p.1.1 (by omega) hBnd.2.2.1 hBnd.1).mp
              ⟨p.1.2, hInEnt⟩
            simpa [s1, ChildState.putDesc, ChildState.isOpen, ChildState.getFd] using hOpenS
          have hrOk := hNoErr2 ⟨hNoCl1, hSortedTaken, hOpen1⟩
          cases hrOk
        | Ok u =>
          have hFds2 := hOk2 rfl
          have hs2Cfg : SameChildConfig s2 s0 := hCfg2.trans (hs1Cfg.trans hCfg)
          have hs2Or : s2.oracle = s0.oracle := hOr2.trans hs1Or
          have hs2Tr : s.trace.length + 1 ≤ s2.trace.length := by
            have h1 : s1.trace.length = s.trace.length + 1 := by simp [s1, ChildState.putDesc]
            omega
          have hs1GetFd : ∀ x, s1.getFd x = s.getFd x := fun _ => rfl
          have hs2Dir : s2.getFd dirfd.val = some eDir := by
            have hd2 := hFds2 dirfd.val
            rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inr (Or.inl rfl)))] at hd2
            rw [hd2, hs1GetFd, hDir]
          have hs2Desc : s2.getDesc eDir.desc = .procSelfFd nc := by
            simp only [ChildState.getDesc, hDescs2]
            change (s.putDesc eDir.desc (.procSelfFd nc)).getDesc eDir.desc = .procSelfFd nc
            exact getDesc_putDesc_self s eDir.desc (.procSelfFd nc)
          refine okPost_ok _ _ ⟨⟨nc, hs2Cfg, hs2Run,
            hPgid2.trans (by simp [s1, ChildState.putDesc, hPgid]),
            hCwd2.trans (by simp [s1, ChildState.putDesc, hCwd]),
            hSig2.trans (by simp [s1, ChildState.putDesc, hSig]),
            hWl2.trans (by simp [s1, ChildState.putDesc, hWl]),
            hs2Or, by omega, hs2Dir, hs2Desc, ?_, ?_⟩, ?_⟩
          · intro d hdNe
            have hd2 : s2.getDesc d = s1.getDesc d := by simp [ChildState.getDesc, hDescs2]
            have hd1 : s1.getDesc d = (s.putDesc eDir.desc (.procSelfFd nc)).getDesc d := rfl
            rw [hd2, hd1, getDesc_putDesc_ne s hdNe, hDescsNe d hdNe]
          · intro fd h0 hMax
            have hd2 := hFds2 fd
            have hdPrev := hFds fd h0 hMax
            by_cases hKept : fd ≤ 2 ∨ fd = dirfd.val ∨
                Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true
            · rw [ite_eq_left_of_eq_true _ _ (eq_true hKept)] at hd2 hdPrev ⊢
              rw [hd2, hs1GetFd, hdPrev]
            · rw [ite_eq_right_of_eq_false _ _ (eq_false hKept)] at hd2 hdPrev ⊢
              by_cases hLtNext : fd < nc
              · rw [ite_eq_left_of_eq_true _ _ (eq_true hLtNext)]
                by_cases hTakenEx : ∃ p ∈ taken, p.1.1 = fd
                · rw [ite_eq_left_of_eq_true _ _ (eq_true hTakenEx)] at hd2
                  exact hd2
                · rw [ite_eq_right_of_eq_false _ _ (eq_false hTakenEx)] at hd2
                  rw [hd2, hs1GetFd]
                  by_cases hLtCur : fd < cursor
                  · rw [ite_eq_left_of_eq_true _ _ (eq_true hLtCur)] at hdPrev
                    exact hdPrev
                  · have hGeCur : cursor ≤ fd := by omega
                    cases hGet : s.getFd fd with
                    | none => rfl
                    | some eFd =>
                      have hOpen : s.isOpen fd = true := by simp [ChildState.isOpen, hGet]
                      obtain ⟨nm, hMem⟩ :=
                        (procSelfFdEntriesFrom_mem_fd_iff s cursor fd h0 hMax hGeCur).mpr hOpen
                      rw [hPrefix, List.mem_append] at hMem
                      rcases hMem with hInTaken | hInRest
                      · rcases List.mem_map.mp hInTaken with ⟨q, hq, hqEq⟩
                        exact absurd ⟨q, hq, congrArg Prod.fst hqEq⟩ hTakenEx
                      · have hGe := hRestGeNc (fd, nm) hInRest
                        dsimp only at hGe
                        omega
              · rw [ite_eq_right_of_eq_false _ _ (eq_false hLtNext)]
                have hNotTaken : ¬ (∃ p ∈ taken, p.1.1 = fd) := by
                  rintro ⟨p, hp, rfl⟩
                  have := hTakenLtNc p hp
                  omega
                rw [ite_eq_right_of_eq_false _ _ (eq_false hNotTaken)] at hd2
                have hNotLtCur : ¬ (fd < cursor) := by omega
                rw [ite_eq_right_of_eq_false _ _ (eq_false hNotLtCur)] at hdPrev
                rw [hd2, hs1GetFd, hdPrev]
          · have hMeas2 : procCloseMeas dirfd s2 =
                (s2.oracle.length - s2.trace.length) + (2147483648 - nc).toNat := by
              simp [procCloseMeas, hs2Run, hs2Dir, hs2Desc]
            have hMeas1 : procCloseMeas dirfd s =
                (s.oracle.length - s.trace.length) + (2147483648 - cursor).toNat := by
              simp [procCloseMeas, hRun, hDir, hDesc]
            rw [hMeas2, hMeas1, hs2Or, hOr]
            omega

private theorem close_via_proc_self_fd_loop_spec (s0 : sys.Sys) (extra_keep_fd : I32)
    (keep_fds : Slice I32) (dirfd : I32) (eDir : FdEntry)
    (hRun0 : s0.status = .running)
    (hOr0 : OracleNoCloseFault s0 s0.trace.length)
    (hDir0 : s0.getFd dirfd.val = some eDir)
    (c0 : Int) (hc0 : c0 ≤ 0)
    (hDesc0 : s0.getDesc eDir.desc = .procSelfFd c0) :
    OkPost (postfork.fd_ops.close_via_proc_self_fd_loop s0 extra_keep_fd keep_fds dirfd) fun p =>
      p.2.2 = false ∧
      SameChildConfig p.1 s0 ∧
      p.1.status = .running ∧
      p.1.pgid = s0.pgid ∧
      p.1.cwd = s0.cwd ∧
      p.1.sig = s0.sig ∧
      p.1.writeLog = s0.writeLog ∧
      p.1.oracle = s0.oracle ∧
      s0.trace.length ≤ p.1.trace.length ∧
      (∀ d, d ≠ eDir.desc → p.1.getDesc d = s0.getDesc d) ∧
      (∀ fd : Int, 0 ≤ fd → fd ≤ 2147483647 →
        if fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true then
          p.1.getFd fd = s0.getFd fd
        else
          p.1.getFd fd = none) := by
  let inv : sys.Sys → Prop := fun s =>
    ∃ cursor : Int,
      SameChildConfig s s0 ∧
      s.status = .running ∧
      s.pgid = s0.pgid ∧
      s.cwd = s0.cwd ∧
      s.sig = s0.sig ∧
      s.writeLog = s0.writeLog ∧
      s.oracle = s0.oracle ∧
      s0.trace.length ≤ s.trace.length ∧
      s.getFd dirfd.val = some eDir ∧
      s.getDesc eDir.desc = .procSelfFd cursor ∧
      (∀ d, d ≠ eDir.desc → s.getDesc d = s0.getDesc d) ∧
      (∀ fd : Int, 0 ≤ fd → fd ≤ 2147483647 →
        if fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true then
          s.getFd fd = s0.getFd fd
        else if fd < cursor then
          s.getFd fd = none
        else
          s.getFd fd = s0.getFd fd)
  have hInv0 : inv s0 := by
    refine ⟨c0, SameChildConfig.refl s0, hRun0, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, hDir0,
      hDesc0, fun _ _ => rfl, fun fd h0 _ => ?_⟩
    split
    · rfl
    · have hNlt : ¬ (fd < c0) := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hNlt)]
  unfold postfork.fd_ops.close_via_proc_self_fd_loop
  refine okPost_loop_decr_nat (procCloseMeas dirfd) inv _
    (fun s1 => postfork.fd_ops.close_via_proc_self_fd_loop.body extra_keep_fd keep_fds dirfd s1)
    s0 ?_ hInv0
  intro s hs
  rcases hs with ⟨cursor, hCfg, hRun, hPgid, hCwd, hSig, hWl, hOr, hTr, hDir, hDesc, hDescsNe, hFds⟩
  cases hFault : currentFault s with
  | seccomp rawE =>
    exfalso
    have hAt := hOr0 s.trace.length hTr
    unfold currentFault at hFault
    rw [← hOr, hFault] at hAt
    exact hAt
  | fail rawE =>
    exfalso
    have hAt := hOr0 s.trace.length hTr
    unfold currentFault at hFault
    rw [← hOr, hFault] at hAt
    exact hAt
  | normal | partialWrite _ | dentsBatch _ =>
    refine okPost_mono (close_via_proc_self_fd_loop_nonfail_step s0 extra_keep_fd keep_fds dirfd eDir hRun0 s cursor
      hCfg hRun hPgid hCwd hSig hWl hOr hTr hDir hDesc hDescsNe hFds
      (fun rawE h => by rw [hFault] at h; cases h)
      (fun rawE h => by rw [hFault] at h; cases h)) fun r hr => ?_
    cases r with
    | done res =>
      rcases hr with ⟨hRunRes, hFf, hOk⟩
      have hResF : res.2.2 = false := hFf hOr0
      rcases hOk hResF with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      exact ⟨hResF, h1, hRunRes, h2, h3, h4, h5, h6, h7, h8, h9⟩
    | cont _ => exact hr

private theorem close_via_proc_self_fd_loop_safety (s0 : sys.Sys) (extra_keep_fd : I32)
    (keep_fds : Slice I32) (dirfd : I32) (eDir : FdEntry)
    (hRun0 : s0.status = .running)
    (hDir0 : s0.getFd dirfd.val = some eDir)
    (c0 : Int) (hc0 : c0 ≤ 0)
    (hDesc0 : s0.getDesc eDir.desc = .procSelfFd c0) :
    OkPost (postfork.fd_ops.close_via_proc_self_fd_loop s0 extra_keep_fd keep_fds dirfd) fun p =>
      p.1.status = .running ∧
      (p.2.2 = false →
        SameChildConfig p.1 s0 ∧
        p.1.pgid = s0.pgid ∧
        p.1.cwd = s0.cwd ∧
        p.1.sig = s0.sig ∧
        p.1.writeLog = s0.writeLog ∧
        (∀ d, d ≠ eDir.desc → p.1.getDesc d = s0.getDesc d) ∧
        (∀ fd : Int, 0 ≤ fd → fd ≤ 2147483647 →
          if fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true then
            p.1.getFd fd = s0.getFd fd
          else
            p.1.getFd fd = none)) := by
  let inv : sys.Sys → Prop := fun s =>
    ∃ cursor : Int,
      SameChildConfig s s0 ∧
      s.status = .running ∧
      s.pgid = s0.pgid ∧
      s.cwd = s0.cwd ∧
      s.sig = s0.sig ∧
      s.writeLog = s0.writeLog ∧
      s.oracle = s0.oracle ∧
      s0.trace.length ≤ s.trace.length ∧
      s.getFd dirfd.val = some eDir ∧
      s.getDesc eDir.desc = .procSelfFd cursor ∧
      (∀ d, d ≠ eDir.desc → s.getDesc d = s0.getDesc d) ∧
      (∀ fd : Int, 0 ≤ fd → fd ≤ 2147483647 →
        if fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true then
          s.getFd fd = s0.getFd fd
        else if fd < cursor then
          s.getFd fd = none
        else
          s.getFd fd = s0.getFd fd)
  let donePost : (sys.Sys × I32 × Bool) → Prop := fun p =>
    p.1.status = .running ∧
    (p.2.2 = false →
      SameChildConfig p.1 s0 ∧
      p.1.pgid = s0.pgid ∧
      p.1.cwd = s0.cwd ∧
      p.1.sig = s0.sig ∧
      p.1.writeLog = s0.writeLog ∧
      (∀ d, d ≠ eDir.desc → p.1.getDesc d = s0.getDesc d) ∧
      (∀ fd : Int, 0 ≤ fd → fd ≤ 2147483647 →
        if fd ≤ 2 ∨ fd = dirfd.val ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true then
          p.1.getFd fd = s0.getFd fd
        else
          p.1.getFd fd = none))
  have hInv0 : inv s0 := by
    refine ⟨c0, SameChildConfig.refl s0, hRun0, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, hDir0,
      hDesc0, fun _ _ => rfl, fun fd h0 _ => ?_⟩
    split
    · rfl
    · have hNlt : ¬ (fd < c0) := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hNlt)]
  unfold postfork.fd_ops.close_via_proc_self_fd_loop
  refine okPost_loop_decr_nat (procCloseMeas dirfd) inv donePost
    (fun s1 => postfork.fd_ops.close_via_proc_self_fd_loop.body extra_keep_fd keep_fds dirfd s1)
    s0 ?_ hInv0
  intro s hs
  rcases hs with ⟨cursor, hCfg, hRun, hPgid, hCwd, hSig, hWl, hOr, hTr, hDir, hDesc, hDescsNe, hFds⟩
  cases hFault : currentFault s with
  | seccomp rawE =>
    rw [close_proc_body_rw]
    rw [sys_getdents64_seccomp s hRun dirfd rawE hFault, proc_step_bind_ok]
    by_cases hNe : (sanitizeErrno rawE != postfork.fd_ops.EINTR) = true
    · rw [procLoopCont_err_ne extra_keep_fd keep_fds dirfd (sanitizeErrno rawE) _
        (Array.repeat 256#usize 0#u8) hNe]
      exact okPost_ok _ _ ⟨hRun, fun h => by cases h⟩
    · rw [procLoopCont_err_eq extra_keep_fd keep_fds dirfd (sanitizeErrno rawE) _
        (Array.repeat 256#usize 0#u8) hNe]
      have hLt : s.trace.length < s.oracle.length := by
        unfold currentFault at hFault
        cases hGet : s.oracle[s.trace.length]? with
        | none => simp [hGet] at hFault
        | some _ => exact (List.getElem?_eq_some_iff.mp hGet).1
      have hSameFail : SameChildConfig
          { s with trace := s.trace ++ [⟨Req.getdents64 dirfd, .err (sanitizeErrno rawE)⟩] } s :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      refine okPost_ok _ _ ⟨?_, ?_⟩
      · refine ⟨cursor, hSameFail.trans hCfg, hRun, hPgid, hCwd, hSig, hWl, hOr, by simp; omega, hDir, hDesc,
          hDescsNe, hFds⟩
      · simp only [procCloseMeas, ChildState.getFd, ChildState.getDesc] at hDir hDesc ⊢
        simp only [hRun, hDir, hDesc, List.length_append, List.length_cons, List.length_nil]
        omega
  | fail rawE =>
    rw [close_proc_body_rw]
    rw [sys_getdents64_proc_fail s hRun dirfd eDir hDir cursor hDesc rawE hFault, proc_step_bind_ok]
    by_cases hNe : (sanitizeErrno rawE != postfork.fd_ops.EINTR) = true
    · rw [procLoopCont_err_ne extra_keep_fd keep_fds dirfd (sanitizeErrno rawE) _
        (Array.repeat 256#usize 0#u8) hNe]
      exact okPost_ok _ _ ⟨hRun, fun h => by cases h⟩
    · rw [procLoopCont_err_eq extra_keep_fd keep_fds dirfd (sanitizeErrno rawE) _
        (Array.repeat 256#usize 0#u8) hNe]
      have hLt : s.trace.length < s.oracle.length := lt_oracle_of_currentFault_fail hFault
      have hSameFail : SameChildConfig
          { s with trace := s.trace ++ [⟨Req.getdents64 dirfd, .err (sanitizeErrno rawE)⟩] } s :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      refine okPost_ok _ _ ⟨?_, ?_⟩
      · refine ⟨cursor, hSameFail.trans hCfg, hRun, hPgid, hCwd, hSig, hWl, hOr, by simp; omega, hDir, hDesc,
          hDescsNe, hFds⟩
      · simp only [procCloseMeas, ChildState.getFd, ChildState.getDesc] at hDir hDesc ⊢
        simp only [hRun, hDir, hDesc, List.length_append, List.length_cons, List.length_nil]
        omega
  | normal | partialWrite _ | dentsBatch _ =>
    refine okPost_mono
      (close_via_proc_self_fd_loop_nonfail_step s0 extra_keep_fd keep_fds dirfd eDir hRun0 s cursor
        hCfg hRun hPgid hCwd hSig hWl hOr hTr hDir hDesc hDescsNe hFds
        (fun rawE h => by rw [hFault] at h; cases h)
        (fun rawE h => by rw [hFault] at h; cases h))
      fun r hr => ?_
    cases r with
    | done res =>
      rcases hr with ⟨hRunR, _, hOk⟩
      refine ⟨hRunR, fun hF => ?_⟩
      rcases hOk hF with ⟨hCfgR, hPgidR, hCwdR, hSigR, hWlR, _, _, hDescsR, hFdsR⟩
      exact ⟨hCfgR, hPgidR, hCwdR, hSigR, hWlR, hDescsR, hFdsR⟩
    | cont a' => exact hr

private theorem close_via_proc_self_fd_spec_of_free (s : sys.Sys) (extra_keep_fd : I32)
    (keep_fds : Slice I32)
    (hRun : s.status = .running)
    (hCur : currentFault s = .normal)
    (hAvail : s.procSelfFdAvailable = true)
    (hFree : ∃ dirfd, findLowestFreeFd s 0 = some dirfd)
    (hNoSec : oracleHasSeccomp s.oracle = false)
    (hOr : OracleNoCloseFault s (s.trace.length + 1)) :
    OkPost (postfork.fd_ops.close_via_proc_self_fd s extra_keep_fd keep_fds) fun p =>
      p.1 = .Ok () ∧
      SameChildConfig p.2 s ∧
      p.2.status = .running ∧
      p.2.pgid = s.pgid ∧
      p.2.cwd = s.cwd ∧
      p.2.sig = s.sig ∧
      p.2.writeLog = s.writeLog ∧
      p.2.oracle = s.oracle ∧
      s.trace.length ≤ p.2.trace.length ∧
      (∀ fd e, s.getFd fd = some e → p.2.getDesc e.desc = s.getDesc e.desc) ∧
      CloseAbove2Post s extra_keep_fd keep_fds.val p.2 := by
  obtain ⟨dirfd, hLow⟩ := hFree
  have hSpec := findLowestFreeFd_spec s 0 dirfd hLow
  rcases hSpec with ⟨h0Le, _, hLtLim, hLeMax, hOpenFalse, hGetNone⟩
  have hMkVal : (mkI32 dirfd).val = dirfd :=
    mkI32_val (z := dirfd) (by omega) (by omega)
  unfold postfork.fd_ops.close_via_proc_self_fd
  rw [sys_open_proc_self_fd_ok_spec s hRun hCur hAvail dirfd hLow, bind_ok]
  let d0 := freshDescId s
  let eDir : FdEntry := { desc := d0, cloexec := true, extraFdFlags := 0#i32 }
  let s1 : sys.Sys :=
    { (s.putDesc d0 (.procSelfFd (-2))).putSlot dirfd eDir with
      trace := ((s.putDesc d0 (.procSelfFd (-2))).putSlot dirfd eDir).trace ++
        [⟨Req.openProcSelfFd, .okVal (mkI32 dirfd).val⟩] }
  have hs1Cfg : SameChildConfig s1 s :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hs1Run : s1.status = .running := hs1Cfg.status.trans hRun
  have hs1NoSec : oracleHasSeccomp s1.oracle = false := by
    simpa [s1, ChildState.putDesc, ChildState.putSlot] using hNoSec
  have hs1TrLen : s1.trace.length = s.trace.length + 1 := by
    simp [s1, ChildState.putDesc, ChildState.putSlot]
  have hs1OrFault : OracleNoCloseFault s1 s1.trace.length := by
    rw [hs1TrLen]
    exact oracleNoCloseFault_mono (by simp [s1, ChildState.putDesc, ChildState.putSlot]) (Nat.le_refl _) hOr
  have hs1Dir : s1.getFd (mkI32 dirfd).val = some eDir := by
    rw [hMkVal]
    exact getFd_putSlot_self (s.putDesc d0 (.procSelfFd (-2))) dirfd eDir
  have hs1Desc : s1.getDesc eDir.desc = .procSelfFd (-2) := by
    change ((s.putDesc d0 (.procSelfFd (-2))).putSlot dirfd eDir).getDesc d0 = .procSelfFd (-2)
    exact getDesc_putDesc_self s d0 (.procSelfFd (-2))
  refine okPost_bind
    (close_via_proc_self_fd_loop_spec s1 extra_keep_fd keep_fds (mkI32 dirfd) eDir
      hs1Run hs1OrFault hs1Dir (-2) (by decide) hs1Desc)
    fun pLoop hpLoop => ?_
  rcases pLoop with ⟨s2, err, failed⟩
  rcases hpLoop with ⟨hFailed, hCfg2, hRun2, hPgid2, hCwd2, hSig2, hWl2, hOr2, hTr2, hDescs2, hFds2⟩
  dsimp only at hFailed hCfg2 hRun2 hPgid2 hCwd2 hSig2 hWl2 hOr2 hTr2 hDescs2 hFds2
  rcases sys_close_running_exact s2 hRun2 (mkI32 dirfd) with
    ⟨rCl, s3, hEqCl, hCfg3, hPgid3, hCwd3, hSig3, hDescs3, hWl3, hTr3, hFdsCl, _, hClIfOk⟩
  have hS2DirOpen : s2.isOpen (mkI32 dirfd).val = true := by
    have hs2Dir : s2.getFd (mkI32 dirfd).val = s1.getFd (mkI32 dirfd).val := by
      have hStep := hFds2 (mkI32 dirfd).val (by omega) (by omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inr (Or.inl rfl)))] at hStep
      exact hStep
    simp [ChildState.isOpen, hs2Dir, hs1Dir]
  have hNoClS2 : ∀ rawE, currentFault s2 ≠ .seccomp rawE ∧ currentFault s2 ≠ .fail rawE := by
    have hAt := hs1OrFault s2.trace.length hTr2
    unfold currentFault
    rw [← hOr2] at hAt
    exact fun rawE => ⟨fun hF => by rw [hF] at hAt; exact hAt, fun hF => by rw [hF] at hAt; exact hAt⟩
  have hrClOk : rCl = .Ok () := hClIfOk hNoClS2 hS2DirOpen
  have hGetCl : ∀ k : Int, s3.getFd k = if k == (mkI32 dirfd).val then none else s2.getFd k := by
    intro k
    cases hf : currentFault s2 with
    | seccomp rawE => exact absurd hf (hNoClS2 rawE).1
    | fail rawE => exact absurd hf (hNoClS2 rawE).2
    | normal | partialWrite _ | dentsBatch _ =>
      simp only [hf] at hFdsCl
      rw [show s3.getFd k = (s2.closeSlot (mkI32 dirfd).val).getFd k from by simp [ChildState.getFd, hFdsCl]]
      by_cases hkf : k == (mkI32 dirfd).val
      · have hEqk : k = (mkI32 dirfd).val := beq_iff_eq.mp hkf
        subst hEqk; simp only [beq_self_eq_true, ↓reduceIte]; exact getFd_closeSlot_self s2 _
      · have hNek : k ≠ (mkI32 dirfd).val := fun h => hkf (beq_iff_eq.mpr h)
        simp only [hkf, Bool.false_eq_true, ↓reduceIte]; exact getFd_closeSlot_ne s2 hNek
  change OkPost (do
    let pCl ← sys.close s2 (mkI32 dirfd)
    let p4 ←
      match pCl.1 with
      | core.result.Result.Ok _ => ok (pCl.2, err, failed)
      | core.result.Result.Err ce => do
        let ib ← if failed then ok (err, failed) else ok (ce, true)
        ok (pCl.2, ib.1, ib.2)
    if p4.2.2 then ok (core.result.Result.Err p4.2.1, p4.1) else ok (core.result.Result.Ok (), p4.1)) _
  rw [hEqCl, bind_ok, hrClOk, hFailed]
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  have hs3Cfg : SameChildConfig s3 s := hCfg3.trans (hCfg2.trans hs1Cfg)
  apply okPost_ok
  refine ⟨rfl, hs3Cfg, hs3Cfg.status.trans hRun,
    hPgid3.trans (hPgid2.trans (by simp [s1, ChildState.putDesc, ChildState.putSlot])),
    hCwd3.trans (hCwd2.trans (by simp [s1, ChildState.putDesc, ChildState.putSlot])),
    hSig3.trans (hSig2.trans (by simp [s1, ChildState.putDesc, ChildState.putSlot])),
    hWl3.trans (hWl2.trans (by simp [s1, ChildState.putDesc, ChildState.putSlot])),
    hCfg3.oracle.trans (hOr2.trans (by simp [s1, ChildState.putDesc, ChildState.putSlot])),
    by dsimp only; rw [hTr3]; omega, ?_, ?_⟩
  · intro fd e hFd
    have hNe : e.desc ≠ d0 := Nat.ne_of_lt (desc_lt_freshDescId_of_getFd s hFd)
    have hd3 : s3.getDesc e.desc = s2.getDesc e.desc := by simp [ChildState.getDesc, hDescs3]
    rw [hd3, hDescs2 e.desc hNe]
    change (s.putDesc d0 (.procSelfFd (-2))).getDesc e.desc = s.getDesc e.desc
    exact getDesc_putDesc_ne s hNe (.procSelfFd (-2))
  · have hGetSlotNe : ∀ fd, fd ≠ dirfd → s1.getFd fd = s.getFd fd := by
      intro fd hne
      exact getFd_putSlot_ne (s.putDesc d0 (.procSelfFd (-2))) hne eDir
    refine ⟨?_, ?_⟩
    · intro fd h0 h2
      have hMax : fd ≤ 2147483647 := by omega
      rw [hGetCl fd, hMkVal]
      by_cases hEqDir : fd = dirfd
      · subst hEqDir
        simp [hGetNone]
      · simp only [beq_false_of_ne hEqDir, Bool.false_eq_true, ↓reduceIte]
        have hStep := hFds2 fd h0 hMax
        have hCond : fd ≤ 2 ∨ fd = (mkI32 dirfd).val ∨
            Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true := by
          simp [h2]
        rw [ite_eq_left_of_eq_true _ _ (eq_true hCond)] at hStep
        rw [hStep, hGetSlotNe fd hEqDir]
    · intro fd h3 hMax
      have h0 : 0 ≤ fd := by omega
      have hNot2 : ¬ (fd ≤ 2) := by omega
      by_cases hEqDir : fd = dirfd
      · subst hEqDir
        split
        · rw [hGetCl fd, hMkVal]
          simp [hGetNone]
        · rw [hGetCl fd, hMkVal]
          simp
      · have hStep := hFds2 fd h0 hMax
        have hNotEqDir : fd ≠ (mkI32 dirfd).val := by rw [hMkVal]; exact hEqDir
        by_cases hKept : Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true
        · have hCond : fd ≤ 2 ∨ fd = (mkI32 dirfd).val ∨
              Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true := by
            simp [hKept]
          rw [ite_eq_left_of_eq_true _ _ (eq_true hCond)] at hStep
          rw [ite_eq_left_of_eq_true _ _ (eq_true hKept)]
          rw [hGetCl fd, hMkVal, beq_false_of_ne hEqDir]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hStep, hGetSlotNe fd hEqDir]
        · have hCond : ¬ (fd ≤ 2 ∨ fd = (mkI32 dirfd).val ∨
              Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true) := by
            simp [hNot2, hNotEqDir, hKept]
          rw [ite_eq_right_of_eq_false _ _ (eq_false hCond)] at hStep
          rw [ite_eq_right_of_eq_false _ _ (eq_false hKept)]
          rw [hGetCl fd, hMkVal, beq_false_of_ne hEqDir]
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact hStep

private theorem close_via_proc_self_fd_spec (s : sys.Sys) (extra_keep_fd : I32)
    (keep_fds : Slice I32)
    (hRun : s.status = .running)
    (hCur : currentFault s = .normal)
    (hAvail : s.procSelfFdAvailable = true)
    (hLim : min s.fdLimit 2147483648 ≥ 1 + Int.ofNat s.fds.length)
    (hNoSec : oracleHasSeccomp s.oracle = false)
    (hOr : OracleNoCloseFault s (s.trace.length + 1)) :
    OkPost (postfork.fd_ops.close_via_proc_self_fd s extra_keep_fd keep_fds) fun p =>
      p.1 = .Ok () ∧
      SameChildConfig p.2 s ∧
      p.2.status = .running ∧
      p.2.pgid = s.pgid ∧
      p.2.cwd = s.cwd ∧
      p.2.sig = s.sig ∧
      p.2.writeLog = s.writeLog ∧
      p.2.oracle = s.oracle ∧
      s.trace.length ≤ p.2.trace.length ∧
      (∀ fd e, s.getFd fd = some e → p.2.getDesc e.desc = s.getDesc e.desc) ∧
      CloseAbove2Post s extra_keep_fd keep_fds.val p.2 :=
  close_via_proc_self_fd_spec_of_free s extra_keep_fd keep_fds hRun hCur hAvail
    (findLowestFreeFd_zero_some_of_lt s hLim) hNoSec hOr

private theorem close_via_proc_self_fd_err_spec_of_free (s : sys.Sys) (extra_keep_fd : I32)
    (keep_fds : Slice I32)
    (hRun : s.status = .running)
    (hNoSec : oracleHasSeccomp s.oracle = false)
    (hNotAvail : s.procSelfFdAvailable = false)
    (hFree : ∃ dirfd, findLowestFreeFd s 0 = some dirfd) :
    OkPost (postfork.fd_ops.close_via_proc_self_fd s extra_keep_fd keep_fds) fun p =>
      p.1 = .Err (sanitizeErrno s.procOpenErrno) ∧
      SameChildConfig p.2 s ∧
      p.2.status = .running ∧
      p.2.pgid = s.pgid ∧
      p.2.cwd = s.cwd ∧
      p.2.sig = s.sig ∧
      p.2.descs = s.descs ∧
      p.2.writeLog = s.writeLog ∧
      p.2.fds = s.fds := by
  obtain ⟨dirfd, hLow⟩ := hFree
  unfold postfork.fd_ops.close_via_proc_self_fd
  rw [sys_open_proc_self_fd_err_spec s hRun
    (fun rawE hS => not_seccomp_of_oracleHasSeccomp_false hNoSec hS) hNotAvail dirfd hLow, bind_ok]
  exact okPost_ok _ _ ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    hRun, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem close_via_proc_self_fd_err_spec (s : sys.Sys) (extra_keep_fd : I32)
    (keep_fds : Slice I32)
    (hRun : s.status = .running)
    (hNoSec : oracleHasSeccomp s.oracle = false)
    (hNotAvail : s.procSelfFdAvailable = false)
    (hLim : min s.fdLimit 2147483648 ≥ 1 + Int.ofNat s.fds.length) :
    OkPost (postfork.fd_ops.close_via_proc_self_fd s extra_keep_fd keep_fds) fun p =>
      p.1 = .Err (sanitizeErrno s.procOpenErrno) ∧
      SameChildConfig p.2 s ∧
      p.2.status = .running ∧
      p.2.pgid = s.pgid ∧
      p.2.cwd = s.cwd ∧
      p.2.sig = s.sig ∧
      p.2.descs = s.descs ∧
      p.2.writeLog = s.writeLog ∧
      p.2.fds = s.fds :=
  close_via_proc_self_fd_err_spec_of_free s extra_keep_fd keep_fds hRun hNoSec hNotAvail
    (findLowestFreeFd_zero_some_of_lt s hLim)

/-- Specification of `close_fds_above2_except` on a valid child state when either `close_range` or `/proc/self/fd` fallback is available. -/
theorem close_fds_above2_except_spec (s : sys.Sys) (extra_keep_fd : I32) (keep_fds : Slice I32)
    (hRun : s.status = .running)
    (hOr : s.oracle = [])
    (hCap : s.closeRangeSupported = true ∨
      (s.procSelfFdAvailable = true ∧ min s.fdLimit 2147483648 ≥ 1 + Int.ofNat s.fds.length)) :
    OkPost (postfork.fd_ops.close_fds_above2_except s extra_keep_fd keep_fds) fun p =>
      p.1 = .Ok () ∧
      SameChildConfig p.2 s ∧
      p.2.status = .running ∧
      p.2.pgid = s.pgid ∧
      p.2.cwd = s.cwd ∧
      p.2.sig = s.sig ∧
      p.2.writeLog = s.writeLog ∧
      p.2.oracle = s.oracle ∧
      (∀ fd e, s.getFd fd = some e → p.2.getDesc e.desc = s.getDesc e.desc) ∧
      CloseAbove2Post s extra_keep_fd keep_fds.val p.2 := by
  unfold postfork.fd_ops.close_fds_above2_except
  by_cases hCr : s.closeRangeSupported = true
  · refine okPost_bind
      (try_close_range_except_spec s hRun hOr hCr extra_keep_fd keep_fds)
      fun ⟨r, s1⟩ hs1 => ?_
    rcases hs1 with ⟨hr, hCfg1, hPgid1, hCwd1, hSig1, hDescs1, hWl1, hClose1⟩
    dsimp only at hr hCfg1 hPgid1 hCwd1 hSig1 hDescs1 hWl1 hClose1
    rw [hr]
    exact okPost_ok _ _ ⟨rfl, hCfg1, hCfg1.status.trans hRun, hPgid1, hCwd1, hSig1, hWl1,
      hCfg1.oracle, fun fd e _ => by simp [ChildState.getDesc, hDescs1], hClose1⟩
  · have hCrF : s.closeRangeSupported = false := Bool.eq_false_iff.mpr hCr
    have hProc : s.procSelfFdAvailable = true ∧ min s.fdLimit 2147483648 ≥ 1 + Int.ofNat s.fds.length := by
      rcases hCap with h | h
      · exact absurd h hCr
      · exact h
    refine okPost_bind
      (try_close_range_except_err_spec s hRun hCrF extra_keep_fd keep_fds)
      fun ⟨r, s1⟩ hs1 => ?_
    rcases hs1 with ⟨hr, hCfg1, hPgid1, hCwd1, hSig1, hWl1, hDescs1, hFds1, hTr1⟩
    dsimp only at hr hCfg1 hPgid1 hCwd1 hSig1 hWl1 hDescs1 hFds1 hTr1
    rcases hr with ⟨errCr, hrEq, _⟩
    rw [hrEq]
    have hs1Run : s1.status = .running := hCfg1.status.trans hRun
    have hs1Or : s1.oracle = [] := hCfg1.oracle.trans hOr
    have hs1Cur : currentFault s1 = .normal := by unfold currentFault; simp [hs1Or]
    have hs1Avail : s1.procSelfFdAvailable = true := hCfg1.procSelfFdAvailable.trans hProc.1
    have hs1Lim : min s1.fdLimit 2147483648 ≥ 1 + Int.ofNat s1.fds.length := by
      rw [hCfg1.fdLimit, hFds1]; exact hProc.2
    have hs1NoSec : oracleHasSeccomp s1.oracle = false := by simp [hs1Or, oracleHasSeccomp]
    have hs1NoClose : OracleNoCloseFault s1 (s1.trace.length + 1) := by
      intro k _
      simp [hs1Or]
    refine okPost_mono
      (close_via_proc_self_fd_spec s1 extra_keep_fd keep_fds hs1Run hs1Cur hs1Avail hs1Lim hs1NoSec hs1NoClose)
      fun ⟨r2, s2⟩ hs2 => ?_
    rcases hs2 with ⟨hr2, hCfg2, hRun2, hPgid2, hCwd2, hSig2, hWl2, hOr2, _, hDescFd2, hClose2⟩
    have hGet1 : ∀ fd, s1.getFd fd = s.getFd fd := fun fd => by simp [ChildState.getFd, hFds1]
    have hClose' : CloseAbove2Post s extra_keep_fd keep_fds.val s2 := by
      refine ⟨fun fd h0 h2 => ?_, fun fd h3 hMax => ?_⟩
      · rw [hClose2.1 fd h0 h2, hGet1 fd]
      · have h2 := hClose2.2 fd h3 hMax
        split at h2
        · next hk => rw [ite_eq_left_of_eq_true _ _ (eq_true hk), h2, hGet1 fd]
        · next hk => rw [ite_eq_right_of_eq_false _ _ (eq_false hk), h2]
    refine ⟨hr2, hCfg2.trans hCfg1, hRun2, hPgid2.trans hPgid1, hCwd2.trans hCwd1,
      hSig2.trans hSig1, hWl2.trans hWl1, hOr2.trans hCfg1.oracle, ?_, hClose'⟩
    intro fd e hFd
    have hFd1 : s1.getFd fd = some e := by rw [hGet1 fd]; exact hFd
    rw [hDescFd2 fd e hFd1]
    simp [ChildState.getDesc, hDescs1]

private theorem sys_open_proc_self_fd_safety (s : sys.Sys) (hRun : s.status = .running) :
    OkPost (sys.open_proc_self_fd s) fun p =>
      SameChildConfig p.2 s ∧ p.2.status = .running ∧ p.2.pgid = s.pgid ∧
      p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧ p.2.writeLog = s.writeLog ∧
      (∀ dirfd, p.1 = .Ok dirfd →
        0 ≤ dirfd.val ∧ dirfd.val < min s.fdLimit 2147483648 ∧ dirfd.val ≤ 2147483647 ∧
        s.getFd dirfd.val = none ∧
        dirfd = mkI32 dirfd.val ∧
        ∃ d0 eDir,
          d0 = freshDescId s ∧
          eDir = { desc := d0, cloexec := true, extraFdFlags := 0#i32 } ∧
          p.2.getFd dirfd.val = some eDir ∧
          p.2.getDesc eDir.desc = .procSelfFd (-2) ∧
          (∀ fd, fd ≠ dirfd.val → p.2.getFd fd = s.getFd fd) ∧
          (∀ d, d ≠ d0 → p.2.getDesc d = s.getDesc d)) := by
  unfold sys.open_proc_self_fd LeanSwe.PostFork.Aeneas.Internal.Sys.open_proc_self_fd
  cases hLow : findLowestFreeFd s 0 with
  | none =>
    rcases runI32Syscall_running s hRun .openProcSelfFd (some EMFILE) (fun s => (0#i32, s)) with
      ⟨r, s', hEq, hr⟩
    rw [hEq]
    cases hf : currentFault s <;> (
      simp only [hf] at hr
      rcases hr with ⟨rfl, rfl⟩
      exact okPost_ok _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        hRun, rfl, rfl, rfl, rfl, fun _ h => nomatch h⟩)
  | some dirfd =>
    by_cases hAvail : (!s.procSelfFdAvailable) = true
    · simp only [hAvail, ↓reduceIte]
      rcases runI32Syscall_running s hRun .openProcSelfFd (some (sanitizeErrno s.procOpenErrno))
          (fun s => (0#i32, s)) with ⟨r, s', hEq, hr⟩
      rw [hEq]
      cases hf : currentFault s <;> (
        simp only [hf] at hr
        rcases hr with ⟨rfl, rfl⟩
        exact okPost_ok _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          hRun, rfl, rfl, rfl, rfl, fun _ h => nomatch h⟩)
    · have hAvailF : (!s.procSelfFdAvailable) = false := Bool.eq_false_iff.mpr hAvail
      simp only [hAvailF, Bool.false_eq_true, ↓reduceIte]
      have hSpec := findLowestFreeFd_spec s 0 dirfd hLow
      rcases hSpec with ⟨h0Le, _, hLtLim, hLeMax, _, hGetNone⟩
      have hMkVal : (mkI32 dirfd).val = dirfd := mkI32_val (z := dirfd) (by omega) (by omega)
      rcases runI32Syscall_running s hRun .openProcSelfFd none
          (fun s =>
            let d := freshDescId s
            let s1 := s.putDesc d (.procSelfFd (-2))
            let s2 := s1.putSlot dirfd { desc := d, cloexec := true, extraFdFlags := 0#i32 }
            (mkI32 dirfd, s2)) with ⟨r, s', hEq, hr⟩
      rw [hEq]
      cases hf : currentFault s with
      | seccomp rawE =>
        simp only [hf] at hr
        rcases hr with ⟨rfl, rfl⟩
        exact okPost_ok _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          hRun, rfl, rfl, rfl, rfl, fun _ h => nomatch h⟩
      | fail rawE =>
        simp only [hf] at hr
        rcases hr with ⟨rfl, rfl⟩
        exact okPost_ok _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          hRun, rfl, rfl, rfl, rfl, fun _ h => nomatch h⟩
      | normal | partialWrite _ | dentsBatch _ =>
        simp only [hf] at hr
        rcases hr with ⟨rfl, rfl⟩
        refine okPost_ok _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          hRun, rfl, rfl, rfl, rfl, fun dirfd' hOk => ?_⟩
        have hEqDir : dirfd' = mkI32 dirfd := by cases hOk; rfl
        subst hEqDir
        rw [hMkVal]
        refine ⟨h0Le, hLtLim, hLeMax, hGetNone, ?_, freshDescId s,
          { desc := freshDescId s, cloexec := true, extraFdFlags := 0#i32 }, rfl, rfl, ?_, ?_, ?_, ?_⟩
        · rfl
        · exact getFd_putSlot_self (s.putDesc (freshDescId s) (.procSelfFd (-2))) dirfd _
        · exact getDesc_putDesc_self s (freshDescId s) (.procSelfFd (-2))
        · intro fd hNe
          exact getFd_putSlot_ne (s.putDesc (freshDescId s) (.procSelfFd (-2))) hNe _
        · intro d hNe
          exact getDesc_putDesc_ne s hNe (.procSelfFd (-2))

private theorem close_via_proc_self_fd_safety (s : sys.Sys) (extra_keep_fd : I32)
    (keep_fds : Slice I32) (hRun : s.status = .running) :
    OkPost (postfork.fd_ops.close_via_proc_self_fd s extra_keep_fd keep_fds) fun p =>
      p.2.status = .running ∧
      (p.1 = .Ok () →
        SameChildConfig p.2 s ∧
        p.2.pgid = s.pgid ∧
        p.2.cwd = s.cwd ∧
        p.2.sig = s.sig ∧
        p.2.writeLog = s.writeLog ∧
        (∀ fd e, s.getFd fd = some e → p.2.getDesc e.desc = s.getDesc e.desc) ∧
        (∀ fd : Int, 0 ≤ fd → fd ≤ 2 → s.getFd fd ≠ none → p.2.getFd fd = s.getFd fd) ∧
        (∀ fd : Int, 3 ≤ fd → fd ≤ 2147483647 →
          Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true → s.getFd fd ≠ none →
          p.2.getFd fd = s.getFd fd) ∧
        CloseAbove2Post s extra_keep_fd keep_fds.val p.2) := by
  unfold postfork.fd_ops.close_via_proc_self_fd
  refine okPost_bind (sys_open_proc_self_fd_safety s hRun) fun ⟨r1, s1⟩ hs1 => ?_
  rcases hs1 with ⟨hs1Cfg, hs1Run, hs1Pgid, hs1Cwd, hs1Sig, hs1Wl, hs1Ok⟩
  cases r1 with
  | Err e =>
    exact okPost_ok _ _ ⟨hs1Run, fun h => by cases h⟩
  | Ok dirfd =>
    rcases hs1Ok dirfd rfl with
      ⟨h0Le, hLtLim, hLeMax, hGetNone, hMk, d0, eDir, hd0, heDir, hs1Dir, hs1Desc, hs1FdNe, hs1DescNe⟩
    refine okPost_bind
      (close_via_proc_self_fd_loop_safety s1 extra_keep_fd keep_fds dirfd eDir hs1Run hs1Dir
        (-2) (by decide) hs1Desc)
      fun pLoop hpLoop => ?_
    rcases pLoop with ⟨s2, err, failed⟩
    rcases hpLoop with ⟨hs2Run, hs2Ok⟩
    rcases sys_close_running_exact s2 hs2Run dirfd with
      ⟨rCl, s3, hEqCl, hCfg3, hPgid3, hCwd3, hSig3, hDescs3, hWl3, _, hFdsCl, hClOkIf, _⟩
    change OkPost (do
      let pCl ← sys.close s2 dirfd
      let p4 ←
        match pCl.1 with
        | core.result.Result.Ok _ => ok (pCl.2, err, failed)
        | core.result.Result.Err ce => do
          let ib ← if failed then ok (err, failed) else ok (ce, true)
          ok (pCl.2, ib.1, ib.2)
      if p4.2.2 then ok (core.result.Result.Err p4.2.1, p4.1) else ok (core.result.Result.Ok (), p4.1)) _
    rw [hEqCl, bind_ok]
    have hs3Run : s3.status = .running := hCfg3.status.trans hs2Run
    cases rCl with
    | Err ce =>
      cases failed
      · simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
        apply okPost_ok
        refine ⟨hs3Run, fun h => by cases h⟩
      · simp only [bind_ok, ↓reduceIte]
        apply okPost_ok
        refine ⟨hs3Run, fun h => by cases h⟩
    | Ok u =>
      by_cases hf : failed = true
      · simp only [bind_ok, hf, ↓reduceIte]
        apply okPost_ok
        refine ⟨hs3Run, fun h => by cases h⟩
      · have hff : failed = false := Bool.eq_false_iff.mpr hf
        simp only [bind_ok, hff, Bool.false_eq_true, ↓reduceIte]
        have hNoSecFail : ∀ rawE, currentFault s2 ≠ .seccomp rawE ∧ currentFault s2 ≠ .fail rawE :=
          hClOkIf rfl
        have hGetCl : ∀ k : Int, s3.getFd k = if k == dirfd.val then none else s2.getFd k := by
          intro k
          cases hf2 : currentFault s2 with
          | seccomp rawE => exact absurd hf2 (hNoSecFail rawE).1
          | fail rawE => exact absurd hf2 (hNoSecFail rawE).2
          | normal | partialWrite _ | dentsBatch _ =>
            simp only [hf2] at hFdsCl
            rw [show s3.getFd k = (s2.closeSlot dirfd.val).getFd k from by simp [ChildState.getFd, hFdsCl]]
            by_cases hkf : k == dirfd.val
            · have hEqk : k = dirfd.val := beq_iff_eq.mp hkf
              subst hEqk; simp only [beq_self_eq_true, ↓reduceIte]; exact getFd_closeSlot_self s2 _
            · have hNek : k ≠ dirfd.val := fun h => hkf (beq_iff_eq.mpr h)
              simp only [hkf, Bool.false_eq_true, ↓reduceIte]; exact getFd_closeSlot_ne s2 hNek
        rcases hs2Ok hff with ⟨hCfg2, hPgid2, hCwd2, hSig2, hWl2, hDescs2, hFds2⟩
        apply okPost_ok
        refine ⟨hs3Run, fun _ => ?_⟩
        refine ⟨hCfg3.trans (hCfg2.trans hs1Cfg),
          hPgid3.trans (hPgid2.trans hs1Pgid),
          hCwd3.trans (hCwd2.trans hs1Cwd),
          hSig3.trans (hSig2.trans hs1Sig),
          hWl3.trans (hWl2.trans hs1Wl), ?_, ?_, ?_, ?_⟩
        · intro fd e hFd
          have hNe : e.desc ≠ d0 := by rw [hd0]; exact Nat.ne_of_lt (desc_lt_freshDescId_of_getFd s hFd)
          have hNeE : e.desc ≠ eDir.desc := by rw [heDir]; exact hNe
          have hd3 : s3.getDesc e.desc = s2.getDesc e.desc := by simp [ChildState.getDesc, hDescs3]
          rw [hd3, hDescs2 e.desc hNeE, hs1DescNe e.desc hNe]
        · have hDirNeFd : ∀ fd, fd ≠ dirfd.val → s1.getFd fd = s.getFd fd := hs1FdNe
          intro fd h0 h2 hOpen
          have hEqDir : fd ≠ dirfd.val := fun hEq => by rw [hEq] at hOpen; exact hOpen hGetNone
          have hMax : fd ≤ 2147483647 := by omega
          have hStep := hFds2 fd h0 hMax
          have hCond : fd ≤ 2 ∨ fd = dirfd.val ∨
              Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true := by
            simp [h2]
          rw [ite_eq_left_of_eq_true _ _ (eq_true hCond)] at hStep
          rw [hGetCl fd]
          simp only [beq_false_of_ne hEqDir, Bool.false_eq_true, ↓reduceIte]
          rw [hStep, hDirNeFd fd hEqDir]
        · have hDirNeFd : ∀ fd, fd ≠ dirfd.val → s1.getFd fd = s.getFd fd := hs1FdNe
          intro fd h3 hMax hKept hOpen
          have hEqDir : fd ≠ dirfd.val := fun hEq => by rw [hEq] at hOpen; exact hOpen hGetNone
          have h0 : 0 ≤ fd := by omega
          have hStep := hFds2 fd h0 hMax
          have hCond : fd ≤ 2 ∨ fd = dirfd.val ∨
              Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true := by
            simp [hKept]
          rw [ite_eq_left_of_eq_true _ _ (eq_true hCond)] at hStep
          rw [hGetCl fd]
          simp only [beq_false_of_ne hEqDir, Bool.false_eq_true, ↓reduceIte]
          rw [hStep, hDirNeFd fd hEqDir]
        · have hDirNeFd : ∀ fd, fd ≠ dirfd.val → s1.getFd fd = s.getFd fd := hs1FdNe
          refine ⟨?_, ?_⟩
          · intro fd h0 h2
            have hMax : fd ≤ 2147483647 := by omega
            rw [hGetCl fd]
            by_cases hEqDir : fd = dirfd.val
            · subst hEqDir
              simp [hGetNone]
            · simp only [beq_false_of_ne hEqDir, Bool.false_eq_true, ↓reduceIte]
              have hStep := hFds2 fd h0 hMax
              have hCond : fd ≤ 2 ∨ fd = dirfd.val ∨
                  Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true := by
                simp [h2]
              rw [ite_eq_left_of_eq_true _ _ (eq_true hCond)] at hStep
              rw [hStep, hDirNeFd fd hEqDir]
          · intro fd h3 hMax
            have h0 : 0 ≤ fd := by omega
            have hNot2 : ¬ (fd ≤ 2) := by omega
            by_cases hEqDir : fd = dirfd.val
            · split
              · rw [hGetCl fd, hEqDir]; simp [hGetNone]
              · rw [hGetCl fd, hEqDir]; simp
            · have hStep := hFds2 fd h0 hMax
              by_cases hKept : Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true
              · have hCond : fd ≤ 2 ∨ fd = dirfd.val ∨
                    Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true := by
                  simp [hKept]
                rw [ite_eq_left_of_eq_true _ _ (eq_true hCond)] at hStep
                rw [ite_eq_left_of_eq_true _ _ (eq_true hKept)]
                rw [hGetCl fd, beq_false_of_ne hEqDir]
                simp only [Bool.false_eq_true, ↓reduceIte]
                rw [hStep, hDirNeFd fd hEqDir]
              · have hCond : ¬ (fd ≤ 2 ∨ fd = dirfd.val ∨
                    Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true) := by
                  simp [hNot2, hEqDir, hKept]
                rw [ite_eq_right_of_eq_false _ _ (eq_false hCond)] at hStep
                rw [ite_eq_right_of_eq_false _ _ (eq_false hKept)]
                rw [hGetCl fd, beq_false_of_ne hEqDir]
                simp only [Bool.false_eq_true, ↓reduceIte]
                exact hStep

/-- Arbitrary-oracle safety specification for `postfork.fd_ops.close_fds_above2_except`. -/
theorem close_fds_above2_except_safety (s : sys.Sys) (extra_keep_fd : I32) (keep_fds : Slice I32)
    (hRun : s.status = .running) :
    OkPost (postfork.fd_ops.close_fds_above2_except s extra_keep_fd keep_fds) fun p =>
      p.2.status = .running ∧
      (p.1 = .Ok () →
        SameChildConfig p.2 s ∧
        p.2.pgid = s.pgid ∧
        p.2.cwd = s.cwd ∧
        p.2.sig = s.sig ∧
        p.2.writeLog = s.writeLog ∧
        (∀ fd e, 0 ≤ fd → fd ≤ 2147483647 →
          (fd ≤ 2 ∨ Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true) →
          s.getFd fd = some e → p.2.getDesc e.desc = s.getDesc e.desc) ∧
        (∀ fd : Int, 0 ≤ fd → fd ≤ 2 → s.getFd fd ≠ none → p.2.getFd fd = s.getFd fd) ∧
        (∀ fd : Int, 3 ≤ fd → fd ≤ 2147483647 →
          Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true → s.getFd fd ≠ none →
          p.2.getFd fd = s.getFd fd) ∧
        CloseAbove2Post s extra_keep_fd keep_fds.val p.2) := by
  unfold postfork.fd_ops.close_fds_above2_except
  refine okPost_bind (try_close_range_except_safety s hRun extra_keep_fd keep_fds) fun ⟨r1, s1⟩ hs1 => ?_
  dsimp only at hs1
  rcases hs1 with ⟨hCfg1, hs1Run, hPgid1, hCwd1, hSig1, hDescs1, hWl1, h02_1, hKept1, hOk1⟩
  cases r1 with
  | Ok _ =>
    exact okPost_ok _ _ ⟨hs1Run, fun _ =>
      ⟨hCfg1, hPgid1, hCwd1, hSig1, hWl1,
        (fun fd e _ _ _ _ => by simp [ChildState.getDesc, hDescs1]),
        (fun fd h0 h2 _ => h02_1 fd h0 h2),
        (fun fd h3 hMax hKept _ => hKept1 fd h3 hMax hKept),
        hOk1 rfl⟩⟩
  | Err _ =>
    refine okPost_mono (close_via_proc_self_fd_safety s1 extra_keep_fd keep_fds hs1Run) fun ⟨r2, s2⟩ hs2 => ?_
    dsimp only at hs2
    rcases hs2 with ⟨hs2Run, hs2Ok⟩
    refine ⟨hs2Run, fun hr2 => ?_⟩
    rcases hs2Ok hr2 with ⟨hCfg2, hPgid2, hCwd2, hSig2, hWl2, hDesc2, h02_2, hKept2, hClose2⟩
    refine ⟨hCfg2.trans hCfg1, hPgid2.trans hPgid1, hCwd2.trans hCwd1, hSig2.trans hSig1, hWl2.trans hWl1,
      ?_, ?_, ?_, ?_⟩
    · intro fd e h0 hMax hKeepOrLow hFd
      rcases hKeepOrLow with h2 | hKept
      · have hFd1 : s1.getFd fd = some e := by rw [h02_1 fd h0 h2]; exact hFd
        rw [hDesc2 fd e hFd1]
        simp [ChildState.getDesc, hDescs1]
      · by_cases h2 : fd ≤ 2
        · have hFd1 : s1.getFd fd = some e := by rw [h02_1 fd h0 h2]; exact hFd
          rw [hDesc2 fd e hFd1]
          simp [ChildState.getDesc, hDescs1]
        · have h3 : 3 ≤ fd := by omega
          have hFd1 : s1.getFd fd = some e := by rw [hKept1 fd h3 hMax hKept]; exact hFd
          rw [hDesc2 fd e hFd1]
          simp [ChildState.getDesc, hDescs1]
    · intro fd h0 h2 hOpen
      have hOpen1 : s1.getFd fd ≠ none := by rw [h02_1 fd h0 h2]; exact hOpen
      rw [h02_2 fd h0 h2 hOpen1, h02_1 fd h0 h2]
    · intro fd h3 hMax hKept hOpen
      have hOpen1 : s1.getFd fd ≠ none := by rw [hKept1 fd h3 hMax hKept]; exact hOpen
      rw [hKept2 fd h3 hMax hKept hOpen1, hKept1 fd h3 hMax hKept]
    · refine ⟨fun fd h0 h2 => ?_, fun fd h3 hMax => ?_⟩
      · rw [hClose2.1 fd h0 h2, h02_1 fd h0 h2]
      · have h2 := hClose2.2 fd h3 hMax
        split at h2
        · next hk => rw [ite_eq_left_of_eq_true _ _ (eq_true hk), h2, hKept1 fd h3 hMax hk]
        · next hk => rw [ite_eq_right_of_eq_false _ _ (eq_false hk), h2]

/-- Kernel proof of `test_postfork_closeFdsAbove2Except_closeRangeAndProcFallback` (`Core.AllPass`). -/
theorem test_postfork_closeFdsAbove2Except_closeRangeAndProcFallback_allPass :
    Core.AllPass
      (test_postfork_closeFdsAbove2Except_closeRangeAndProcFallback rustAeneasApi) := by
  intro s extraKeep keepFds
  refine ⟨close_fds_above2_except_total s extraKeep keepFds, ?_⟩
  let sHighProc : ChildState :=
    { fdLimit := 64
      closeRangeSupported := false
      closeRangeErrno := ENOSYS
      procSelfFdAvailable := true
      fds :=
        [ (0, { desc := 10, cloexec := false })
        , (1, { desc := 11, cloexec := false })
        , (2, { desc := 12, cloexec := false })
        , (7, { desc := 17, cloexec := true })
        , (42, { desc := 42, cloexec := false })
        , (500, { desc := 50, cloexec := false })
        , (70000, { desc := 70, cloexec := false }) ]
      oracle := [.normal, .normal, .fail EINTR, .dentsBatch 0, .dentsBatch 0, .dentsBatch 0] }
  let keepHigh := mkSliceI32 2#usize [(-1)#i32, 42#i32]
  have hHigh : OkPost
      (postfork.fd_ops.close_fds_above2_except sHighProc 7#i32 keepHigh) fun p =>
        p.1 = .Ok () ∧
        p.2.isOpen 0 = true ∧ p.2.isOpen 1 = true ∧ p.2.isOpen 2 = true ∧
        p.2.isOpen 7 = true ∧ p.2.isOpen 42 = true ∧
        p.2.isOpen 500 = false ∧ p.2.isOpen 70000 = false := by
    unfold postfork.fd_ops.close_fds_above2_except
    refine okPost_bind
      (try_close_range_except_err_spec sHighProc rfl rfl 7#i32 keepHigh)
      fun ⟨r1, s1⟩ hs1 => ?_
    rcases hs1 with ⟨hr1, hCfg1, _, _, _, _, _, hFds1, hTr1⟩
    dsimp only at hr1 hCfg1 hFds1 hTr1
    rcases hr1 with ⟨errCr, hr1Eq, _⟩
    rw [hr1Eq]
    have hs1Run : s1.status = .running := hCfg1.status
    have hs1Or : s1.oracle = sHighProc.oracle := hCfg1.oracle
    have hs1Tr : s1.trace.length = 1 := by simpa [sHighProc] using hTr1
    have hs1Cur : currentFault s1 = .normal := by
      unfold currentFault
      rw [hs1Tr, hs1Or]
      rfl
    have hs1Avail : s1.procSelfFdAvailable = true := hCfg1.procSelfFdAvailable
    have hs1Lim : min s1.fdLimit 2147483648 ≥ 1 + Int.ofNat s1.fds.length := by
      rw [hCfg1.fdLimit, hFds1]
      decide
    have hs1NoSec : oracleHasSeccomp s1.oracle = false := by
      rw [hs1Or]
      decide
    have hs1Avail : s1.procSelfFdAvailable = true := hCfg1.procSelfFdAvailable
    have hs1Lim : min s1.fdLimit 2147483648 ≥ 1 + Int.ofNat s1.fds.length := by
      rw [hCfg1.fdLimit, hFds1]
      decide
    have hLow1 := findLowestFreeFd_zero_some_of_lt s1 hs1Lim
    obtain ⟨dirfd, hLow⟩ := hLow1
    have hSpec := findLowestFreeFd_spec s1 0 dirfd hLow
    rcases hSpec with ⟨h0Le, _, _, _, _, hGetNone⟩
    have hMkVal : (mkI32 dirfd).val = dirfd := mkI32_val (z := dirfd) (by omega) (by omega)
    have hProcMono : OkPost (postfork.fd_ops.close_via_proc_self_fd s1 7#i32 keepHigh) fun p =>
        p.1 = .Ok () ∧ CloseAbove2Post s1 7#i32 keepHigh.val p.2 := by
      unfold postfork.fd_ops.close_via_proc_self_fd
      rw [sys_open_proc_self_fd_ok_spec s1 hs1Run hs1Cur hs1Avail dirfd hLow, bind_ok]
      let d0 := freshDescId s1
      let eDir : FdEntry := { desc := d0, cloexec := true, extraFdFlags := 0#i32 }
      let s1a : sys.Sys :=
        { (s1.putDesc d0 (.procSelfFd (-2))).putSlot dirfd eDir with
          trace := ((s1.putDesc d0 (.procSelfFd (-2))).putSlot dirfd eDir).trace ++
            [⟨Req.openProcSelfFd, .okVal (mkI32 dirfd).val⟩] }
      have hs1aTr : s1a.trace.length = 2 := by simp [s1a, ChildState.putDesc, ChildState.putSlot, hs1Tr]
      have hs1aOr : s1a.oracle = sHighProc.oracle := by simp [s1a, ChildState.putDesc, ChildState.putSlot, hs1Or]
      have hs1aRun : s1a.status = .running := hCfg1.status
      have hs1aDir : s1a.getFd (mkI32 dirfd).val = some eDir := by
        rw [hMkVal]; exact getFd_putSlot_self (s1.putDesc d0 (.procSelfFd (-2))) dirfd eDir
      have hs1aDesc : s1a.getDesc eDir.desc = .procSelfFd (-2) := by
        change ((s1.putDesc d0 (.procSelfFd (-2))).putSlot dirfd eDir).getDesc d0 = .procSelfFd (-2)
        exact getDesc_putDesc_self s1 d0 (.procSelfFd (-2))
      have hStepEintr : postfork.fd_ops.close_via_proc_self_fd_loop s1a 7#i32 keepHigh (mkI32 dirfd) =
          postfork.fd_ops.close_via_proc_self_fd_loop
            { s1a with trace := s1a.trace ++ [⟨Req.getdents64 (mkI32 dirfd), .err EINTR⟩] }
            7#i32 keepHigh (mkI32 dirfd) := by
        rw [postfork.fd_ops.close_via_proc_self_fd_loop, loop.eq_def]
        rw [close_proc_body_rw]
        have hF2 : currentFault s1a = .fail EINTR := by
          unfold currentFault; rw [hs1aTr, hs1aOr]; rfl
        have hSanEintr : sanitizeErrno EINTR = EINTR := by unfold sanitizeErrno EINTR; decide
        have hNotNe : ¬ ((sanitizeErrno EINTR != postfork.fd_ops.EINTR) = true) := by
          rw [hSanEintr, fd_ops_eintr_eq_loc]; decide
        rw [sys_getdents64_proc_fail s1a hs1aRun (mkI32 dirfd) eDir hs1aDir (-2) hs1aDesc EINTR hF2,
          proc_step_bind_ok, procLoopCont_err_eq _ _ _ _ _ _ hNotNe, hSanEintr, bind_ok]
        rfl
      let s1b : sys.Sys := { s1a with trace := s1a.trace ++ [⟨Req.getdents64 (mkI32 dirfd), .err EINTR⟩] }
      have hs1bOr : OracleNoCloseFault s1b s1b.trace.length := by
        intro k hk
        have hk3 : 3 ≤ k := by simpa [s1b, hs1aTr] using hk
        have hOrB : s1b.oracle = sHighProc.oracle := hs1aOr
        rw [hOrB]
        rcases k with _ | _ | _ | k
        · omega
        · omega
        · omega
        · rcases k with _ | _ | _ | k <;> simp [sHighProc]
      refine okPost_bind
        (by
          rw [hStepEintr]
          exact close_via_proc_self_fd_loop_spec s1b 7#i32 keepHigh (mkI32 dirfd) eDir
            hs1aRun hs1bOr hs1aDir (-2) (by decide) hs1aDesc)
        fun pLoop hpLoop => ?_
      rcases pLoop with ⟨s2, err, failed⟩
      rcases hpLoop with ⟨hFailed, hCfg2, hRun2, _, _, _, _, hOr2, hTr2, _, hFds2⟩
      dsimp only at hFailed hCfg2 hRun2 hOr2 hTr2
      rcases sys_close_running_exact s2 hRun2 (mkI32 dirfd) with
        ⟨rCl, s3, hEqCl, hCfg3, _, _, _, _, _, _, hFdsCl, _, hClIfOk⟩
      have hS2DirOpen : s2.isOpen (mkI32 dirfd).val = true := by
        have hStep := hFds2 (mkI32 dirfd).val (by omega) (by omega)
        rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inr (Or.inl rfl)))] at hStep
        simp [ChildState.isOpen, hStep, show s1b.getFd (mkI32 dirfd).val = some eDir from hs1aDir]
      have hAt2 : match (s2.oracle[s2.trace.length]?).getD .normal with
          | .fail _ => False | .seccomp _ => False | _ => True := by
        rw [hOr2]; exact hs1bOr s2.trace.length hTr2
      have hNoSecFail2 : ∀ rawE, currentFault s2 ≠ .seccomp rawE ∧ currentFault s2 ≠ .fail rawE := by
        intro rawE
        constructor
        · intro hF; unfold currentFault at hF; rw [hF] at hAt2; cases hAt2
        · intro hF; unfold currentFault at hF; rw [hF] at hAt2; cases hAt2
      have hrClOk : rCl = .Ok () := hClIfOk hNoSecFail2 hS2DirOpen
      have hGetCl : ∀ k : Int, s3.getFd k = if k == (mkI32 dirfd).val then none else s2.getFd k := by
        intro k
        cases hf : currentFault s2 with
        | seccomp rawE => exact absurd hf (hNoSecFail2 rawE).1
        | fail rawE => exact absurd hf (hNoSecFail2 rawE).2
        | normal | partialWrite _ | dentsBatch _ =>
          simp only [hf] at hFdsCl
          rw [show s3.getFd k = (s2.closeSlot (mkI32 dirfd).val).getFd k from by simp [ChildState.getFd, hFdsCl]]
          by_cases hkf : k == (mkI32 dirfd).val
          · rw [beq_iff_eq.mp hkf]; simp [getFd_closeSlot_self]
          · simp [hkf, getFd_closeSlot_ne s2 (fun h => hkf (beq_iff_eq.mpr h))]
      change OkPost (do
        let pCl ← sys.close s2 (mkI32 dirfd)
        let p4 ←
          match pCl.1 with
          | core.result.Result.Ok _ => ok (pCl.2, err, failed)
          | core.result.Result.Err ce => do
            let ib ← if failed then ok (err, failed) else ok (ce, true)
            ok (pCl.2, ib.1, ib.2)
        if p4.2.2 then ok (core.result.Result.Err p4.2.1, p4.1) else ok (core.result.Result.Ok (), p4.1)) _
      rw [hEqCl, bind_ok, hrClOk, hFailed]
      simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
      have hGetSlotNe : ∀ fd, fd ≠ dirfd → s1b.getFd fd = s1.getFd fd := fun fd hne =>
        getFd_putSlot_ne (s1.putDesc d0 (.procSelfFd (-2))) hne eDir
      apply okPost_ok
      refine ⟨rfl, ?_, ?_⟩
      · intro fd h0 h2
        rw [hGetCl fd, hMkVal]
        by_cases hEqDir : fd = dirfd
        · subst hEqDir; simp [hGetNone]
        · simp only [beq_false_of_ne hEqDir, Bool.false_eq_true, ↓reduceIte]
          have hStep := hFds2 fd h0 (by omega)
          rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inl h2))] at hStep
          rw [hStep, hGetSlotNe fd hEqDir]
      · intro fd h3 hMax
        by_cases hEqDir : fd = dirfd
        · subst hEqDir; split <;> [simp [hGetCl, hMkVal, hGetNone]; simp [hGetCl, hMkVal]]
        · have hStep := hFds2 fd (by omega) hMax
          by_cases hKept : Model.isKeptAbove2 7#i32 keepHigh.val fd = true
          · rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inr (Or.inr hKept)))] at hStep
            rw [ite_eq_left_of_eq_true _ _ (eq_true hKept), hGetCl fd, hMkVal, beq_false_of_ne hEqDir]
            simp only [Bool.false_eq_true, ↓reduceIte]; rw [hStep, hGetSlotNe fd hEqDir]
          · have hCond : ¬ (fd ≤ 2 ∨ fd = (mkI32 dirfd).val ∨ Model.isKeptAbove2 7#i32 keepHigh.val fd = true) := by
              rw [hMkVal]; simp [show ¬ fd ≤ 2 by omega, hEqDir, hKept]
            rw [ite_eq_right_of_eq_false _ _ (eq_false hCond)] at hStep
            rw [ite_eq_right_of_eq_false _ _ (eq_false hKept), hGetCl fd, hMkVal, beq_false_of_ne hEqDir]
            simp only [Bool.false_eq_true, ↓reduceIte]; exact hStep
    refine okPost_mono hProcMono fun ⟨r2, s2⟩ hs2 => ?_
    rcases hs2 with ⟨hr2, hClose2⟩
    have hGet1 : ∀ fd, s1.getFd fd = sHighProc.getFd fd := fun fd => by simp [ChildState.getFd, hFds1]
    have hk7 : Model.isKeptAbove2 7#i32 keepHigh.val 7 = true := by decide
    have hk42 : Model.isKeptAbove2 7#i32 keepHigh.val 42 = true := by decide
    have hk500 : Model.isKeptAbove2 7#i32 keepHigh.val 500 = false := by decide
    have hk70000 : Model.isKeptAbove2 7#i32 keepHigh.val 70000 = false := by decide
    have h0 : s2.isOpen 0 = true := by
      simp [ChildState.isOpen, hClose2.1 0 (by decide) (by decide), hGet1 0]; decide
    have h1 : s2.isOpen 1 = true := by
      simp [ChildState.isOpen, hClose2.1 1 (by decide) (by decide), hGet1 1]; decide
    have h2 : s2.isOpen 2 = true := by
      simp [ChildState.isOpen, hClose2.1 2 (by decide) (by decide), hGet1 2]; decide
    have h7 : s2.isOpen 7 = true := by
      have hc := hClose2.2 7 (by decide) (by decide)
      rw [ite_eq_left_of_eq_true _ _ (eq_true hk7)] at hc
      simp [ChildState.isOpen, hc, hGet1 7]; decide
    have h42 : s2.isOpen 42 = true := by
      have hc := hClose2.2 42 (by decide) (by decide)
      rw [ite_eq_left_of_eq_true _ _ (eq_true hk42)] at hc
      simp [ChildState.isOpen, hc, hGet1 42]; decide
    have h500 : s2.isOpen 500 = false := by
      have hc := hClose2.2 500 (by decide) (by decide)
      rw [ite_eq_right_of_eq_false _ _ (by simp [hk500])] at hc
      simp [ChildState.isOpen, hc]
    have h70000 : s2.isOpen 70000 = false := by
      have hc := hClose2.2 70000 (by decide) (by decide)
      rw [ite_eq_right_of_eq_false _ _ (by simp [hk70000])] at hc
      simp [ChildState.isOpen, hc]
    exact ⟨hr2, h0, h1, h2, h7, h42, h500, h70000⟩
  refine ⟨hHigh, ?_⟩
  let sNoProc : ChildState :=
    { closeRangeSupported := false
      closeRangeErrno := EPERM
      procSelfFdAvailable := false
      procOpenErrno := ENOENT
      fds := [(0, { desc := 1, cloexec := false }), (500, { desc := 2, cloexec := false })] }
  have hNoProc : OkPost
      (postfork.fd_ops.close_fds_above2_except sNoProc (-1)#i32 (mkSliceI32 0#usize []))
      fun p => p.1 = .Err ENOENT := by
    unfold postfork.fd_ops.close_fds_above2_except
    refine okPost_bind
      (try_close_range_except_err_spec sNoProc rfl rfl (-1)#i32 (mkSliceI32 0#usize []))
      fun ⟨r1, s1⟩ hs1 => ?_
    rcases hs1 with ⟨hr1, hCfg1, _, _, _, _, _, hFds1, _⟩
    dsimp only at hr1 hCfg1 hFds1
    rcases hr1 with ⟨errCr, hr1Eq, _⟩
    rw [hr1Eq]
    have hs1Run : s1.status = .running := hCfg1.status
    have hs1NoSec : oracleHasSeccomp s1.oracle = false := by
      rw [hCfg1.oracle]; rfl
    have hs1NotAvail : s1.procSelfFdAvailable = false := hCfg1.procSelfFdAvailable
    have hs1Lim : min s1.fdLimit 2147483648 ≥ 1 + Int.ofNat s1.fds.length := by
      rw [hCfg1.fdLimit, hFds1]
      decide
    refine okPost_mono
      (close_via_proc_self_fd_err_spec s1 (-1)#i32 (mkSliceI32 0#usize []) hs1Run hs1NoSec hs1NotAvail hs1Lim)
      fun ⟨r2, s2⟩ hs2 => ?_
    rcases hs2 with ⟨hr2, _⟩
    have hSan : sanitizeErrno s1.procOpenErrno = ENOENT := by
      rw [hCfg1.procOpenErrno]
      decide
    rw [hSan] at hr2
    exact hr2
  refine ⟨hNoProc, ?_⟩
  rintro ⟨hRun, hOr⟩ hCap
  refine ⟨okPost_mono (close_fds_above2_except_spec s extraKeep keepFds hRun hOr (Or.elim hCap Or.inl
    (fun h => Or.inr ⟨h.1, by omega⟩))) fun p hp => ⟨hp.1, hp.2.2.2.2.2.2.2.2.2⟩, trivial⟩

/-- Reachability witness for `test_postfork_closeFdsAbove2Except_closeRangeAndProcFallback` (`Core.CanReach`). -/
theorem test_postfork_closeFdsAbove2Except_closeRangeAndProcFallback_canReach :
    Core.CanReach
      (test_postfork_closeFdsAbove2Except_closeRangeAndProcFallback rustAeneasApi) := by
  have hAll := test_postfork_closeFdsAbove2Except_closeRangeAndProcFallback_allPass
    {} (-1)#i32 (mkSliceI32 0#usize [])
  dsimp only [Core.AllPass, test_postfork_closeFdsAbove2Except_closeRangeAndProcFallback] at hAll
  dsimp only [Core.CanReach, test_postfork_closeFdsAbove2Except_closeRangeAndProcFallback]
  rcases hAll with ⟨hTot, hHigh, hNoProc, hImp⟩
  exact ⟨{}, (-1)#i32, mkSliceI32 0#usize [], hTot, hHigh, hNoProc, ⟨rfl, rfl⟩, Or.inl rfl,
    hImp ⟨rfl, rfl⟩ (Or.inl rfl)⟩

/-- Specification of `close_fds_above2_except` error return when both `close_range` and `/proc/self/fd` are unavailable. -/
theorem close_fds_above2_except_err_spec (s : sys.Sys) (extra_keep_fd : I32) (keep_fds : Slice I32)
    (hRun : s.status = .running)
    (hNoSec : oracleHasSeccomp s.oracle = false)
    (hCr : s.closeRangeSupported = false)
    (hProc : s.procSelfFdAvailable = false)
    (hLim : min s.fdLimit 2147483648 ≥ 1 + Int.ofNat s.fds.length) :
    OkPost (postfork.fd_ops.close_fds_above2_except s extra_keep_fd keep_fds) fun p =>
      p.1 = .Err (sanitizeErrno s.procOpenErrno) ∧
      SameChildConfig p.2 s ∧
      p.2.status = .running ∧
      p.2.pgid = s.pgid ∧
      p.2.cwd = s.cwd ∧
      p.2.sig = s.sig ∧
      p.2.descs = s.descs ∧
      p.2.writeLog = s.writeLog ∧
      p.2.fds = s.fds := by
  unfold postfork.fd_ops.close_fds_above2_except
  refine okPost_bind
    (try_close_range_except_err_spec s hRun hCr extra_keep_fd keep_fds)
    fun ⟨r1, s1⟩ hs1 => ?_
  rcases hs1 with ⟨hr1, hCfg1, hPgid1, hCwd1, hSig1, hWl1, hDescs1, hFds1, _⟩
  dsimp only at hr1 hCfg1 hPgid1 hCwd1 hSig1 hWl1 hDescs1 hFds1
  rcases hr1 with ⟨errCr, hr1Eq, _⟩
  rw [hr1Eq]
  have hs1Run : s1.status = .running := hCfg1.status.trans hRun
  have hs1NoSec : oracleHasSeccomp s1.oracle = false := by rw [hCfg1.oracle]; exact hNoSec
  have hs1NotAvail : s1.procSelfFdAvailable = false := hCfg1.procSelfFdAvailable.trans hProc
  have hs1Lim : min s1.fdLimit 2147483648 ≥ 1 + Int.ofNat s1.fds.length := by
    rw [hCfg1.fdLimit, hFds1]; exact hLim
  refine okPost_mono
    (close_via_proc_self_fd_err_spec s1 extra_keep_fd keep_fds hs1Run hs1NoSec hs1NotAvail hs1Lim)
    fun ⟨r2, s2⟩ hs2 => ?_
  rcases hs2 with ⟨hr2, hCfg2, hRun2, hPgid2, hCwd2, hSig2, hDescs2, hWl2, hFds2⟩
  refine ⟨?_, hCfg2.trans hCfg1, hRun2, hPgid2.trans hPgid1, hCwd2.trans hCwd1,
    hSig2.trans hSig1, hDescs2.trans hDescs1, hWl2.trans hWl1, hFds2.trans hFds1⟩
  rw [hr2, hCfg1.procOpenErrno]

private theorem findLowestFreeFdAux_eq_of_fds_eq (s1 s2 : sys.Sys) (hFds : s1.fds = s2.fds)
    (n : Nat) (cur : Int) :
    findLowestFreeFdAux s1 cur n = findLowestFreeFdAux s2 cur n := by
  induction n generalizing cur with
  | zero => rfl
  | succ k ih =>
    unfold findLowestFreeFdAux
    have hOpen : s1.isOpen cur = s2.isOpen cur := by simp [ChildState.isOpen, ChildState.getFd, hFds]
    rw [hOpen]
    split
    · exact ih (cur + 1)
    · rfl

private theorem findLowestFreeFd_eq_of_fds_lim_eq {s1 s2 : sys.Sys}
    (hFds : s1.fds = s2.fds) (hLim : s1.fdLimit = s2.fdLimit) (minFd : Int) :
    findLowestFreeFd s1 minFd = findLowestFreeFd s2 minFd := by
  unfold findLowestFreeFd
  rw [hLim]
  dsimp only
  split
  · rfl
  · exact findLowestFreeFdAux_eq_of_fds_eq s1 s2 hFds _ minFd

/-- Specification of `close_fds_above2_except` using an explicit free-FD witness. -/
theorem close_fds_above2_except_spec_of_free (s : sys.Sys) (extra_keep_fd : I32)
    (keep_fds : Slice I32)
    (hRun : s.status = .running)
    (hOr : s.oracle = [])
    (hCap : s.closeRangeSupported = true ∨
      (s.procSelfFdAvailable = true ∧ ∃ dirfd, findLowestFreeFd s 0 = some dirfd)) :
    OkPost (postfork.fd_ops.close_fds_above2_except s extra_keep_fd keep_fds) fun p =>
      p.1 = .Ok () ∧
      SameChildConfig p.2 s ∧
      p.2.status = .running ∧
      p.2.pgid = s.pgid ∧
      p.2.cwd = s.cwd ∧
      p.2.sig = s.sig ∧
      p.2.writeLog = s.writeLog ∧
      p.2.oracle = s.oracle ∧
      (∀ fd e, s.getFd fd = some e → p.2.getDesc e.desc = s.getDesc e.desc) ∧
      CloseAbove2Post s extra_keep_fd keep_fds.val p.2 := by
  unfold postfork.fd_ops.close_fds_above2_except
  by_cases hCr : s.closeRangeSupported = true
  · refine okPost_bind
      (try_close_range_except_spec s hRun hOr hCr extra_keep_fd keep_fds)
      fun ⟨r, s1⟩ hs1 => ?_
    rcases hs1 with ⟨hr, hCfg1, hPgid1, hCwd1, hSig1, hDescs1, hWl1, hClose1⟩
    dsimp only at hr hCfg1 hPgid1 hCwd1 hSig1 hDescs1 hWl1 hClose1
    rw [hr]
    exact okPost_ok _ _ ⟨rfl, hCfg1, hCfg1.status.trans hRun, hPgid1, hCwd1, hSig1, hWl1,
      hCfg1.oracle, fun fd e _ => by simp [ChildState.getDesc, hDescs1], hClose1⟩
  · have hCrF : s.closeRangeSupported = false := Bool.eq_false_iff.mpr hCr
    have hProc : s.procSelfFdAvailable = true ∧ ∃ dirfd, findLowestFreeFd s 0 = some dirfd := by
      rcases hCap with h | h
      · exact absurd h hCr
      · exact h
    refine okPost_bind
      (try_close_range_except_err_spec s hRun hCrF extra_keep_fd keep_fds)
      fun ⟨r, s1⟩ hs1 => ?_
    rcases hs1 with ⟨hr, hCfg1, hPgid1, hCwd1, hSig1, hWl1, hDescs1, hFds1, _⟩
    dsimp only at hr hCfg1 hPgid1 hCwd1 hSig1 hWl1 hDescs1 hFds1
    rcases hr with ⟨errCr, hrEq, _⟩
    rw [hrEq]
    have hs1Run : s1.status = .running := hCfg1.status.trans hRun
    have hs1Or : s1.oracle = [] := hCfg1.oracle.trans hOr
    have hs1Cur : currentFault s1 = .normal := by unfold currentFault; simp [hs1Or]
    have hs1Avail : s1.procSelfFdAvailable = true := hCfg1.procSelfFdAvailable.trans hProc.1
    have hs1Free : ∃ dirfd, findLowestFreeFd s1 0 = some dirfd := by
      rw [findLowestFreeFd_eq_of_fds_lim_eq hFds1 hCfg1.fdLimit]; exact hProc.2
    have hs1NoSec : oracleHasSeccomp s1.oracle = false := by simp [hs1Or, oracleHasSeccomp]
    have hs1NoClose : OracleNoCloseFault s1 (s1.trace.length + 1) := by
      intro k _
      simp [hs1Or]
    refine okPost_mono
      (close_via_proc_self_fd_spec_of_free s1 extra_keep_fd keep_fds hs1Run hs1Cur hs1Avail hs1Free hs1NoSec hs1NoClose)
      fun ⟨r2, s2⟩ hs2 => ?_
    rcases hs2 with ⟨hr2, hCfg2, hRun2, hPgid2, hCwd2, hSig2, hWl2, hOr2, _, hDescFd2, hClose2⟩
    have hGet1 : ∀ fd, s1.getFd fd = s.getFd fd := fun fd => by simp [ChildState.getFd, hFds1]
    have hClose' : CloseAbove2Post s extra_keep_fd keep_fds.val s2 := by
      refine ⟨fun fd h0 h2 => ?_, fun fd h3 hMax => ?_⟩
      · rw [hClose2.1 fd h0 h2, hGet1 fd]
      · have h2 := hClose2.2 fd h3 hMax
        split at h2
        · next hk => rw [ite_eq_left_of_eq_true _ _ (eq_true hk), h2, hGet1 fd]
        · next hk => rw [ite_eq_right_of_eq_false _ _ (eq_false hk), h2]
    refine ⟨hr2, hCfg2.trans hCfg1, hRun2, hPgid2.trans hPgid1, hCwd2.trans hCwd1,
      hSig2.trans hSig1, hWl2.trans hWl1, hOr2.trans hCfg1.oracle, ?_, hClose'⟩
    intro fd e hFd
    have hFd1 : s1.getFd fd = some e := by rw [hGet1 fd]; exact hFd
    rw [hDescFd2 fd e hFd1]
    simp [ChildState.getDesc, hDescs1]

/-- Specification of `close_fds_above2_except` error return using an explicit free-FD witness. -/
theorem close_fds_above2_except_err_spec_of_free (s : sys.Sys) (extra_keep_fd : I32)
    (keep_fds : Slice I32)
    (hRun : s.status = .running)
    (hNoSec : oracleHasSeccomp s.oracle = false)
    (hCr : s.closeRangeSupported = false)
    (hProc : s.procSelfFdAvailable = false)
    (hFree : ∃ dirfd, findLowestFreeFd s 0 = some dirfd) :
    OkPost (postfork.fd_ops.close_fds_above2_except s extra_keep_fd keep_fds) fun p =>
      p.1 = .Err (sanitizeErrno s.procOpenErrno) ∧
      SameChildConfig p.2 s ∧
      p.2.status = .running ∧
      p.2.pgid = s.pgid ∧
      p.2.cwd = s.cwd ∧
      p.2.sig = s.sig ∧
      p.2.descs = s.descs ∧
      p.2.writeLog = s.writeLog ∧
      p.2.fds = s.fds := by
  unfold postfork.fd_ops.close_fds_above2_except
  refine okPost_bind
    (try_close_range_except_err_spec s hRun hCr extra_keep_fd keep_fds)
    fun ⟨r1, s1⟩ hs1 => ?_
  rcases hs1 with ⟨hr1, hCfg1, hPgid1, hCwd1, hSig1, hWl1, hDescs1, hFds1, _⟩
  dsimp only at hr1 hCfg1 hPgid1 hCwd1 hSig1 hWl1 hDescs1 hFds1
  rcases hr1 with ⟨errCr, hr1Eq, _⟩
  rw [hr1Eq]
  have hs1Run : s1.status = .running := hCfg1.status.trans hRun
  have hs1NoSec : oracleHasSeccomp s1.oracle = false := by rw [hCfg1.oracle]; exact hNoSec
  have hs1NotAvail : s1.procSelfFdAvailable = false := hCfg1.procSelfFdAvailable.trans hProc
  have hs1Free : ∃ dirfd, findLowestFreeFd s1 0 = some dirfd := by
    rw [findLowestFreeFd_eq_of_fds_lim_eq hFds1 hCfg1.fdLimit]; exact hFree
  refine okPost_mono
    (close_via_proc_self_fd_err_spec_of_free s1 extra_keep_fd keep_fds hs1Run hs1NoSec hs1NotAvail hs1Free)
    fun ⟨r2, s2⟩ hs2 => ?_
  rcases hs2 with ⟨hr2, hCfg2, hRun2, hPgid2, hCwd2, hSig2, hDescs2, hWl2, hFds2⟩
  refine ⟨?_, hCfg2.trans hCfg1, hRun2, hPgid2.trans hPgid1, hCwd2.trans hCwd1,
    hSig2.trans hSig1, hDescs2.trans hDescs1, hWl2.trans hWl1, hFds2.trans hFds1⟩
  rw [hr2, hCfg1.procOpenErrno]

end LeanSwe.PostFork.Proofs
