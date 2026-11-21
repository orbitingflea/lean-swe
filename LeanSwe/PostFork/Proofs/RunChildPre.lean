import LeanSwe.PostFork.Proofs.ChildCommon

/-!
# Unified `run_child` Pre-Sync & Validation Proofs

Proves exact specifications for `validate_flags`, `validate_signs`,
`validate_sync_overlaps`, `validate_stdio_overlaps`, `validate_child_args`,
`apply_set_pgid`, `apply_reset_sigpipe`, `probe_sync_fd`, `probe_redir_stdio`,
`await_sync_barrier`, and `run_child_pre_sync`.
-/

namespace LeanSwe.PostFork.Proofs

open _root_.Aeneas _root_.Aeneas.Std Result
open LeanSwe.PostFork
open LeanSwe.PostFork.World
open LeanSwe.PostFork.Aeneas
open LeanSwe.PostFork.Aeneas.Model

section FlagsAndValidation

private theorem all_flags_not_eq : (~~~ postfork.child.ALL_FLAGS) = 4294967232#u32 := by
  unfold postfork.child.ALL_FLAGS
  decide

private theorem flag_set_pgid_eq : postfork.child.FLAG_SET_PGID = FLAG_SET_PGID := by
  unfold postfork.child.FLAG_SET_PGID FLAG_SET_PGID; rfl

private theorem flag_reset_sigpipe_eq : postfork.child.FLAG_RESET_SIGPIPE = FLAG_RESET_SIGPIPE := by
  unfold postfork.child.FLAG_RESET_SIGPIPE FLAG_RESET_SIGPIPE; rfl

private theorem flag_has_sync_barrier_eq :
    postfork.child.FLAG_HAS_SYNC_BARRIER = FLAG_HAS_SYNC_BARRIER := by
  unfold postfork.child.FLAG_HAS_SYNC_BARRIER FLAG_HAS_SYNC_BARRIER; rfl

private theorem flag_redirect_stdio_eq : postfork.child.FLAG_REDIRECT_STDIO = FLAG_REDIRECT_STDIO := by
  unfold postfork.child.FLAG_REDIRECT_STDIO FLAG_REDIRECT_STDIO; rfl

private theorem flag_close_unkept_eq :
    postfork.child.FLAG_CLOSE_UNKEPT_ABOVE2 = FLAG_CLOSE_UNKEPT_ABOVE2 := by
  unfold postfork.child.FLAG_CLOSE_UNKEPT_ABOVE2 FLAG_CLOSE_UNKEPT_ABOVE2; rfl

private theorem flag_close_stdio_eq :
    postfork.child.FLAG_CLOSE_STDIO_SOURCES = FLAG_CLOSE_STDIO_SOURCES := by
  unfold postfork.child.FLAG_CLOSE_STDIO_SOURCES FLAG_CLOSE_STDIO_SOURCES; rfl

/-- Exact specification of `postfork.child.validate_flags`. -/
theorem validate_flags_spec (flags : U32) :
    OkPost (postfork.child.validate_flags flags) fun r =>
      r = if validFlagsSpec flags then .Ok () else .Err EINVAL := by
  unfold postfork.child.validate_flags OkPost
  simp only [all_flags_not_eq, flag_redirect_stdio_eq, flag_close_unkept_eq, flag_close_stdio_eq,
    fd_ops_einval_eq, lift, Aeneas.Std.lift, bind_ok]
  dsimp only [validFlagsSpec, flagSet]
  by_cases hBad : ((flags &&& 4294967232#u32) != 0#u32) = true
  · have hEq : ((flags &&& 4294967232#u32) == 0#u32) = false := by
      cases h : ((flags &&& 4294967232#u32) == 0#u32) <;> simp_all [bne_iff_ne]
    simp [hBad, hEq]
  · have hEq : ((flags &&& 4294967232#u32) == 0#u32) = true := by
      cases h : ((flags &&& 4294967232#u32) == 0#u32) <;> simp_all [bne_iff_ne]
    have hBadF : ((flags &&& 4294967232#u32) != 0#u32) = false := Bool.eq_false_iff.mpr hBad
    simp only [hBadF, hEq, Bool.false_eq_true, ↓reduceIte, Bool.true_and]
    cases (flags &&& FLAG_CLOSE_STDIO_SOURCES != 0#u32) <;>
      cases (flags &&& FLAG_REDIRECT_STDIO != 0#u32) <;>
      cases (flags &&& FLAG_CLOSE_UNKEPT_ABOVE2 != 0#u32) <;>
      simp

/-- Exact specification of `postfork.child.validate_signs`. -/
theorem validate_signs_spec (flags : U32) (syncR inFd outFd errFd : I32) :
    OkPost (postfork.child.validate_signs flags syncR inFd outFd errFd) fun r =>
      r = if validSignsSpec flags syncR inFd outFd errFd then .Ok () else .Err EBADF := by
  unfold postfork.child.validate_signs OkPost
  simp only [flag_has_sync_barrier_eq, flag_redirect_stdio_eq, fd_ops_ebadf_eq, lift,
    Aeneas.Std.lift, bind_ok]
  have hPos0 (x : I32) : decide (0#i32 ≤ x) = !decide (x < 0#i32) := by
    by_cases h : x < 0#i32
    · simp [h, show ¬ (0#i32 ≤ x) by scalar_tac]
    · simp [h, show 0#i32 ≤ x by scalar_tac]
  dsimp only [validSignsSpec, flagSet]
  simp only [hPos0]
  cases hSync : (flags &&& FLAG_HAS_SYNC_BARRIER != 0#u32) <;>
    cases hRedir : (flags &&& FLAG_REDIRECT_STDIO != 0#u32)
  · simp
  · by_cases hi : inFd < 0#i32
    · simp [hi]
    · simp only [hi, ↓reduceIte, Bool.not_false]
      by_cases ho : outFd < 0#i32
      · simp [ho]
      · simp only [ho, ↓reduceIte, decide_false, Bool.not_false, Bool.true_and]
        by_cases he : errFd < 0#i32 <;> simp [he]
  · simp only [↓reduceIte, Bool.not_true, Bool.false_or]
    by_cases hs : syncR < 0#i32
    · simp [hs]
    · simp [hs]
  · simp only [↓reduceIte, Bool.not_true, Bool.false_or]
    by_cases hs : syncR < 0#i32
    · simp [hs]
    · simp only [hs, ↓reduceIte]
      by_cases hi : inFd < 0#i32
      · simp [hi]
      · simp only [hi, ↓reduceIte]
        by_cases ho : outFd < 0#i32
        · simp [ho]
        · simp only [ho, ↓reduceIte, decide_false, Bool.not_false, Bool.true_and]
          by_cases he : errFd < 0#i32 <;> simp [he]

/-- Exact specification of `postfork.child.fd_in_stdio`. -/
theorem fd_in_stdio_spec (fd inFd outFd errFd : I32) :
    OkPost (postfork.child.fd_in_stdio fd inFd outFd errFd) fun b =>
      b = fdInStdioSpec fd inFd outFd errFd := by
  unfold postfork.child.fd_in_stdio fdInStdioSpec OkPost
  by_cases h1 : fd = inFd <;> by_cases h2 : fd = outFd <;> by_cases h3 : fd = errFd <;>
    simp [h1, h2, h3]

/-- Exact specification of `postfork.child.stdio_in_slice`. -/
theorem stdio_in_slice_spec (fds : Slice I32) (inFd outFd errFd : I32) :
    OkPost (postfork.child.stdio_in_slice fds inFd outFd errFd) fun b =>
      b = stdioInSliceSpec fds.val inFd outFd errFd := by
  unfold postfork.child.stdio_in_slice stdioInSliceSpec
  refine okPost_bind (slice_contains_nonneg_spec fds inFd) fun b1 hb1 => ?_
  subst hb1
  cases sliceContainsNonnegSpec fds.val inFd.val
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_or]
    refine okPost_bind (slice_contains_nonneg_spec fds outFd) fun b2 hb2 => ?_
    subst hb2
    cases sliceContainsNonnegSpec fds.val outFd.val
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      exact slice_contains_nonneg_spec fds errFd
    · exact okPost_ok _ _ rfl
  · exact okPost_ok _ _ rfl

private theorem validate_sync_overlaps_spec
    (flags : U32) (syncR repW : I32) (closeFds keepFds : Slice I32) :
    OkPost (postfork.child.validate_sync_overlaps flags syncR repW closeFds keepFds) fun r =>
      r =
        if !flagSet flags FLAG_HAS_SYNC_BARRIER ||
            (repW != syncR &&
              !sliceContainsNonnegSpec closeFds.val syncR.val &&
              !sliceContainsNonnegSpec keepFds.val syncR.val) then
          .Ok ()
        else
          .Err EINVAL := by
  unfold postfork.child.validate_sync_overlaps
  simp only [flag_has_sync_barrier_eq, fd_ops_einval_eq, lift, Aeneas.Std.lift, bind_ok]
  dsimp only [flagSet]
  by_cases hSync : (flags &&& FLAG_HAS_SYNC_BARRIER = 0#u32)
  · have hF : (flags &&& FLAG_HAS_SYNC_BARRIER != 0#u32) = false := by
      simpa [bne_iff_ne] using hSync
    simp only [hSync, ↓reduceIte]
    exact okPost_ok _ _ (by simp)
  · have hT : (flags &&& FLAG_HAS_SYNC_BARRIER != 0#u32) = true := by
      simpa [bne_iff_ne] using hSync
    simp only [hSync, ↓reduceIte, hT, Bool.not_true, Bool.false_or]
    by_cases hEq : syncR = repW
    · have hNe : (repW != syncR) = false := by simp [hEq]
      simp only [hEq, ↓reduceIte]
      exact okPost_ok _ _ (by simp)
    · have hNe : (repW != syncR) = true := bne_iff_ne.mpr (Ne.symm hEq)
      simp only [hEq, ↓reduceIte]
      refine okPost_bind (slice_contains_nonneg_spec closeFds syncR) fun b1 hb1 => ?_
      subst hb1
      cases sliceContainsNonnegSpec closeFds.val syncR.val
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine okPost_bind (slice_contains_nonneg_spec keepFds syncR) fun b2 hb2 => ?_
        subst hb2
        cases sliceContainsNonnegSpec keepFds.val syncR.val <;> exact okPost_ok _ _ (by simp [hNe])
      · simp only [↓reduceIte]
        exact okPost_ok _ _ (by simp)

private theorem validate_stdio_keep_sources_spec
    (inFd outFd errFd : I32) (keepFds : Slice I32) :
    OkPost
      (if inFd > 2#i32 then do
        let b3 ← postfork.fd_ops.slice_contains_nonneg keepFds inFd
        if b3 then ok (core.result.Result.Err postfork.fd_ops.EINVAL)
        else if outFd > 2#i32 then do
          let b4 ← postfork.fd_ops.slice_contains_nonneg keepFds outFd
          if b4 then ok (core.result.Result.Err postfork.fd_ops.EINVAL)
          else if errFd > 2#i32 then do
            let b5 ← postfork.fd_ops.slice_contains_nonneg keepFds errFd
            if b5 then ok (core.result.Result.Err postfork.fd_ops.EINVAL)
            else ok (core.result.Result.Ok ())
          else ok (core.result.Result.Ok ())
        else if errFd > 2#i32 then do
          let b4 ← postfork.fd_ops.slice_contains_nonneg keepFds errFd
          if b4 then ok (core.result.Result.Err postfork.fd_ops.EINVAL)
          else ok (core.result.Result.Ok ())
        else ok (core.result.Result.Ok ())
      else if outFd > 2#i32 then do
        let b3 ← postfork.fd_ops.slice_contains_nonneg keepFds outFd
        if b3 then ok (core.result.Result.Err postfork.fd_ops.EINVAL)
        else if errFd > 2#i32 then do
          let b4 ← postfork.fd_ops.slice_contains_nonneg keepFds errFd
          if b4 then ok (core.result.Result.Err postfork.fd_ops.EINVAL)
          else ok (core.result.Result.Ok ())
        else ok (core.result.Result.Ok ())
      else if errFd > 2#i32 then do
        let b3 ← postfork.fd_ops.slice_contains_nonneg keepFds errFd
        if b3 then ok (core.result.Result.Err postfork.fd_ops.EINVAL)
        else ok (core.result.Result.Ok ())
      else ok (core.result.Result.Ok ()))
      fun r =>
        r =
          if (!decide (inFd > 2#i32) || !sliceContainsNonnegSpec keepFds.val inFd.val) &&
             (!decide (outFd > 2#i32) || !sliceContainsNonnegSpec keepFds.val outFd.val) &&
             (!decide (errFd > 2#i32) || !sliceContainsNonnegSpec keepFds.val errFd.val) then
            .Ok ()
          else
            .Err EINVAL := by
  have hErrBranch :
      OkPost
        (if errFd > 2#i32 then do
          let b ← postfork.fd_ops.slice_contains_nonneg keepFds errFd
          if b then ok (core.result.Result.Err postfork.fd_ops.EINVAL)
          else ok (core.result.Result.Ok ())
        else ok (core.result.Result.Ok ()))
        fun r =>
          r = if !decide (errFd > 2#i32) || !sliceContainsNonnegSpec keepFds.val errFd.val then .Ok () else .Err EINVAL := by
    by_cases he : errFd > 2#i32
    · simp only [he, ↓reduceIte, decide_true, Bool.not_true, Bool.false_or]
      refine okPost_bind (slice_contains_nonneg_spec keepFds errFd) fun b hb => ?_
      subst hb
      cases sliceContainsNonnegSpec keepFds.val errFd.val <;>
        exact okPost_ok _ _ (by simp [fd_ops_einval_eq])
    · simp only [he, ↓reduceIte, decide_false, Bool.not_false, Bool.true_or]
      exact okPost_ok _ _ rfl
  have hOutErrBranch :
      OkPost
        (if outFd > 2#i32 then do
          let b4 ← postfork.fd_ops.slice_contains_nonneg keepFds outFd
          if b4 then ok (core.result.Result.Err postfork.fd_ops.EINVAL)
          else if errFd > 2#i32 then do
            let b5 ← postfork.fd_ops.slice_contains_nonneg keepFds errFd
            if b5 then ok (core.result.Result.Err postfork.fd_ops.EINVAL)
            else ok (core.result.Result.Ok ())
          else ok (core.result.Result.Ok ())
        else if errFd > 2#i32 then do
          let b4 ← postfork.fd_ops.slice_contains_nonneg keepFds errFd
          if b4 then ok (core.result.Result.Err postfork.fd_ops.EINVAL)
          else ok (core.result.Result.Ok ())
        else ok (core.result.Result.Ok ()))
        fun r =>
          r =
            if (!decide (outFd > 2#i32) || !sliceContainsNonnegSpec keepFds.val outFd.val) &&
               (!decide (errFd > 2#i32) || !sliceContainsNonnegSpec keepFds.val errFd.val) then
              .Ok ()
            else
              .Err EINVAL := by
    by_cases ho : outFd > 2#i32
    · simp only [ho, ↓reduceIte, decide_true, Bool.not_true, Bool.false_or]
      refine okPost_bind (slice_contains_nonneg_spec keepFds outFd) fun b hb => ?_
      subst hb
      cases sliceContainsNonnegSpec keepFds.val outFd.val
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
        exact hErrBranch
      · simp only [↓reduceIte, Bool.not_true, Bool.false_and, Bool.false_eq_true, fd_ops_einval_eq]
        exact okPost_ok _ _ rfl
    · simp only [ho, ↓reduceIte, decide_false, Bool.not_false, Bool.true_or, Bool.true_and]
      exact hErrBranch
  by_cases hi : inFd > 2#i32
  · simp only [hi, ↓reduceIte, decide_true, Bool.not_true, Bool.false_or]
    refine okPost_bind (slice_contains_nonneg_spec keepFds inFd) fun b hb => ?_
    subst hb
    cases sliceContainsNonnegSpec keepFds.val inFd.val
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
      exact hOutErrBranch
    · simp only [↓reduceIte, Bool.not_true, Bool.false_and, Bool.false_eq_true, fd_ops_einval_eq]
      exact okPost_ok _ _ rfl
  · simp only [hi, ↓reduceIte, decide_false, Bool.not_false, Bool.true_or, Bool.true_and]
    exact hOutErrBranch

private theorem validate_stdio_overlaps_spec
    (flags : U32) (syncR inFd outFd errFd repW : I32) (closeFds keepFds : Slice I32) :
    OkPost
      (postfork.child.validate_stdio_overlaps flags syncR inFd outFd errFd repW closeFds keepFds)
      fun r =>
        r =
          if !flagSet flags FLAG_REDIRECT_STDIO ||
              (!sliceHasStdioSlotSpec keepFds.val &&
                !fdInStdioSpec repW inFd outFd errFd &&
                !stdioInSliceSpec closeFds.val inFd outFd errFd &&
                (!flagSet flags FLAG_HAS_SYNC_BARRIER || !fdInStdioSpec syncR inFd outFd errFd) &&
                (!flagSet flags FLAG_CLOSE_STDIO_SOURCES ||
                  ((!decide (inFd > 2#i32) || !sliceContainsNonnegSpec keepFds.val inFd.val) &&
                   (!decide (outFd > 2#i32) || !sliceContainsNonnegSpec keepFds.val outFd.val) &&
                   (!decide (errFd > 2#i32) || !sliceContainsNonnegSpec keepFds.val errFd.val)))) then
            .Ok ()
          else
            .Err EINVAL := by
  unfold postfork.child.validate_stdio_overlaps
  simp only [flag_redirect_stdio_eq, flag_has_sync_barrier_eq, flag_close_stdio_eq, fd_ops_einval_eq,
    lift, Aeneas.Std.lift, bind_ok]
  dsimp only [flagSet]
  by_cases hRedir : (flags &&& FLAG_REDIRECT_STDIO = 0#u32)
  · have hF : (flags &&& FLAG_REDIRECT_STDIO != 0#u32) = false := by
      simpa [bne_iff_ne] using hRedir
    simp only [hRedir, ↓reduceIte]
    exact okPost_ok _ _ (by simp)
  · have hT : (flags &&& FLAG_REDIRECT_STDIO != 0#u32) = true := by
      simpa [bne_iff_ne] using hRedir
    simp only [hRedir, ↓reduceIte, hT, Bool.not_true, Bool.false_or]
    refine okPost_bind (slice_has_stdio_slot_spec keepFds) fun b0 hb0 => ?_
    subst hb0
    cases sliceHasStdioSlotSpec keepFds.val
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
      refine okPost_bind (fd_in_stdio_spec repW inFd outFd errFd) fun b1 hb1 => ?_
      subst hb1
      cases fdInStdioSpec repW inFd outFd errFd
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
        refine okPost_bind (stdio_in_slice_spec closeFds inFd outFd errFd) fun b2 hb2 => ?_
        subst hb2
        cases stdioInSliceSpec closeFds.val inFd outFd errFd
        · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
          have hCloseSrc :
              OkPost
                (if (flags &&& FLAG_CLOSE_STDIO_SOURCES != 0#u32) = true then
                  if inFd > 2#i32 then do
                    let b4 ← postfork.fd_ops.slice_contains_nonneg keepFds inFd
                    if b4 then ok (core.result.Result.Err EINVAL)
                    else if outFd > 2#i32 then do
                      let b5 ← postfork.fd_ops.slice_contains_nonneg keepFds outFd
                      if b5 then ok (core.result.Result.Err EINVAL)
                      else if errFd > 2#i32 then do
                        let b6 ← postfork.fd_ops.slice_contains_nonneg keepFds errFd
                        if b6 then ok (core.result.Result.Err EINVAL)
                        else ok (core.result.Result.Ok ())
                      else ok (core.result.Result.Ok ())
                    else if errFd > 2#i32 then do
                      let b5 ← postfork.fd_ops.slice_contains_nonneg keepFds errFd
                      if b5 then ok (core.result.Result.Err EINVAL)
                      else ok (core.result.Result.Ok ())
                    else ok (core.result.Result.Ok ())
                  else if outFd > 2#i32 then do
                    let b4 ← postfork.fd_ops.slice_contains_nonneg keepFds outFd
                    if b4 then ok (core.result.Result.Err EINVAL)
                    else if errFd > 2#i32 then do
                      let b5 ← postfork.fd_ops.slice_contains_nonneg keepFds errFd
                      if b5 then ok (core.result.Result.Err EINVAL)
                      else ok (core.result.Result.Ok ())
                    else ok (core.result.Result.Ok ())
                  else if errFd > 2#i32 then do
                    let b4 ← postfork.fd_ops.slice_contains_nonneg keepFds errFd
                    if b4 then ok (core.result.Result.Err EINVAL)
                    else ok (core.result.Result.Ok ())
                  else ok (core.result.Result.Ok ())
                else ok (core.result.Result.Ok ()))
                fun r =>
                  r =
                    if !(flags &&& FLAG_CLOSE_STDIO_SOURCES != 0#u32) ||
                        ((!decide (inFd > 2#i32) || !sliceContainsNonnegSpec keepFds.val inFd.val) &&
                         (!decide (outFd > 2#i32) || !sliceContainsNonnegSpec keepFds.val outFd.val) &&
                         (!decide (errFd > 2#i32) || !sliceContainsNonnegSpec keepFds.val errFd.val)) then
                      .Ok ()
                    else
                      .Err EINVAL := by
            by_cases hCs : (flags &&& FLAG_CLOSE_STDIO_SOURCES != 0#u32) = true
            · simp only [hCs, ↓reduceIte, Bool.not_true, Bool.false_or]
              simpa [fd_ops_einval_eq] using validate_stdio_keep_sources_spec inFd outFd errFd keepFds
            · have hCsF : (flags &&& FLAG_CLOSE_STDIO_SOURCES != 0#u32) = false := Bool.eq_false_iff.mpr hCs
              simp only [hCsF, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_or]
              exact okPost_ok _ _ rfl
          by_cases hSy : (flags &&& FLAG_HAS_SYNC_BARRIER != 0#u32) = true
          · simp only [hSy, ↓reduceIte, Bool.not_true, Bool.false_or]
            refine okPost_bind (fd_in_stdio_spec syncR inFd outFd errFd) fun b3 hb3 => ?_
            subst hb3
            cases fdInStdioSpec syncR inFd outFd errFd
            · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
              exact hCloseSrc
            · simp only [↓reduceIte, Bool.not_true, Bool.false_and, Bool.false_eq_true]
              exact okPost_ok _ _ rfl
          · have hSyF : (flags &&& FLAG_HAS_SYNC_BARRIER != 0#u32) = false := Bool.eq_false_iff.mpr hSy
            simp only [hSyF, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_or, Bool.true_and]
            exact hCloseSrc
        · simp only [↓reduceIte, Bool.not_true, Bool.false_and, Bool.false_eq_true]
          exact okPost_ok _ _ rfl
      · simp only [↓reduceIte, Bool.not_true, Bool.false_and, Bool.false_eq_true]
        exact okPost_ok _ _ rfl
    · simp only [↓reduceIte, Bool.not_true, Bool.false_and, Bool.false_eq_true]
      exact okPost_ok _ _ rfl

/-- Exact specification of `postfork.child.validate_child_args` with precedence `validate_flags` (`EINVAL`) > `validate_signs` (`EBADF`) > `validRunChildNoOverlap` (`EINVAL`). -/
theorem validate_child_args_spec
    (flags : U32) (syncR inFd outFd errFd repW : I32) (closeFds keepFds : Slice I32) :
    OkPost (postfork.child.validate_child_args flags syncR inFd outFd errFd repW closeFds keepFds)
      fun r =>
        if !validFlagsSpec flags then r = .Err EINVAL
        else if !validSignsSpec flags syncR inFd outFd errFd then r = .Err EBADF
        else if !validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds.val keepFds.val then
          r = .Err EINVAL
        else r = .Ok () := by
  unfold postfork.child.validate_child_args
  dsimp only [validRunChildNoOverlap]
  refine okPost_bind (validate_flags_spec flags) fun r0 hr0 => ?_
  by_cases hFl : validFlagsSpec flags = true
  · simp only [hFl, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    rw [hr0]
    simp only [hFl, ↓reduceIte]
    refine okPost_bind (validate_signs_spec flags syncR inFd outFd errFd) fun r1 hr1 => ?_
    by_cases hSg : validSignsSpec flags syncR inFd outFd errFd = true
    · simp only [hSg, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
      rw [hr1]
      simp only [hSg, ↓reduceIte]
      refine okPost_bind (slice_contains_nonneg_spec closeFds repW) fun b0 hb0 => ?_
      subst hb0
      by_cases hC0 : sliceContainsNonnegSpec closeFds.val repW.val = true
      · simp [hC0, fd_ops_einval_eq]
        exact okPost_ok _ _ rfl
      · have hC0F : sliceContainsNonnegSpec closeFds.val repW.val = false := Bool.eq_false_iff.mpr hC0
        simp only [hC0F, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
        refine okPost_bind (slice_contains_nonneg_spec keepFds repW) fun b1 hb1 => ?_
        subst hb1
        by_cases hC1 : sliceContainsNonnegSpec keepFds.val repW.val = true
        · simp [hC1, fd_ops_einval_eq]
          exact okPost_ok _ _ rfl
        · have hC1F : sliceContainsNonnegSpec keepFds.val repW.val = false := Bool.eq_false_iff.mpr hC1
          simp only [hC1F, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
          refine okPost_bind (slices_overlap_nonneg_spec closeFds keepFds) fun b2 hb2 => ?_
          subst hb2
          by_cases hC2 : slicesOverlapNonnegSpec closeFds.val keepFds.val = true
          · simp [hC2, fd_ops_einval_eq]
            exact okPost_ok _ _ rfl
          · have hC2F : slicesOverlapNonnegSpec closeFds.val keepFds.val = false := Bool.eq_false_iff.mpr hC2
            simp only [hC2F, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
            refine okPost_bind (validate_sync_overlaps_spec flags syncR repW closeFds keepFds) fun r2 hr2 => ?_
            by_cases hSy : (!flagSet flags FLAG_HAS_SYNC_BARRIER ||
                (repW != syncR &&
                  !sliceContainsNonnegSpec closeFds.val syncR.val &&
                  !sliceContainsNonnegSpec keepFds.val syncR.val)) = true
            · simp only [hSy, ↓reduceIte, Bool.true_and] at hr2 ⊢
              rw [hr2]
              refine okPost_mono (validate_stdio_overlaps_spec flags syncR inFd outFd errFd repW closeFds keepFds)
                fun r3 hr3 => ?_
              rw [hr3]
              have hGt2 (x : I32) : decide (x > 2#i32) = !decide (x.val ≤ 2) := by
                by_cases h : (2 : Int) < x.val
                · have hx : x > 2#i32 := by scalar_tac
                  have hn : ¬ (x.val ≤ 2) := by omega
                  rw [decide_eq_true hx, decide_eq_false hn]; rfl
                · have hx : ¬ (x > 2#i32) := by scalar_tac
                  have hy : x.val ≤ 2 := by omega
                  rw [decide_eq_false hx, decide_eq_true hy]; rfl
              rw [hGt2 inFd, hGt2 outFd, hGt2 errFd]
              cases hRf : flagSet flags FLAG_REDIRECT_STDIO
              · simp
              · simp only [Bool.not_true, Bool.false_or]
                cases hK : sliceHasStdioSlotSpec keepFds.val
                · simp only [Bool.not_false, Bool.true_and]
                  cases hW : fdInStdioSpec repW inFd outFd errFd
                  · simp only [Bool.not_false, Bool.true_and]
                    cases hC : stdioInSliceSpec closeFds.val inFd outFd errFd
                    · simp only [Bool.not_false, Bool.true_and]
                      cases hB : flagSet flags FLAG_HAS_SYNC_BARRIER
                      · cases hCloseS : (!flagSet flags FLAG_CLOSE_STDIO_SOURCES ||
                            ((!!decide (inFd.val ≤ 2) || !sliceContainsNonnegSpec keepFds.val inFd.val) &&
                             (!!decide (outFd.val ≤ 2) || !sliceContainsNonnegSpec keepFds.val outFd.val) &&
                             (!!decide (errFd.val ≤ 2) || !sliceContainsNonnegSpec keepFds.val errFd.val))) <;> simp
                      · cases hS : fdInStdioSpec syncR inFd outFd errFd
                        · cases hCloseS : (!flagSet flags FLAG_CLOSE_STDIO_SOURCES ||
                              ((!!decide (inFd.val ≤ 2) || !sliceContainsNonnegSpec keepFds.val inFd.val) &&
                               (!!decide (outFd.val ≤ 2) || !sliceContainsNonnegSpec keepFds.val outFd.val) &&
                               (!!decide (errFd.val ≤ 2) || !sliceContainsNonnegSpec keepFds.val errFd.val))) <;> simp
                        · simp
                    · simp
                  · simp
                · simp
            · have hSyF : (!flagSet flags FLAG_HAS_SYNC_BARRIER ||
                  (repW != syncR &&
                    !sliceContainsNonnegSpec closeFds.val syncR.val &&
                    !sliceContainsNonnegSpec keepFds.val syncR.val)) = false := Bool.eq_false_iff.mpr hSy
              simp only [hSyF, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.not_false] at hr2 ⊢
              rw [hr2]
              exact okPost_ok _ _ rfl
    · have hSgF : validSignsSpec flags syncR inFd outFd errFd = false := Bool.eq_false_iff.mpr hSg
      simp only [hSgF, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hr1 ⊢
      rw [hr1]
      exact okPost_ok _ _ rfl
  · have hFlF : validFlagsSpec flags = false := Bool.eq_false_iff.mpr hFl
    simp only [hFlF, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hr0 ⊢
    rw [hr0]
    exact okPost_ok _ _ rfl

end FlagsAndValidation

section PreSyncSteps

private theorem okPost_and_dspec {α : Type} {m : Result α} {P Q : α → Prop}
    (hP : OkPost m P) (hQ : WP.dspec m Q) :
    OkPost m (fun a => P a ∧ Q a) := by
  rcases hP with ⟨v, hv, hp⟩
  exact ⟨v, hv, hp, dspec_of_ok hQ hv⟩

private theorem apply_set_pgid_spec (s : ChildState) (hRun : s.status = .running) (flags : U32) :
    OkPost (postfork.child.apply_set_pgid s flags) fun (r, s1) =>
      s1.status = .running ∧ SameChildConfig s1 s ∧ s1.fds = s.fds ∧
      s1.descs = s.descs ∧ s1.writeLog = s.writeLog ∧ s1.cwd = s.cwd ∧
      s1.sig = s.sig ∧ s1.blockedSigs = s.blockedSigs ∧
      (r = .Ok () →
        (flagSet flags FLAG_SET_PGID = true → s1.pgid = s.pid) ∧
        (flagSet flags FLAG_SET_PGID = false → s1.pgid = s.pgid)) ∧
      (flagSet flags FLAG_SET_PGID = false → r = .Ok ()) ∧
      (s.oracle = [] → flagSet flags FLAG_SET_PGID = true →
        if decide (s.pid > 0 ∧ s.pid = s.sid) then r = .Err EPERM
        else r = .Ok ()) ∧
      ∃ suf, s1.trace = s.trace ++ suf ∧ ∀ ev ∈ suf, ∀ x, ev.req ≠ .read1 x := by
  unfold postfork.child.apply_set_pgid
  simp only [flag_set_pgid_eq, lift, Aeneas.Std.lift, bind_ok]
  dsimp only [flagSet]
  by_cases hPg : (flags &&& FLAG_SET_PGID != 0#u32) = true
  · simp only [hPg, ↓reduceIte]
    obtain ⟨r, s1, hEq, hCfg1, hFds1, hDescs1, hSig1, hWl1, hCw1, _, _, hPgOk, hPgErr⟩ :=
      sys_setpgid_self_running s hRun
    have hBlk1 : s1.blockedSigs = s.blockedSigs :=
      dspec_of_ok (sys_setpgid_self_dspec_blockedSigs s) hEq
    obtain ⟨out, hTr1⟩ := sys_setpgid_self_trace_eq s hRun hEq
    refine ⟨(r, s1), hEq, hCfg1.status.trans hRun, hCfg1, hFds1, hDescs1, hWl1, hCw1,
      hSig1, hBlk1, fun hr => ⟨fun _ => hPgOk hr, (fun hf => nomatch hf)⟩,
      (fun hf => nomatch hf), fun hOr _ => ?_, ⟨[Event.mk .setpgidSelf out], hTr1, by simp⟩⟩
    by_cases hSess : s.pid > 0 ∧ s.pid = s.sid
    · simp only [decide_eq_true hSess, ↓reduceIte]
      have hCondT : (s.pid == s.sid && decide (s.pid > 0)) = true :=
        (Bool.and_eq_true _ _).mpr ⟨beq_iff_eq.mpr hSess.2, decide_eq_true hSess.1⟩
      exact (hPgErr hOr).1 hCondT
    · simp only [decide_eq_false hSess, Bool.false_eq_true, ↓reduceIte]
      have hCondF : (s.pid == s.sid && decide (s.pid > 0)) = false := by
        rw [Bool.and_eq_false_iff]
        by_cases hgt : s.pid > 0
        · left; rw [beq_false_of_ne]; intro heq; exact hSess ⟨hgt, heq⟩
        · right; simp [hgt]
      exact (hPgErr hOr).2 hCondF
  · have hPgF : (flags &&& FLAG_SET_PGID != 0#u32) = false := Bool.eq_false_iff.mpr hPg
    simp only [hPgF, Bool.false_eq_true, ↓reduceIte]
    exact ⟨(.Ok (), s), rfl, hRun, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ => ⟨(fun ht => nomatch ht), fun _ => rfl⟩,
      fun _ => rfl, (fun _ ht => nomatch ht), ⟨[], by simp, by simp⟩⟩

private theorem apply_reset_sigpipe_spec (s : ChildState) (hRun : s.status = .running) (flags : U32) :
    OkPost (postfork.child.apply_reset_sigpipe s flags) fun (r, s2) =>
      s2.status = .running ∧ SameChildConfig s2 s ∧ s2.fds = s.fds ∧
      s2.descs = s.descs ∧ s2.writeLog = s.writeLog ∧ s2.cwd = s.cwd ∧ s2.pgid = s.pgid ∧
      (r = .Ok () →
        (flagSet flags FLAG_RESET_SIGPIPE = true →
          s2.getSig 13 = .default ∧ s2.blockedSigs = s.blockedSigs.filter (· != 13)) ∧
        (flagSet flags FLAG_RESET_SIGPIPE = false →
          s2.getSig 13 = s.getSig 13 ∧ s2.blockedSigs = s.blockedSigs) ∧
        ∀ g : Int, g ≠ 13 → s2.getSig g = s.getSig g) ∧
      (s.oracle = [] → r = .Ok ()) ∧
      ∃ suf, s2.trace = s.trace ++ suf ∧ ∀ ev ∈ suf, ∀ x, ev.req ≠ .read1 x := by
  unfold postfork.child.apply_reset_sigpipe
  simp only [flag_reset_sigpipe_eq, lift, Aeneas.Std.lift, bind_ok]
  dsimp only [flagSet]
  by_cases hSp : (flags &&& FLAG_RESET_SIGPIPE != 0#u32) = true
  · simp only [hSp, ↓reduceIte]
    obtain ⟨r1, s1, hEq1, hRun1, hCfg1, hFds1, hDescs1, hWl1, hCw1, hPg1, hSig1, hOr1⟩ :=
      sig_dfl_13_post s hRun
    have hBlk1 : s1.blockedSigs = s.blockedSigs :=
      dspec_of_ok (sys_sig_dfl_dspec_blockedSigs s _) hEq1
    obtain ⟨out1, hTr1⟩ := sys_sig_dfl_trace_eq s hRun _ hEq1
    rw [hEq1, bind_ok]
    cases r1 with
    | Err e =>
      have hOrEmpty : s.oracle ≠ [] := fun h0 => by cases hOr1 h0
      refine ⟨(.Err e, s1), rfl, hRun1, hCfg1, hFds1, hDescs1, hWl1, hCw1, hPg1, ?_,
        fun h0 => absurd h0 hOrEmpty,
        ⟨[Event.mk (.sigDfl postfork.child.SIGPIPE) out1], hTr1, by simp⟩⟩
      intro hOk; cases hOk
    | Ok _ =>
      obtain ⟨r2, s2, hEq2, hRun2, hCfg2, hFds2, hDescs2, hWl2, hCw2, hPg2, hSig2, hBlk2, hOr2⟩ :=
        sig_unblock_13_post s1 hRun1
      obtain ⟨out2, hTr2⟩ := sys_sig_unblock_trace_eq s1 hRun1 _ hEq2
      refine ⟨(r2, s2), hEq2, hRun2, hCfg2.trans hCfg1, hFds2.trans hFds1,
        hDescs2.trans hDescs1, hWl2.trans hWl1, hCw2.trans hCw1, hPg2.trans hPg1, fun hr2 => ?_,
        fun h0 => hOr2 (hCfg1.oracle.trans h0),
        ⟨[Event.mk (.sigDfl postfork.child.SIGPIPE) out1,
          Event.mk (.sigUnblock postfork.child.SIGPIPE) out2],
         by rw [hTr2, hTr1, List.append_assoc]; rfl, by simp⟩⟩
      rcases hSig1 rfl with ⟨h13, hOth⟩
      have hSigEq : ∀ g : Int, s2.getSig g = s1.getSig g := fun g => by
        simp [ChildState.getSig, hSig2]
      refine ⟨fun _ => ⟨(hSigEq 13).trans h13, by rw [hBlk2 hr2, hBlk1]⟩,
        (fun hf => nomatch hf),
        fun g hg => (hSigEq g).trans (hOth g hg)⟩
  · have hSpF : (flags &&& FLAG_RESET_SIGPIPE != 0#u32) = false := Bool.eq_false_iff.mpr hSp
    simp only [hSpF, Bool.false_eq_true, ↓reduceIte]
    exact ⟨(.Ok (), s), rfl, hRun, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl,
      fun _ => ⟨(fun ht => nomatch ht), fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩,
      fun _ => rfl, ⟨[], by simp, by simp⟩⟩

private theorem probe_sync_fd_spec
    (s : ChildState) (hRun : s.status = .running) (flags : U32) (syncR : I32) :
    OkPost (postfork.child.probe_sync_fd s flags syncR) fun (r, s1) =>
      s1.status = .running ∧ SameChildConfig s1 s ∧ s1.fds = s.fds ∧
      s1.descs = s.descs ∧ s1.writeLog = s.writeLog ∧ s1.cwd = s.cwd ∧
      s1.pgid = s.pgid ∧ s1.sig = s.sig ∧ s1.blockedSigs = s.blockedSigs ∧
      (s.oracle = [] →
        r = if flagSet flags FLAG_HAS_SYNC_BARRIER && !s.isOpen syncR.val then .Err EBADF else .Ok ()) ∧
      ∃ suf, s1.trace = s.trace ++ suf ∧ ∀ ev ∈ suf, ev.req ≠ .read1 syncR := by
  unfold postfork.child.probe_sync_fd
  simp only [flag_has_sync_barrier_eq, lift, Aeneas.Std.lift, bind_ok]
  dsimp only [flagSet]
  by_cases hSync : (flags &&& FLAG_HAS_SYNC_BARRIER != 0#u32) = true
  · simp only [hSync, ↓reduceIte]
    obtain ⟨r, s1, hEq, hStruct, _, _, hResSpec⟩ := sys_fcntl_getfd_running s hRun syncR
    have hCfg1 : SameChildConfig s1 s := by rw [hStruct]; exact (SameChildConfig.refl s).with_trace _
    have hRun1 : s1.status = .running := hCfg1.status.trans hRun
    have hFds1 : s1.fds = s.fds := by rw [hStruct]
    have hDescs1 : s1.descs = s.descs := by rw [hStruct]
    have hWl1 : s1.writeLog = s.writeLog := by rw [hStruct]
    have hCw1 : s1.cwd = s.cwd := by rw [hStruct]
    have hPg1 : s1.pgid = s.pgid := by rw [hStruct]
    have hSig1 : s1.sig = s.sig := by rw [hStruct]
    have hBlk1 : s1.blockedSigs = s.blockedSigs := by rw [hStruct]
    obtain ⟨out, hTr1⟩ := sys_fcntl_getfd_trace_eq s hRun syncR hEq
    rw [hEq, bind_ok]
    have hOrSpec : s.oracle = [] →
        (match r with | .Ok _ => core.result.Result.Ok () | .Err e => core.result.Result.Err e) =
        if !s.isOpen syncR.val then .Err EBADF else .Ok () := by
      intro h0
      have hNorm : currentFault s = .normal := currentFault_oracle_nil s h0
      rw [hNorm] at hResSpec
      cases hGet : s.getFd syncR.val with
      | none =>
        rw [hGet] at hResSpec
        have hNotOp : s.isOpen syncR.val = false := by simp [ChildState.isOpen, hGet]
        simp [hResSpec, hNotOp]
      | some e =>
        rw [hGet] at hResSpec
        have hOp : s.isOpen syncR.val = true := by simp [ChildState.isOpen, hGet]
        simp [hResSpec, hOp]
    have hTrList : ∃ suf, s1.trace = s.trace ++ suf ∧ ∀ ev ∈ suf, ev.req ≠ .read1 syncR :=
      ⟨[Event.mk (.fcntlGetfd syncR) out], hTr1, by simp⟩
    cases r with
    | Ok _ =>
      refine ⟨(.Ok (), s1), rfl, hRun1, hCfg1, hFds1, hDescs1, hWl1, hCw1, hPg1, hSig1, hBlk1,
        fun h0 => by simpa [flagSet, hSync] using hOrSpec h0, hTrList⟩
    | Err e =>
      refine ⟨(.Err e, s1), rfl, hRun1, hCfg1, hFds1, hDescs1, hWl1, hCw1, hPg1, hSig1, hBlk1,
        fun h0 => by simpa [flagSet, hSync] using hOrSpec h0, hTrList⟩
  · have hSyncF : (flags &&& FLAG_HAS_SYNC_BARRIER != 0#u32) = false := Bool.eq_false_iff.mpr hSync
    simp only [hSyncF, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    exact ⟨(.Ok (), s), rfl, hRun, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ => by simp, ⟨[], by simp, by simp⟩⟩

private theorem probe_redir_stdio_spec
    (s : ChildState) (hRun : s.status = .running)
    (flags : U32) (syncR inFd outFd errFd : I32) :
    OkPost (postfork.child.probe_redir_stdio s flags inFd outFd errFd) fun (r, s1) =>
      s1.status = .running ∧ SameChildConfig s1 s ∧ s1.fds = s.fds ∧
      s1.descs = s.descs ∧ s1.writeLog = s.writeLog ∧ s1.cwd = s.cwd ∧
      s1.pgid = s.pgid ∧ s1.sig = s.sig ∧ s1.blockedSigs = s.blockedSigs ∧
      (r = .Ok () → flagSet flags FLAG_REDIRECT_STDIO = true →
        s.isOpen inFd.val = true ∧ s.isOpen outFd.val = true ∧ s.isOpen errFd.val = true) ∧
      (s.oracle = [] →
        r =
          if flagSet flags FLAG_REDIRECT_STDIO &&
              (inFd < 0#i32 || outFd < 0#i32 || errFd < 0#i32 ||
                !s.isOpen inFd.val || !s.isOpen outFd.val || !s.isOpen errFd.val) then
            .Err EBADF
          else
            .Ok ()) ∧
      ∃ suf, s1.trace = s.trace ++ suf ∧ ∀ ev ∈ suf, ev.req ≠ .read1 syncR := by
  unfold postfork.child.probe_redir_stdio
  simp only [flag_redirect_stdio_eq, lift, Aeneas.Std.lift, bind_ok]
  dsimp only [flagSet]
  by_cases hRedir : (flags &&& FLAG_REDIRECT_STDIO != 0#u32) = true
  · simp only [hRedir, ↓reduceIte]
    by_cases hOr : s.oracle = []
    · refine okPost_mono
        (okPost_and_dspec
          (okPost_and (probe_stdio_open_safety s hRun inFd outFd errFd)
            (okPost_and (probe_stdio_open_noRead s hRun syncR inFd outFd errFd)
              (probe_stdio_open_spec s hRun hOr inFd outFd errFd)))
          (probe_stdio_open_dspec_blockedSigs s inFd outFd errFd))
        fun ⟨r, s1⟩ ⟨⟨⟨hRun1, hCfg1, hPg1, hCw1, hSig1, hDe1, hFds1, hWl1, hSafe1⟩,
          ⟨suf, hTr, hNoRd⟩, ⟨_, _, _, _, _, _, _, hSp⟩⟩, hBlk1⟩ => ?_
      refine ⟨hRun1, hCfg1, hFds1, hDe1, hWl1, hCw1, hPg1, hSig1, hBlk1, fun hr _ => ?_, fun _ => ?_, ⟨suf, hTr, hNoRd⟩⟩
      · exact ⟨(hSafe1 hr).2.2.2.1, (hSafe1 hr).2.2.2.2.1, (hSafe1 hr).2.2.2.2.2⟩
      · rw [Bool.true_and]
        by_cases hNeg : (decide (inFd < 0#i32) || decide (outFd < 0#i32) || decide (errFd < 0#i32)) = true
        · simp only [hNeg, ↓reduceIte] at hSp
          have hNeg' : (inFd < 0#i32 || outFd < 0#i32 || errFd < 0#i32) = true := hNeg
          simp only [hNeg', ↓reduceIte, Bool.true_or]
          exact hSp.1
        · have hNegF : (inFd < 0#i32 || outFd < 0#i32 || errFd < 0#i32) = false := Bool.eq_false_iff.mpr hNeg
          simp only [hNegF, Bool.false_eq_true, ↓reduceIte, Bool.false_or] at hSp ⊢
          by_cases hOp : (s.isOpen inFd.val && s.isOpen outFd.val && s.isOpen errFd.val) = true
          · simp only [hOp, ↓reduceIte] at hSp
            have h1 : s.isOpen inFd.val = true := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hOp).1).1
            have h2 : s.isOpen outFd.val = true := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hOp).1).2
            have h3 : s.isOpen errFd.val = true := (Bool.and_eq_true _ _ |>.mp hOp).2
            simp [h1, h2, h3, hSp]
          · have hOpF : (s.isOpen inFd.val && s.isOpen outFd.val && s.isOpen errFd.val) = false :=
              Bool.eq_false_iff.mpr hOp
            simp only [hOpF, Bool.false_eq_true, ↓reduceIte] at hSp
            have hNotOp : ((!s.isOpen inFd.val || !s.isOpen outFd.val || !s.isOpen errFd.val)) = true := by
              rw [Bool.and_eq_false_iff, Bool.and_eq_false_iff] at hOpF
              rcases hOpF with (h1 | h2) | h3
              · simp [h1]
              · simp [h2]
              · simp [h3]
            simp [hNotOp, hSp]
    · refine okPost_mono
        (okPost_and_dspec
          (okPost_and (probe_stdio_open_safety s hRun inFd outFd errFd)
            (probe_stdio_open_noRead s hRun syncR inFd outFd errFd))
          (probe_stdio_open_dspec_blockedSigs s inFd outFd errFd))
        fun ⟨r, s1⟩ ⟨⟨⟨hRun1, hCfg1, hPg1, hCw1, hSig1, hDe1, hFds1, hWl1, hSafe1⟩, ⟨suf, hTr, hNoRd⟩⟩, hBlk1⟩ => ?_
      exact ⟨hRun1, hCfg1, hFds1, hDe1, hWl1, hCw1, hPg1, hSig1, hBlk1,
        (fun hr _ => ⟨(hSafe1 hr).2.2.2.1, (hSafe1 hr).2.2.2.2.1, (hSafe1 hr).2.2.2.2.2⟩),
        fun h0 => absurd h0 hOr, ⟨suf, hTr, hNoRd⟩⟩
  · have hRedirF : (flags &&& FLAG_REDIRECT_STDIO != 0#u32) = false := Bool.eq_false_iff.mpr hRedir
    simp only [hRedirF, Bool.false_eq_true, ↓reduceIte]
    exact ⟨(.Ok (), s), rfl, hRun, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      (fun _ ht => nomatch ht), fun _ => by simp, ⟨[], by simp, by simp⟩⟩

private theorem probe_open_slice_pre_spec
    (s : ChildState) (hRun : s.status = .running) (syncR : I32) (keepFds : Slice I32) :
    OkPost (postfork.fd_ops.probe_open_slice s keepFds) fun (r, s1) =>
      s1.status = .running ∧ SameChildConfig s1 s ∧ s1.fds = s.fds ∧
      s1.descs = s.descs ∧ s1.writeLog = s.writeLog ∧ s1.cwd = s.cwd ∧
      s1.pgid = s.pgid ∧ s1.sig = s.sig ∧ s1.blockedSigs = s.blockedSigs ∧
      (r = .Ok () → ∀ fd ∈ keepFds.val, 0 ≤ fd.val → s.isOpen fd.val = true) ∧
      (s.oracle = [] →
        r =
          if keepFds.val.any (fun k => decide (0#i32 ≤ k) && !s.isOpen k.val) then
            .Err EBADF
          else
            .Ok ()) ∧
      ∃ suf, s1.trace = s.trace ++ suf ∧ ∀ ev ∈ suf, ev.req ≠ .read1 syncR := by
  by_cases hOr : s.oracle = []
  · refine okPost_mono
      (okPost_and_dspec
        (okPost_and (probe_open_slice_safety s hRun keepFds)
          (okPost_and (probe_open_slice_noRead s hRun syncR keepFds)
            (probe_open_slice_spec s hRun hOr keepFds)))
        (probe_open_slice_dspec_blockedSigs s keepFds))
      fun ⟨r, s1⟩ ⟨⟨⟨hRun1, hCfg1, hFds1, hPg1, hCw1, hSig1, hDe1, hWl1, hSafe1⟩,
        ⟨suf, hTr, hNoRd⟩, ⟨_, _, _, _, _, _, _, hSp⟩⟩, hBlk1⟩ => ?_
    refine ⟨hRun1, hCfg1, hFds1, hDe1, hWl1, hCw1, hPg1, hSig1, hBlk1, hSafe1, fun _ => ?_, ⟨suf, hTr, hNoRd⟩⟩
    cases hr : r with
    | Ok u =>
      cases u
      rw [hr] at hSp
      dsimp only at hSp
      have hNone : keepFds.val.any (fun k => decide (0#i32 ≤ k) && !s.isOpen k.val) = false := by
        rw [List.any_eq_false]
        intro k hk
        by_cases h0 : (0 : Int) ≤ k.val
        · have h0i : decide (0#i32 ≤ k) = true := decide_eq_true (by scalar_tac)
          rw [h0i]; simp [hSp k hk h0]
        · have h0i : decide (0#i32 ≤ k) = false := decide_eq_false (by scalar_tac)
          rw [h0i]; simp
      rw [hNone]
      rfl
    | Err e =>
      rw [hr] at hSp
      rcases hSp with ⟨hErr, fd, hmem, h0, hClosed⟩
      have hAny : keepFds.val.any (fun k => decide (0#i32 ≤ k) && !s.isOpen k.val) = true := by
        rw [List.any_eq_true]
        have h0i : decide (0#i32 ≤ fd) = true := decide_eq_true (by scalar_tac)
        exact ⟨fd, hmem, by rw [h0i]; simp [hClosed]⟩
      simp only [hAny, ↓reduceIte]
      exact congrArg core.result.Result.Err hErr
  · refine okPost_mono
      (okPost_and_dspec
        (okPost_and (probe_open_slice_safety s hRun keepFds)
          (probe_open_slice_noRead s hRun syncR keepFds))
        (probe_open_slice_dspec_blockedSigs s keepFds))
      fun ⟨r, s1⟩ ⟨⟨⟨hRun1, hCfg1, hFds1, hPg1, hCw1, hSig1, hDe1, hWl1, hSafe1⟩, ⟨suf, hTr, hNoRd⟩⟩, hBlk1⟩ => ?_
    exact ⟨hRun1, hCfg1, hFds1, hDe1, hWl1, hCw1, hPg1, hSig1, hBlk1, hSafe1,
      fun h0 => absurd h0 hOr, ⟨suf, hTr, hNoRd⟩⟩

private theorem read_sync_byte_preserves_streams
    (s : ChildState) (syncR : I32) :
    OkPost (postfork.child.read_sync_byte s syncR) fun (_, sOut) =>
      ∀ d rd rem, s.getDesc d = .stream rd true false rem →
        ∃ rd' rem', sOut.getDesc d = .stream rd' true false rem' := by
  unfold postfork.child.read_sync_byte
  by_cases hNeg : syncR < 0#i32
  · simp only [hNeg, ↓reduceIte]
    exact ⟨(false, s), rfl, fun d rd rem hD => ⟨rd, rem, hD⟩⟩
  · simp only [hNeg, ↓reduceIte]
    let inv : ChildState → Prop := fun cur =>
      ∀ d rd rem, s.getDesc d = .stream rd true false rem →
        ∃ rd' rem', cur.getDesc d = .stream rd' true false rem'
    let post : ChildState × Bool → Prop := fun (cur, _) => inv cur
    have hLoop :
        OkPost (postfork.child.read_sync_byte_loop s syncR) post := by
      rw [postfork.child.read_sync_byte_loop]
      refine okPost_loop_decr_nat
        (fun cur => cur.oracle.length - cur.trace.length) inv post
        (postfork.child.read_sync_byte_loop.body syncR) s ?_
        (fun d rd rem hD => ⟨rd, rem, hD⟩)
      intro cur hInv
      unfold postfork.child.read_sync_byte_loop.body
      dsimp only
      have hEbadfNe : EBADF ≠ postfork.fd_ops.EINTR := by
        unfold EBADF postfork.fd_ops.EINTR; decide
      have hEisdirNe : EISDIR ≠ postfork.fd_ops.EINTR := by
        unfold EISDIR postfork.fd_ops.EINTR; decide
      have hRead1 :
          OkPost (sys.read1 cur syncR (Array.repeat 1#usize 0#u8)) fun (r, cur', _) =>
            inv cur' ∧
            (r = .Err postfork.fd_ops.EINTR →
              cur'.oracle = cur.oracle ∧
              cur'.trace.length = cur.trace.length + 1 ∧ cur.trace.length < cur.oracle.length) := by
        unfold sys.read1
        by_cases hRun : cur.status = .running
        · simp only [hRun]
          cases hcf : currentFault cur
          · dsimp only
            cases hFd : cur.getFd syncR.val with
            | none =>
              dsimp only
              refine ⟨_, rfl, ?_⟩
              exact ⟨hInv, fun hEq => absurd (core.result.Result.Err.inj hEq) hEbadfNe⟩
            | some e =>
              dsimp only
              cases hE : cur.getDesc e.desc with
              | directory _ | procSelfFd _ =>
                dsimp only
                refine ⟨_, rfl, ?_⟩
                exact ⟨hInv, fun hEq => absurd (core.result.Result.Err.inj hEq) hEisdirNe⟩
              | stream r0 w0 b0 s0 =>
                cases r0
                · dsimp only
                  refine ⟨_, rfl, ?_⟩
                  exact ⟨hInv, fun hEq => absurd (core.result.Result.Err.inj hEq) hEbadfNe⟩
                · dsimp only
                  cases s0 with
                  | nil =>
                    dsimp only
                    refine ⟨_, rfl, ?_⟩
                    exact ⟨hInv, fun hEq => by cases hEq⟩
                  | cons hd tl =>
                    dsimp only
                    refine ⟨_, rfl, ?_, fun hEq => by cases hEq⟩
                    intro d rd rem hD
                    rcases hInv d rd rem hD with ⟨rd1, rem1, hD1⟩
                    by_cases hEqD : e.desc = d
                    · rw [hEqD, hD1] at hE
                      cases hE
                      refine ⟨true, tl, ?_⟩
                      have hPut : (cur.putDesc e.desc (DescState.stream true true false tl)).getDesc d =
                          DescState.stream true true false tl := by
                        rw [hEqD]; exact getDesc_putDesc_self _ _ _
                      exact hPut
                    · refine ⟨rd1, rem1, ?_⟩
                      have hPut : (cur.putDesc e.desc (DescState.stream true w0 b0 tl)).getDesc d =
                          cur.getDesc d := getDesc_putDesc_ne cur (Ne.symm hEqD) _
                      exact hPut.trans hD1
          · rename_i rawE
            dsimp only
            cases hFd : cur.getFd syncR.val with
            | none =>
              dsimp only
              refine ⟨_, rfl, ?_⟩
              exact ⟨hInv, fun hEq => absurd (core.result.Result.Err.inj hEq) hEbadfNe⟩
            | some e =>
              dsimp only
              cases hE : cur.getDesc e.desc with
              | directory _ | procSelfFd _ =>
                dsimp only
                refine ⟨_, rfl, ?_⟩
                exact ⟨hInv, fun hEq => absurd (core.result.Result.Err.inj hEq) hEisdirNe⟩
              | stream r0 w0 b0 s0 =>
                cases r0
                · dsimp only
                  refine ⟨_, rfl, ?_⟩
                  exact ⟨hInv, fun hEq => absurd (core.result.Result.Err.inj hEq) hEbadfNe⟩
                · dsimp only
                  refine ⟨_, rfl, ?_⟩
                  refine ⟨hInv, fun _ => ?_⟩
                  unfold currentFault at hcf
                  have hlt : cur.trace.length < cur.oracle.length := by
                    by_contra hge
                    have hnone : cur.oracle[cur.trace.length]? = none := List.getElem?_eq_none (by omega)
                    rw [hnone] at hcf; cases hcf
                  exact ⟨rfl, by simp, hlt⟩
          · rename_i rawE
            dsimp only
            refine ⟨_, rfl, ?_⟩
            refine ⟨hInv, fun _ => ?_⟩
            unfold currentFault at hcf
            have hlt : cur.trace.length < cur.oracle.length := by
              by_contra hge
              have hnone : cur.oracle[cur.trace.length]? = none := List.getElem?_eq_none (by omega)
              rw [hnone] at hcf; cases hcf
            exact ⟨rfl, by simp, hlt⟩
          · dsimp only
            cases hFd : cur.getFd syncR.val with
            | none =>
              dsimp only
              refine ⟨_, rfl, ?_⟩
              exact ⟨hInv, fun hEq => absurd (core.result.Result.Err.inj hEq) hEbadfNe⟩
            | some e =>
              dsimp only
              cases hE : cur.getDesc e.desc with
              | directory _ | procSelfFd _ =>
                dsimp only
                refine ⟨_, rfl, ?_⟩
                exact ⟨hInv, fun hEq => absurd (core.result.Result.Err.inj hEq) hEisdirNe⟩
              | stream r0 w0 b0 s0 =>
                cases r0
                · dsimp only
                  refine ⟨_, rfl, ?_⟩
                  exact ⟨hInv, fun hEq => absurd (core.result.Result.Err.inj hEq) hEbadfNe⟩
                · dsimp only
                  cases s0 with
                  | nil =>
                    dsimp only
                    refine ⟨_, rfl, ?_⟩
                    exact ⟨hInv, fun hEq => by cases hEq⟩
                  | cons hd tl =>
                    dsimp only
                    refine ⟨_, rfl, ?_, fun hEq => by cases hEq⟩
                    intro d rd rem hD
                    rcases hInv d rd rem hD with ⟨rd1, rem1, hD1⟩
                    by_cases hEqD : e.desc = d
                    · rw [hEqD, hD1] at hE
                      cases hE
                      refine ⟨true, tl, ?_⟩
                      have hPut : (cur.putDesc e.desc (DescState.stream true true false tl)).getDesc d =
                          DescState.stream true true false tl := by
                        rw [hEqD]; exact getDesc_putDesc_self _ _ _
                      exact hPut
                    · refine ⟨rd1, rem1, ?_⟩
                      have hPut : (cur.putDesc e.desc (DescState.stream true w0 b0 tl)).getDesc d =
                          cur.getDesc d := getDesc_putDesc_ne cur (Ne.symm hEqD) _
                      exact hPut.trans hD1
          · dsimp only
            cases hFd : cur.getFd syncR.val with
            | none =>
              dsimp only
              refine ⟨_, rfl, ?_⟩
              exact ⟨hInv, fun hEq => absurd (core.result.Result.Err.inj hEq) hEbadfNe⟩
            | some e =>
              dsimp only
              cases hE : cur.getDesc e.desc with
              | directory _ | procSelfFd _ =>
                dsimp only
                refine ⟨_, rfl, ?_⟩
                exact ⟨hInv, fun hEq => absurd (core.result.Result.Err.inj hEq) hEisdirNe⟩
              | stream r0 w0 b0 s0 =>
                cases r0
                · dsimp only
                  refine ⟨_, rfl, ?_⟩
                  exact ⟨hInv, fun hEq => absurd (core.result.Result.Err.inj hEq) hEbadfNe⟩
                · dsimp only
                  cases s0 with
                  | nil =>
                    dsimp only
                    refine ⟨_, rfl, ?_⟩
                    exact ⟨hInv, fun hEq => by cases hEq⟩
                  | cons hd tl =>
                    dsimp only
                    refine ⟨_, rfl, ?_, fun hEq => by cases hEq⟩
                    intro d rd rem hD
                    rcases hInv d rd rem hD with ⟨rd1, rem1, hD1⟩
                    by_cases hEqD : e.desc = d
                    · rw [hEqD, hD1] at hE
                      cases hE
                      refine ⟨true, tl, ?_⟩
                      have hPut : (cur.putDesc e.desc (DescState.stream true true false tl)).getDesc d =
                          DescState.stream true true false tl := by
                        rw [hEqD]; exact getDesc_putDesc_self _ _ _
                      exact hPut
                    · refine ⟨rd1, rem1, ?_⟩
                      have hPut : (cur.putDesc e.desc (DescState.stream true w0 b0 tl)).getDesc d =
                          cur.getDesc d := getDesc_putDesc_ne cur (Ne.symm hEqD) _
                      exact hPut.trans hD1
        · cases hSt : cur.status
          · exact absurd hSt hRun
          · exact ⟨_, rfl, hInv, fun hEq => by cases hEq⟩
          · exact ⟨_, rfl, hInv, fun hEq => by cases hEq⟩
          · exact ⟨_, rfl, hInv, fun hEq => by cases hEq⟩
      refine okPost_bind hRead1 fun p ⟨hInv', hDecr⟩ => ?_
      rcases p with ⟨r, cur', snd⟩
      dsimp only at hInv' hDecr
      cases r with
      | Ok i =>
        change OkPost
          (match i.val with
            | 1 => ok (ControlFlow.done (cur', true))
            | _ => ok (ControlFlow.done (cur', false))) _
        split <;> exact ⟨_, rfl, hInv'⟩
      | Err e =>
        change OkPost
          (if (e != postfork.fd_ops.EINTR) = true then ok (ControlFlow.done (cur', false))
           else ok (ControlFlow.cont cur')) _
        by_cases hNe : (e != postfork.fd_ops.EINTR) = true
        · simp only [hNe, ↓reduceIte]
          exact ⟨ControlFlow.done (cur', false), rfl, hInv'⟩
        · have hNeF : (e != postfork.fd_ops.EINTR) = false := Bool.eq_false_iff.mpr hNe
          have hEq : e = postfork.fd_ops.EINTR := by simpa [bne_iff_ne] using hNeF
          simp only [hNeF, Bool.false_eq_true, ↓reduceIte]
          have ⟨hOrEq, hTrLen, hLt⟩ := hDecr (congrArg core.result.Result.Err hEq)
          exact ⟨ControlFlow.cont cur', rfl, hInv', by rw [hOrEq]; omega⟩
    refine okPost_bind hLoop fun ⟨s1, gotOne⟩ hPost => ?_
    dsimp only [Aeneas.Std.uncurry]
    by_cases hRun1 : s1.status = .running
    · obtain ⟨r2, s2, h2eq, _, _, _, _, hde2, _, _, _, _⟩ := sys_close_running s1 hRun1 syncR
      rw [h2eq, bind_ok]
      refine ⟨(gotOne, s2), rfl, ?_⟩
      intro d rd rem hD
      rcases hPost d rd rem hD with ⟨rd', rem', hD'⟩
      refine ⟨rd', rem', ?_⟩
      dsimp only
      unfold ChildState.getDesc at hD' ⊢
      rw [hde2]
      exact hD'
    · unfold sys.close
      rw [runUnitSyscall_not_running s1 hRun1, bind_ok]
      exact ⟨(gotOne, s1), rfl, hPost⟩

private theorem await_sync_barrier_spec
    (s : ChildState) (hRun : s.status = .running) (flags : U32) (syncR : I32)
    (hSign : !(flagSet flags FLAG_HAS_SYNC_BARRIER) || decide (0#i32 ≤ syncR) = true) :
    OkPost (postfork.child.await_sync_barrier s flags syncR) fun (b, sOut) =>
      (s.oracle = [] → flagSet flags FLAG_HAS_SYNC_BARRIER = true →
        (∃ e w brk hd tl, s.getFd syncR.val = some e ∧ s.getDesc e.desc = .stream true w brk (hd :: tl)) →
        b = true) ∧
      if b then
        sOut.status = .running ∧ SameChildConfig sOut s ∧
        sOut.pgid = s.pgid ∧ sOut.cwd = s.cwd ∧ sOut.sig = s.sig ∧
        sOut.blockedSigs = s.blockedSigs ∧
        sOut.writeLog = s.writeLog ∧
        (oracleHasSeccomp s.oracle = false → sOut.fds.length ≤ s.fds.length) ∧
        (oracleHasSeccomp s.oracle = false →
          flagSet flags FLAG_HAS_SYNC_BARRIER = true → sOut.isOpen syncR.val = false) ∧
        (∀ k : Int, (k ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false) →
          sOut.getFd k = s.getFd k) ∧
        (∀ d rd rem, s.getDesc d = .stream rd true false rem →
          ∃ rd' rem', sOut.getDesc d = .stream rd' true false rem') ∧
        (flagSet flags FLAG_HAS_SYNC_BARRIER = false → sOut.descs = s.descs) ∧
        (∃ suf, sOut.trace = s.trace ++ suf) ∧
        (flagSet flags FLAG_HAS_SYNC_BARRIER = true →
          ∃ e writable broken byte rest,
            s.getFd syncR.val = some e ∧
            s.getDesc e.desc = .stream true writable broken (byte :: rest))
      else
        flagSet flags FLAG_HAS_SYNC_BARRIER = true ∧
        sOut.status = .exited 125#i32 ∧
        sOut.writeLog = s.writeLog ∧
        (oracleHasSeccomp s.oracle = false → sOut.isOpen syncR.val = false) ∧
        (∀ k : Int, k ≠ syncR.val → sOut.getFd k = s.getFd k) ∧
        (∃ suf, sOut.trace = s.trace ++ suf) := by
  unfold postfork.child.await_sync_barrier
  simp only [flag_has_sync_barrier_eq, lift, Aeneas.Std.lift, bind_ok]
  dsimp only [flagSet]
  by_cases hSync : (flags &&& FLAG_HAS_SYNC_BARRIER != 0#u32) = true
  · simp only [hSync, ↓reduceIte]
    have hNonNeg : ¬ (syncR < 0#i32) := by
      simp only [flagSet, hSync, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hSign
      scalar_tac
    refine okPost_bind
      (okPost_and (read_sync_byte_preserves_streams s syncR)
        (okPost_and_dspec (read_sync_byte_spec s syncR) (read_sync_byte_dspec_blockedSigs s syncR)))
      fun (gotOne, s1) ⟨hDescPres, hSp, hBlk1⟩ => ?_
    dsimp only [SyncBytePost] at hSp
    simp only [hNonNeg, ↓reduceIte, hRun] at hSp
    rcases hSp with ⟨hCfg1, hPg1, hCw1, hSig1, hWl1, hFdsSec1, hClosed1, hOther1, ⟨suf1, hTr1⟩, hGot⟩
    have hRun1 : s1.status = .running := hCfg1.status.trans hRun
    have hLen1 : oracleHasSeccomp s.oracle = false → s1.fds.length ≤ s.fds.length := fun hNoSec => by
      rw [hFdsSec1 hNoSec]
      exact List.length_filter_le _ _
    cases gotOne
    · change OkPost (do let s2 ← sys.exit s1 postfork.child.EXIT_SYNC_ABORT; ok (false, s2)) _
      unfold sys.exit
      rw [hRun1, child_exit_sync_abort_eq, bind_ok]
      refine ⟨(false, _), rfl, fun hOr _ ⟨e, w, brk, hd, tl, he, hde⟩ => ?_,
        trivial, rfl, hWl1, hClosed1, hOther1,
        ⟨_, by dsimp only; rw [hTr1, List.append_assoc]⟩⟩
      exfalso
      have hTrue : (false : Bool) = true := hGot.mpr ⟨e, w, brk, hd, tl, he, hde, by
        simp [hOr, firstNonEintrFault]⟩
      cases hTrue
    · have hStream := hGot.mp rfl
      rcases hStream with ⟨e, w, brk, b, rest, hFd, hDesc, _⟩
      exact ⟨(true, s1), rfl,
        fun _ _ _ => rfl, hRun1, hCfg1, hPg1, hCw1, hSig1, hBlk1, hWl1, hLen1,
        fun hNs _ => hClosed1 hNs,
        fun k hk => hOther1 k (hk.resolve_right (by decide)),
        hDescPres, (fun hf => nomatch hf),
        ⟨suf1, hTr1⟩, fun _ => ⟨e, w, brk, b, rest, hFd, hDesc⟩⟩
  · have hSyncF : (flags &&& FLAG_HAS_SYNC_BARRIER != 0#u32) = false := Bool.eq_false_iff.mpr hSync
    simp only [hSyncF, Bool.false_eq_true, ↓reduceIte]
    exact ⟨(true, s), rfl,
      fun _ _ _ => rfl, hRun, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl,
      fun _ => Nat.le_refl _,
      (fun _ hf => nomatch hf), fun _ _ => rfl,
      fun d rd rem hD => ⟨rd, rem, hD⟩, fun _ => rfl, ⟨[], by simp⟩,
      (fun hf => nomatch hf)⟩

/-- State invariant guaranteed whenever `postfork.child.run_child_pre_sync` returns `(true, sOut)` from running state `s`. -/
def PreSyncOkPost
    (s : ChildState) (flags : U32) (syncR inFd outFd errFd repW : I32)
    (closeFds keepFds : List I32) (sOut : ChildState) : Prop :=
  sOut.status = .running ∧
  SameChildConfig sOut s ∧
  sOut.writeLog = s.writeLog ∧
  sOut.cwd = s.cwd ∧
  validFlagsSpec flags = true ∧
  0#i32 ≤ repW ∧
  validSignsSpec flags syncR inFd outFd errFd = true ∧
  validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds keepFds = true ∧
  (oracleHasSeccomp s.oracle = false → sOut.fds.length ≤ s.fds.length) ∧
  (flagSet flags FLAG_SET_PGID = true → sOut.pgid = s.pid) ∧
  (flagSet flags FLAG_SET_PGID = false → sOut.pgid = s.pgid) ∧
  (flagSet flags FLAG_RESET_SIGPIPE = true →
    sOut.getSig 13 = .default ∧ sOut.blockedSigs = s.blockedSigs.filter (· != 13)) ∧
  (flagSet flags FLAG_RESET_SIGPIPE = false →
    sOut.getSig 13 = s.getSig 13 ∧ sOut.blockedSigs = s.blockedSigs) ∧
  (∀ g : Int, g ≠ 13 → sOut.getSig g = s.getSig g) ∧
  (∀ k : Int,
    (k ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false) →
    sliceContainsNonnegSpec closeFds k = false →
    sOut.getFd k = s.getFd k) ∧
  (oracleHasSeccomp s.oracle = false →
    ∀ k : Int,
      sOut.getFd k =
        if sliceContainsNonnegSpec closeFds k ||
            (flagSet flags FLAG_HAS_SYNC_BARRIER && k == syncR.val) then
          none
        else
          s.getFd k) ∧
  (∀ d rd rem, s.getDesc d = .stream rd true false rem →
    ∃ rd' rem', sOut.getDesc d = .stream rd' true false rem') ∧
  (flagSet flags FLAG_HAS_SYNC_BARRIER = false → sOut.descs = s.descs) ∧
  (flagSet flags FLAG_REDIRECT_STDIO = true →
    s.isOpen inFd.val = true ∧ s.isOpen outFd.val = true ∧ s.isOpen errFd.val = true) ∧
  (∀ k ∈ keepFds, 0#i32 ≤ k → s.isOpen k.val = true) ∧
  (∃ tA tB : List Event,
    sOut.trace = s.trace ++ tA ++ tB ∧
    (∀ ev ∈ tA, ev.req ≠ .read1 syncR) ∧
    (∀ cfd ∈ closeFds, 0#i32 ≤ cfd → ∃ out, Event.mk (.close cfd) out ∈ tA))

/-- Arbitrary-oracle safety specification of `postfork.child.run_child_pre_sync`. -/
theorem run_child_pre_sync_safety
    (s : ChildState) (hRun : s.status = .running)
    (flags : U32) (syncR inFd outFd errFd repW : I32) (closeFds keepFds : Slice I32) :
    OkPost
      (postfork.child.run_child_pre_sync s flags syncR inFd outFd errFd repW closeFds keepFds)
      fun (b, sOut) =>
        if b then
          PreSyncOkPost s flags syncR inFd outFd errFd repW closeFds.val keepFds.val sOut
        else
          sOut.status = .exited 127#i32 ∨
          (flagSet flags FLAG_HAS_SYNC_BARRIER = true ∧
            sOut.status = .exited 125#i32 ∧
            sOut.writeLog = s.writeLog ∧
            (oracleHasSeccomp s.oracle = false →
              sOut.isOpen syncR.val = false ∧
              (∀ cfd ∈ closeFds.val, 0#i32 ≤ cfd → sOut.isOpen cfd.val = false)) ∧
            closedBeforeSyncRead (sOut.trace.drop s.trace.length) closeFds.val syncR) := by
  unfold postfork.child.run_child_pre_sync
  by_cases hRep : repW < 0#i32
  · simp only [hRep, ↓reduceIte, child_exit_exec_failed_eq]
    unfold sys.exit
    rw [hRun]
    simp only [bind_ok]
    exact ⟨(false, _), rfl, Or.inl rfl⟩
  · simp only [hRep, ↓reduceIte]
    have hRepGe : 0#i32 ≤ repW := by scalar_tac
    refine okPost_bind (validate_child_args_spec flags syncR inFd outFd errFd repW closeFds keepFds)
      fun rVal hrVal => ?_
    by_cases hValFl : (!validFlagsSpec flags) = true
    · simp only [hValFl, ↓reduceIte] at hrVal
      rw [hrVal]
      refine okPost_bind (report_and_exit_status127 s hRun repW _ _ _) fun sExit hExit => ?_
      exact ⟨(false, sExit), rfl, Or.inl hExit⟩
    · have hValFlF : (!validFlagsSpec flags) = false := Bool.eq_false_iff.mpr hValFl
      simp only [hValFlF, Bool.false_eq_true, ↓reduceIte] at hrVal
      have hFlT : validFlagsSpec flags = true := by simpa using hValFlF
      by_cases hValSg : (!validSignsSpec flags syncR inFd outFd errFd) = true
      · simp only [hValSg, ↓reduceIte] at hrVal
        rw [hrVal]
        refine okPost_bind (report_and_exit_status127 s hRun repW _ _ _) fun sExit hExit => ?_
        exact ⟨(false, sExit), rfl, Or.inl hExit⟩
      · have hValSgF : (!validSignsSpec flags syncR inFd outFd errFd) = false := Bool.eq_false_iff.mpr hValSg
        simp only [hValSgF, Bool.false_eq_true, ↓reduceIte] at hrVal
        have hSgT : validSignsSpec flags syncR inFd outFd errFd = true := by simpa using hValSgF
        by_cases hValOv : (!validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds.val keepFds.val) = true
        · simp only [hValOv, ↓reduceIte] at hrVal
          rw [hrVal]
          refine okPost_bind (report_and_exit_status127 s hRun repW _ _ _) fun sExit hExit => ?_
          exact ⟨(false, sExit), rfl, Or.inl hExit⟩
        · have hValOvF : (!validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds.val keepFds.val) = false :=
            Bool.eq_false_iff.mpr hValOv
          simp only [hValOvF, Bool.false_eq_true, ↓reduceIte] at hrVal
          have hOvT : validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds.val keepFds.val = true := by
            simpa using hValOvF
          rw [hrVal]
          refine okPost_bind (apply_set_pgid_spec s hRun flags) fun (r1, s1) hs1 => ?_
          rcases hs1 with ⟨hRun1, hCfg1, hFds1, hDe1, hWl1, hCw1, hSig1, hBlk1, hPg1, _, _, ⟨suf1, hTr1, hNoRd1⟩⟩
          cases r1 with
          | Err e1 =>
            refine okPost_bind (report_and_exit_status127 s1 hRun1 repW _ _ _) fun sExit hExit => ?_
            exact ⟨(false, sExit), rfl, Or.inl hExit⟩
          | Ok _ =>
            rcases hPg1 rfl with ⟨hPgT1, hPgF1⟩
            refine okPost_bind (apply_reset_sigpipe_spec s1 hRun1 flags) fun (r2, s2) hs2 => ?_
            rcases hs2 with ⟨hRun2, hCfg2, hFds2, hDe2, hWl2, hCw2, hPg2, hSig2, _, ⟨suf2, hTr2, hNoRd2⟩⟩
            cases r2 with
            | Err e2 =>
              refine okPost_bind (report_and_exit_status127 s2 hRun2 repW _ _ _) fun sExit hExit => ?_
              exact ⟨(false, sExit), rfl, Or.inl hExit⟩
            | Ok _ =>
              rcases hSig2 rfl with ⟨hSpT2, hSpF2, hSpOth2⟩
              refine okPost_bind
                (okPost_and_dspec (close_unused_slice_safety s2 hRun2 closeFds)
                  (close_unused_slice_dspec_blockedSigs s2 closeFds))
                fun s3 ⟨hs3, hBlk3⟩ => ?_
              rcases hs3 with ⟨hRun3, hCfg3, hPg3, hCw3, hSig3, hDe3, hWl3, hLen3, hKeep3, hSec3,
                ⟨suf3, hTr3, hEvs3, hClosed3⟩⟩
              refine okPost_bind (probe_sync_fd_spec s3 hRun3 flags syncR) fun (r3, s4) hs4 => ?_
              rcases hs4 with ⟨hRun4, hCfg4, hFds4, hDe4, hWl4, hCw4, hPg4, hSig4, hBlk4, _,
                ⟨suf4, hTr4, hNoRd4⟩⟩
              cases r3 with
              | Err e3 =>
                refine okPost_bind (report_and_exit_status127 s4 hRun4 repW _ _ _) fun sExit hExit => ?_
                exact ⟨(false, sExit), rfl, Or.inl hExit⟩
              | Ok _ =>
                refine okPost_bind (probe_redir_stdio_spec s4 hRun4 flags syncR inFd outFd errFd)
                  fun (r4, s5) hs5 => ?_
                rcases hs5 with ⟨hRun5, hCfg5, hFds5, hDe5, hWl5, hCw5, hPg5, hSig5, hBlk5, hStdOp5, _,
                  ⟨suf5, hTr5, hNoRd5⟩⟩
                cases r4 with
                | Err e4 =>
                  refine okPost_bind (report_and_exit_status127 s5 hRun5 repW _ _ _) fun sExit hExit => ?_
                  exact ⟨(false, sExit), rfl, Or.inl hExit⟩
                | Ok _ =>
                  refine okPost_bind (probe_open_slice_pre_spec s5 hRun5 syncR keepFds)
                    fun (r5, s6) hs6 => ?_
                  rcases hs6 with ⟨hRun6, hCfg6, hFds6, hDe6, hWl6, hCw6, hPg6, hSig6, hBlk6, hKpOp6, _,
                    ⟨suf6, hTr6, hNoRd6⟩⟩
                  cases r5 with
                  | Err e5 =>
                    refine okPost_bind (report_and_exit_status127 s6 hRun6 repW _ _ _) fun sExit hExit => ?_
                    exact ⟨(false, sExit), rfl, Or.inl hExit⟩
                  | Ok _ =>
                    have hSignSync : !(flagSet flags FLAG_HAS_SYNC_BARRIER) || decide (0#i32 ≤ syncR) = true := by
                      simpa [validSignsSpec] using (Bool.and_eq_true _ _ |>.mp hSgT).1
                    let tA : List Event := suf1 ++ suf2 ++ suf3 ++ suf4 ++ suf5 ++ suf6
                    have hTrA : s6.trace = s.trace ++ tA := by
                      rw [hTr6, hTr5, hTr4, hTr3, hTr2, hTr1]
                      simp only [tA, List.append_assoc]
                    have hNoRdA : ∀ ev ∈ tA, ev.req ≠ .read1 syncR := by
                      intro ev hev
                      simp only [tA, List.mem_append] at hev
                      rcases hev with ((((h1 | h2) | h3) | h4) | h5) | h6
                      · exact hNoRd1 ev h1 syncR
                      · exact hNoRd2 ev h2 syncR
                      · rcases hEvs3 ev h3 with ⟨fd, out, rfl⟩; simp
                      · exact hNoRd4 ev h4
                      · exact hNoRd5 ev h5
                      · exact hNoRd6 ev h6
                    have hClosedA : ∀ cfd ∈ closeFds.val, 0#i32 ≤ cfd → ∃ out, Event.mk (.close cfd) out ∈ tA := by
                      intro cfd hc h0
                      rcases hClosed3 cfd hc h0 with ⟨out, hout⟩
                      exact ⟨out, by simp [tA, hout]⟩
                    have hCfg60 : SameChildConfig s6 s :=
                      hCfg6.trans (hCfg5.trans (hCfg4.trans (hCfg3.trans (hCfg2.trans hCfg1))))
                    have hFds63 : s6.fds = s3.fds := hFds6.trans (hFds5.trans hFds4)
                    have hDe60 : s6.descs = s.descs :=
                      hDe6.trans (hDe5.trans (hDe4.trans (hDe3.trans (hDe2.trans hDe1))))
                    have hWl60 : s6.writeLog = s.writeLog :=
                      hWl6.trans (hWl5.trans (hWl4.trans (hWl3.trans (hWl2.trans hWl1))))
                    have hCw60 : s6.cwd = s.cwd :=
                      hCw6.trans (hCw5.trans (hCw4.trans (hCw3.trans (hCw2.trans hCw1))))
                    have hPg62 : s6.pgid = s2.pgid := hPg6.trans (hPg5.trans (hPg4.trans hPg3))
                    have hSig62 : s6.sig = s2.sig := hSig6.trans (hSig5.trans (hSig4.trans hSig3))
                    have hBlk62 : s6.blockedSigs = s2.blockedSigs :=
                      hBlk6.trans (hBlk5.trans (hBlk4.trans hBlk3))
                    have hFds20 : s2.fds = s.fds := hFds2.trans hFds1
                    have hLen6 : s6.fds.length ≤ s.fds.length := by
                      rw [hFds63]; exact hLen3.trans_eq (congrArg List.length hFds20)
                    refine okPost_mono (await_sync_barrier_spec s6 hRun6 flags syncR hSignSync)
                      fun (b, sOut) ⟨_, hAw⟩ => ?_
                    cases b
                    · dsimp only at hAw ⊢
                      rcases hAw with ⟨hSyncFl, hSt125, hWlOut, hClosedSync, hOtherOut, ⟨suf7, hTrOut⟩⟩
                      refine Or.inr ⟨hSyncFl, hSt125, hWlOut.trans hWl60, ?_, ?_⟩
                      · intro hNoSec
                        have hNoSec6 : oracleHasSeccomp s6.oracle = false := by
                          rw [hCfg60.oracle]; exact hNoSec
                        have hNoSec2 : oracleHasSeccomp s2.oracle = false := by
                          rw [(hCfg2.trans hCfg1).oracle]; exact hNoSec
                        refine ⟨hClosedSync hNoSec6, fun cfd hmem hc0 => ?_⟩
                        by_cases hEq : cfd.val = syncR.val
                        · rw [hEq]; exact hClosedSync hNoSec6
                        · rw [ChildState.isOpen, hOtherOut cfd.val hEq, ChildState.getFd, hFds63, ← ChildState.getFd]
                          have hS3 : s3.getFd cfd.val = none := by
                            rw [hSec3 hNoSec2 cfd.val]
                            have hMemB : sliceContainsNonnegSpec closeFds.val cfd.val = true := by
                              unfold sliceContainsNonnegSpec
                              rw [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
                              exact ⟨hc0, cfd, hmem, by simp⟩
                            simp [hMemB]
                          rw [hS3]; rfl
                      · have hDrop : sOut.trace.drop s.trace.length = tA ++ suf7 := by
                          rw [hTrOut, hTrA, List.append_assoc, List.drop_left]
                        rw [hDrop]
                        exact closedBeforeSyncRead_append hNoRdA hClosedA
                    · dsimp only at hAw ⊢
                      rcases hAw with ⟨hRunOut, hCfgOut, hPgOut, hCwOut, hSigOut, hBlkOut, hWlOut,
                        hLenOut, hClosedOut, hOtherOut, hDeOut, hDeFOut, ⟨suf7, hTrOut⟩, _⟩
                      have hPg21 : s2.pgid = s1.pgid := hPg2
                      have hCfg20 : SameChildConfig s2 s := hCfg2.trans hCfg1
                      refine ⟨hRunOut, hCfgOut.trans hCfg60, hWlOut.trans hWl60, hCwOut.trans hCw60,
                        hFlT, hRepGe, hSgT, hOvT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                      · intro hNoSec
                        have hNoSec6 : oracleHasSeccomp s6.oracle = false := by
                          rw [hCfg60.oracle]; exact hNoSec
                        exact (hLenOut hNoSec6).trans hLen6
                      · intro ht; rw [hPgOut, hPg62, hPg21]; exact hPgT1 ht
                      · intro hf; rw [hPgOut, hPg62, hPg21]; exact hPgF1 hf
                      · intro ht
                        rcases hSpT2 ht with ⟨h13, hB13⟩
                        refine ⟨?_, ?_⟩
                        · have hSigEq : sOut.getSig 13 = s2.getSig 13 := by
                            simp only [ChildState.getSig, hSigOut, hSig62]
                          rw [hSigEq]; exact h13
                        · rw [hBlkOut, hBlk62, hB13, hBlk1]
                      · intro hf
                        rcases hSpF2 hf with ⟨h13, hB13⟩
                        refine ⟨?_, ?_⟩
                        · have hSigEq : sOut.getSig 13 = s2.getSig 13 := by
                            simp only [ChildState.getSig, hSigOut, hSig62]
                          rw [hSigEq, h13, ChildState.getSig, hSig1]; rfl
                        · rw [hBlkOut, hBlk62, hB13, hBlk1]
                      · intro g hg
                        have hSigEq : sOut.getSig g = s2.getSig g := by
                          simp [ChildState.getSig, hSigOut, hSig62]
                        rw [hSigEq, hSpOth2 g hg]
                        simp [ChildState.getSig, hSig1]
                      · intro k hk hNotCl
                        rw [hOtherOut k hk, ChildState.getFd, hFds63, ← ChildState.getFd,
                          hKeep3 k hNotCl, ChildState.getFd, hFds20]
                        rfl
                      · intro hNoSec k
                        have hNoSec6 : oracleHasSeccomp s6.oracle = false := by
                          rw [hCfg60.oracle]; exact hNoSec
                        have hNoSec2 : oracleHasSeccomp s2.oracle = false := by
                          rw [hCfg20.oracle]; exact hNoSec
                        by_cases hSyncK : (flagSet flags FLAG_HAS_SYNC_BARRIER && k == syncR.val) = true
                        · simp only [Bool.and_eq_true, beq_iff_eq] at hSyncK
                          rcases hSyncK with ⟨hFlagS, rfl⟩
                          simp only [hFlagS, beq_self_eq_true, Bool.and_true, Bool.or_true, ↓reduceIte]
                          have hNotOp := hClosedOut hNoSec6 hFlagS
                          cases hgk : sOut.getFd syncR.val with
                          | none => rfl
                          | some _ => simp [ChildState.isOpen, hgk] at hNotOp
                        · have hNotSync : k ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false := by
                            by_cases hFlagS : flagSet flags FLAG_HAS_SYNC_BARRIER = true
                            · left; intro heq; apply hSyncK; simp [hFlagS, heq]
                            · right; exact Bool.eq_false_iff.mpr hFlagS
                          have hSyncKF : (flagSet flags FLAG_HAS_SYNC_BARRIER && k == syncR.val) = false :=
                            Bool.eq_false_iff.mpr hSyncK
                          simp only [hSyncKF, Bool.or_false]
                          rw [hOtherOut k hNotSync, ChildState.getFd, hFds63, ← ChildState.getFd,
                            hSec3 hNoSec2 k]
                          split <;> simp [ChildState.getFd, hFds20]
                      · intro d rd rem hD
                        apply hDeOut d rd rem
                        rw [ChildState.getDesc, hDe60]; exact hD
                      · intro hf
                        rw [hDeFOut hf, hDe60]
                      · intro hR
                        rcases hStdOp5 rfl hR with ⟨hInOp, hOutOp, hErrOp⟩
                        have hNoStdSlice : stdioInSliceSpec closeFds.val inFd outFd errFd = false := by
                          cases h : stdioInSliceSpec closeFds.val inFd outFd errFd <;>
                            first | rfl | (unfold validRunChildNoOverlap at hOvT; simp [hR, h] at hOvT)
                        have hInNotCl : sliceContainsNonnegSpec closeFds.val inFd.val = false := by
                          cases h : sliceContainsNonnegSpec closeFds.val inFd.val <;>
                            first | rfl | (unfold stdioInSliceSpec at hNoStdSlice; simp [h] at hNoStdSlice)
                        have hOutNotCl : sliceContainsNonnegSpec closeFds.val outFd.val = false := by
                          cases h : sliceContainsNonnegSpec closeFds.val outFd.val <;>
                            first | rfl | (unfold stdioInSliceSpec at hNoStdSlice; simp [h] at hNoStdSlice)
                        have hErrNotCl : sliceContainsNonnegSpec closeFds.val errFd.val = false := by
                          cases h : sliceContainsNonnegSpec closeFds.val errFd.val <;>
                            first | rfl | (unfold stdioInSliceSpec at hNoStdSlice; simp [h] at hNoStdSlice)
                        have hS4Eq : ∀ k, sliceContainsNonnegSpec closeFds.val k = false → s4.getFd k = s.getFd k := by
                          intro k hk
                          rw [ChildState.getFd, hFds4, ← ChildState.getFd, hKeep3 k hk, ChildState.getFd, hFds20]
                          rfl
                        refine ⟨?_, ?_, ?_⟩
                        · simpa [ChildState.isOpen, hS4Eq inFd.val hInNotCl] using hInOp
                        · simpa [ChildState.isOpen, hS4Eq outFd.val hOutNotCl] using hOutOp
                        · simpa [ChildState.isOpen, hS4Eq errFd.val hErrNotCl] using hErrOp
                      · intro k hk hk0
                        have hKpOp := hKpOp6 rfl k hk hk0
                        have hNotCl : sliceContainsNonnegSpec closeFds.val k.val = false := by
                          by_contra hc
                          simp only [Bool.not_eq_false, sliceContainsNonnegSpec, Bool.and_eq_true,
                            decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hc
                          rcases hc with ⟨_, c, hcM, hcEq⟩
                          have hOv : slicesOverlapNonnegSpec closeFds.val keepFds.val = true := by
                            rw [slicesOverlapNonnegSpec, List.any_eq_true]
                            refine ⟨c, hcM, ?_⟩
                            simp only [Bool.and_eq_true, decide_eq_true_eq, sliceContainsNonnegSpec, List.any_eq_true, beq_iff_eq]
                            exact ⟨by scalar_tac, by scalar_tac, k, hk, hcEq.symm⟩
                          have hNoOv : slicesOverlapNonnegSpec closeFds.val keepFds.val = false := by
                            cases h : slicesOverlapNonnegSpec closeFds.val keepFds.val <;>
                              first | rfl | (unfold validRunChildNoOverlap at hOvT; simp [h] at hOvT)
                          rw [hOv] at hNoOv; cases hNoOv
                        have hS5Eq : s5.getFd k.val = s.getFd k.val := by
                          rw [ChildState.getFd, hFds5, hFds4, ← ChildState.getFd, hKeep3 k.val hNotCl, ChildState.getFd, hFds20]
                          rfl
                        simpa [ChildState.isOpen, hS5Eq] using hKpOp
                      · exact ⟨tA, suf7, by rw [hTrOut, hTrA, List.append_assoc], hNoRdA, hClosedA⟩

/-- Exact early-failure and continuation specification of `run_child_pre_sync` under `s.oracle = []`. -/
theorem run_child_pre_sync_oracle_empty
    (s : ChildState) (hRun : s.status = .running) (hOr : s.oracle = [])
    (flags : U32) (syncR inFd outFd errFd repW : I32) (closeFds keepFds : Slice I32) :
    OkPost
      (postfork.child.run_child_pre_sync s flags syncR inFd outFd errFd repW closeFds keepFds)
      fun (b, sOut) =>
        if repW < 0#i32 then
          b = false ∧ sOut.status = .exited 127#i32 ∧ sOut.writeLog = s.writeLog
        else
          match s.getFd repW.val with
          | none => True
          | some repEnt =>
            match s.getDesc repEnt.desc with
            | .stream _ true false _ =>
              if !validFlagsSpec flags then
                b = false ∧ sOut.status = .exited 127#i32 ∧
                appendedBytesForDesc s.writeLog sOut.writeLog repEnt.desc =
                  expectedFailureWireBytes 1#u8 EINVAL
              else if !validSignsSpec flags syncR inFd outFd errFd then
                b = false ∧ sOut.status = .exited 127#i32 ∧
                appendedBytesForDesc s.writeLog sOut.writeLog repEnt.desc =
                  expectedFailureWireBytes 1#u8 EBADF
              else if !validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds.val keepFds.val then
                b = false ∧ sOut.status = .exited 127#i32 ∧
                appendedBytesForDesc s.writeLog sOut.writeLog repEnt.desc =
                  expectedFailureWireBytes 1#u8 EINVAL
              else if flagSet flags FLAG_SET_PGID && decide (s.pid > 0) && decide (s.pid = s.sid) then
                b = false ∧ sOut.status = .exited 127#i32 ∧
                appendedBytesForDesc s.writeLog sOut.writeLog repEnt.desc =
                  expectedFailureWireBytes 2#u8 EPERM
              else if (flagSet flags FLAG_HAS_SYNC_BARRIER && !s.isOpen syncR.val) ||
                  (flagSet flags FLAG_REDIRECT_STDIO &&
                    (!s.isOpen inFd.val || !s.isOpen outFd.val || !s.isOpen errFd.val)) ||
                  keepFds.val.any (fun k => decide (0#i32 ≤ k) && !s.isOpen k.val) then
                b = false ∧ sOut.status = .exited 127#i32 ∧
                appendedBytesForDesc s.writeLog sOut.writeLog repEnt.desc =
                  expectedFailureWireBytes 4#u8 EBADF
              else if flagSet flags FLAG_HAS_SYNC_BARRIER then
                match s.getFd syncR.val with
                | none => True
                | some syncEnt =>
                  match s.getDesc syncEnt.desc with
                  | .stream true _ _ [] =>
                    b = false ∧ sOut.status = .exited 125#i32 ∧ sOut.writeLog = s.writeLog ∧
                    closedBeforeSyncRead (sOut.trace.drop s.trace.length) closeFds.val syncR
                  | .stream true _ _ (_ :: _) =>
                    b = true ∧ PreSyncOkPost s flags syncR inFd outFd errFd repW closeFds.val keepFds.val sOut ∧
                    s.isOpen syncR.val = true ∧
                    (flagSet flags FLAG_REDIRECT_STDIO = true →
                      s.isOpen inFd.val = true ∧ s.isOpen outFd.val = true ∧ s.isOpen errFd.val = true) ∧
                    (∀ k ∈ keepFds.val, 0#i32 ≤ k → s.isOpen k.val = true)
                  | _ => True
              else
                b = true ∧ PreSyncOkPost s flags syncR inFd outFd errFd repW closeFds.val keepFds.val sOut ∧
                (flagSet flags FLAG_REDIRECT_STDIO = true →
                  s.isOpen inFd.val = true ∧ s.isOpen outFd.val = true ∧ s.isOpen errFd.val = true) ∧
                (∀ k ∈ keepFds.val, 0#i32 ≤ k → s.isOpen k.val = true)
            | _ => True := by
  have hSafety := run_child_pre_sync_safety s hRun flags syncR inFd outFd errFd repW closeFds keepFds
  by_cases hRep : repW < 0#i32
  · simp only [hRep, ↓reduceIte]
    unfold postfork.child.run_child_pre_sync
    simp only [hRep, ↓reduceIte, child_exit_exec_failed_eq]
    unfold sys.exit; rw [hRun]; simp only [bind_ok]
    exact ⟨(false, _), rfl, rfl, rfl, rfl⟩
  · simp only [hRep, ↓reduceIte]
    cases hRepFd : s.getFd repW.val with
    | none =>
      exact okPost_mono hSafety (fun _ _ => by simp)
    | some repEnt =>
      cases hDesc : s.getDesc repEnt.desc with
      | directory _ | procSelfFd _ =>
        exact okPost_mono hSafety (fun _ _ => by simp [hDesc])
      | stream rd wr bp rem =>
        cases wr
        · exact okPost_mono hSafety (fun _ _ => by simp [hDesc])
        · cases bp
          · simp only [hDesc]
            have hRepGe : 0#i32 ≤ repW := by scalar_tac
            unfold postfork.child.run_child_pre_sync
            simp only [hRep, ↓reduceIte]
            refine okPost_bind (validate_child_args_spec flags syncR inFd outFd errFd repW closeFds keepFds)
              fun rVal hrVal => ?_
            by_cases hValFl : !validFlagsSpec flags
            · simp only [hValFl, ↓reduceIte] at hrVal ⊢
              rw [hrVal]
              refine okPost_bind (report_and_exit_bytes s hRun hOr repW _ _ _ hRepGe hRepFd hDesc)
                fun sExit ⟨hSt, hApp⟩ => ?_
              have hNorm : normalizeErrnoSpec EINVAL postfork.fd_ops.EINVAL = EINVAL := by
                rw [fd_ops_einval_eq]; rfl
              rw [child_stage_validate_eq, hNorm] at hApp
              exact ⟨(false, sExit), rfl, rfl, hSt, hApp⟩
            · simp only [hValFl, Bool.false_eq_true, ↓reduceIte] at hrVal ⊢
              by_cases hValSg : !validSignsSpec flags syncR inFd outFd errFd
              · simp only [hValSg, ↓reduceIte] at hrVal ⊢
                rw [hrVal]
                refine okPost_bind (report_and_exit_bytes s hRun hOr repW _ _ _ hRepGe hRepFd hDesc)
                  fun sExit ⟨hSt, hApp⟩ => ?_
                have hNorm : normalizeErrnoSpec EBADF postfork.fd_ops.EINVAL = EBADF := by rfl
                rw [child_stage_validate_eq, hNorm] at hApp
                exact ⟨(false, sExit), rfl, rfl, hSt, hApp⟩
              · simp only [hValSg, Bool.false_eq_true, ↓reduceIte] at hrVal ⊢
                by_cases hValOv : !validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds.val keepFds.val
                · simp only [hValOv, ↓reduceIte] at hrVal ⊢
                  rw [hrVal]
                  refine okPost_bind (report_and_exit_bytes s hRun hOr repW _ _ _ hRepGe hRepFd hDesc)
                    fun sExit ⟨hSt, hApp⟩ => ?_
                  have hNorm : normalizeErrnoSpec EINVAL postfork.fd_ops.EINVAL = EINVAL := by
                    rw [fd_ops_einval_eq]; rfl
                  rw [child_stage_validate_eq, hNorm] at hApp
                  exact ⟨(false, sExit), rfl, rfl, hSt, hApp⟩
                · simp only [hValOv, Bool.false_eq_true, ↓reduceIte] at hrVal ⊢
                  have hFlT : validFlagsSpec flags = true := by simpa using hValFl
                  have hSgT : validSignsSpec flags syncR inFd outFd errFd = true := by simpa using hValSg
                  have hOvT : validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds.val keepFds.val = true := by
                    simpa using hValOv
                  rw [hrVal]
                  refine okPost_bind (apply_set_pgid_spec s hRun flags) fun (r1, s1) hs1 => ?_
                  rcases hs1 with ⟨hRun1, hCfg1, hFds1, hDe1, hWl1, hCw1, hSig1, hBlk1, hPg1, hPgF1, hPgOr1,
                    ⟨suf1, hTr1, hNoRd1⟩⟩
                  by_cases hSess : (flagSet flags FLAG_SET_PGID && decide (s.pid > 0) && decide (s.pid = s.sid)) = true
                  · simp only [hSess, ↓reduceIte]
                    have hFlP : flagSet flags FLAG_SET_PGID = true := by
                      simp only [Bool.and_eq_true] at hSess; exact hSess.1.1
                    have hSessCond : decide (s.pid > 0 ∧ s.pid = s.sid) = true := by
                      simp only [Bool.and_eq_true, decide_eq_true_eq] at hSess ⊢
                      exact ⟨hSess.1.2, hSess.2⟩
                    have hR1 : r1 = .Err EPERM := by simpa [hSessCond] using hPgOr1 hOr hFlP
                    rw [hR1]
                    have hOr1 : s1.oracle = [] := hCfg1.oracle.trans hOr
                    have hRepFd1 : s1.getFd repW.val = some repEnt := by
                      simpa [ChildState.getFd, hFds1] using hRepFd
                    have hDesc1 : s1.getDesc repEnt.desc = .stream rd true false rem := by
                      simpa [ChildState.getDesc, hDe1] using hDesc
                    refine okPost_bind
                      (report_and_exit_bytes s1 hRun1 hOr1 repW _ _ _ hRepGe hRepFd1 hDesc1)
                      fun sExit ⟨hSt, hApp⟩ => ?_
                    have hNorm : normalizeErrnoSpec EPERM postfork.fd_ops.EIO = EPERM := by rfl
                    rw [child_stage_process_group_eq, hNorm, hWl1] at hApp
                    exact ⟨(false, sExit), rfl, rfl, hSt, hApp⟩
                  · have hSessF : (flagSet flags FLAG_SET_PGID && decide (s.pid > 0) && decide (s.pid = s.sid)) = false :=
                      Bool.eq_false_iff.mpr hSess
                    simp only [hSessF, Bool.false_eq_true, ↓reduceIte]
                    have hR1 : r1 = .Ok () := by
                      by_cases hFlP : flagSet flags FLAG_SET_PGID = true
                      · have hNot : decide (s.pid > 0 ∧ s.pid = s.sid) = false := by
                          rw [decide_eq_false_iff_not]
                          intro ⟨hGt, hb⟩
                          apply hSess
                          have hs0 : decide (s.pid > 0) = true := decide_eq_true hGt
                          rw [hFlP, hs0, hb]; simp
                        simpa [hNot] using hPgOr1 hOr hFlP
                      · exact hPgF1 (Bool.eq_false_iff.mpr hFlP)
                    rw [hR1]
                    rcases hPg1 hR1 with ⟨hPgT1, hPgF1'⟩
                    refine okPost_bind (apply_reset_sigpipe_spec s1 hRun1 flags) fun (r2, s2) hs2 => ?_
                    rcases hs2 with ⟨hRun2, hCfg2, hFds2, hDe2, hWl2, hCw2, hPg2, hSig2, hOr2,
                      ⟨suf2, hTr2, hNoRd2⟩⟩
                    have hOr1 : s1.oracle = [] := hCfg1.oracle.trans hOr
                    have hR2 : r2 = .Ok () := hOr2 hOr1
                    rw [hR2]
                    rcases hSig2 hR2 with ⟨hSpT2, hSpF2, hSpOth2⟩
                    refine okPost_bind
                      (okPost_and_dspec (close_unused_slice_safety s2 hRun2 closeFds)
                        (close_unused_slice_dspec_blockedSigs s2 closeFds))
                      fun s3 ⟨hs3, hBlk3⟩ => ?_
                    rcases hs3 with ⟨hRun3, hCfg3, hPg3, hCw3, hSig3, hDe3, hWl3, hLen3, hKeep3, hSec3,
                      ⟨suf3, hTr3, hEvs3, hClosed3⟩⟩
                    have hCfg20 : SameChildConfig s2 s := hCfg2.trans hCfg1
                    have hOr2' : s2.oracle = [] := hCfg20.oracle.trans hOr
                    have hNoSec2 : oracleHasSeccomp s2.oracle = false := by simp [oracleHasSeccomp, hOr2']
                    have hOr3 : s3.oracle = [] := hCfg3.oracle.trans hOr2'
                    have hFds20 : s2.fds = s.fds := hFds2.trans hFds1
                    have hGet20 : ∀ k, s2.getFd k = s.getFd k := fun k => by simp [ChildState.getFd, hFds20]
                    have hNotClRep : sliceContainsNonnegSpec closeFds.val repW.val = false := by
                      unfold validRunChildNoOverlap at hOvT
                      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hOvT
                      rcases hOvT with ⟨⟨⟨⟨hR, _⟩, _⟩, _⟩, _⟩
                      exact hR
                    have hRepFd3 : s3.getFd repW.val = some repEnt := by
                      rw [hKeep3 repW.val hNotClRep, hGet20 repW.val, hRepFd]
                    have hDe30 : s3.getDesc repEnt.desc = .stream rd true false rem := by
                      simpa [ChildState.getDesc, hDe3, hDe2, hDe1] using hDesc
                    have hSyncEqOpen : flagSet flags FLAG_HAS_SYNC_BARRIER = true →
                        s3.isOpen syncR.val = s.isOpen syncR.val := by
                      intro hFlagS
                      have hNotClS : sliceContainsNonnegSpec closeFds.val syncR.val = false := by
                        cases h : sliceContainsNonnegSpec closeFds.val syncR.val
                        · rfl
                        · unfold validRunChildNoOverlap at hOvT; simp [hFlagS, h] at hOvT
                      simp [ChildState.isOpen, hKeep3 syncR.val hNotClS, hGet20]
                    have hStdEqOpen : flagSet flags FLAG_REDIRECT_STDIO = true →
                        s3.isOpen inFd.val = s.isOpen inFd.val ∧
                        s3.isOpen outFd.val = s.isOpen outFd.val ∧
                        s3.isOpen errFd.val = s.isOpen errFd.val := by
                      intro hFlagR
                      have hNotI : sliceContainsNonnegSpec closeFds.val inFd.val = false := by
                        cases h : sliceContainsNonnegSpec closeFds.val inFd.val
                        · rfl
                        · unfold validRunChildNoOverlap at hOvT; simp [hFlagR, stdioInSliceSpec, h] at hOvT
                      have hNotO : sliceContainsNonnegSpec closeFds.val outFd.val = false := by
                        cases h : sliceContainsNonnegSpec closeFds.val outFd.val
                        · rfl
                        · unfold validRunChildNoOverlap at hOvT; simp [hFlagR, stdioInSliceSpec, h] at hOvT
                      have hNotE : sliceContainsNonnegSpec closeFds.val errFd.val = false := by
                        cases h : sliceContainsNonnegSpec closeFds.val errFd.val
                        · rfl
                        · unfold validRunChildNoOverlap at hOvT; simp [hFlagR, stdioInSliceSpec, h] at hOvT
                      exact ⟨by simp [ChildState.isOpen, hKeep3 _ hNotI, hGet20],
                        by simp [ChildState.isOpen, hKeep3 _ hNotO, hGet20],
                        by simp [ChildState.isOpen, hKeep3 _ hNotE, hGet20]⟩
                    have hKeepEqOpen : ∀ k ∈ keepFds.val, 0#i32 ≤ k → s3.isOpen k.val = s.isOpen k.val := by
                      intro k hk h0
                      have hNotOv : slicesOverlapNonnegSpec closeFds.val keepFds.val = false := by
                        cases h : slicesOverlapNonnegSpec closeFds.val keepFds.val
                        · rfl
                        · unfold validRunChildNoOverlap at hOvT; simp [h] at hOvT
                      have hNotClK : sliceContainsNonnegSpec closeFds.val k.val = false := by
                        by_contra hYes
                        have hYesT : sliceContainsNonnegSpec closeFds.val k.val = true := by
                          cases h : sliceContainsNonnegSpec closeFds.val k.val <;> simp_all
                        unfold sliceContainsNonnegSpec at hYesT
                        simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hYesT
                        rcases hYesT with ⟨_, c, hcm, hceq⟩
                        have hOvT' : slicesOverlapNonnegSpec closeFds.val keepFds.val = true := by
                          unfold slicesOverlapNonnegSpec
                          rw [List.any_eq_true]
                          refine ⟨c, hcm, ?_⟩
                          simp only [Bool.and_eq_true, decide_eq_true_eq]
                          refine ⟨by have := h0; omega, ?_⟩
                          unfold sliceContainsNonnegSpec
                          rw [Bool.and_eq_true, List.any_eq_true]
                          refine ⟨by rw [decide_eq_true_eq]; have := h0; omega, k, hk, by simp [hceq]⟩
                        rw [hOvT'] at hNotOv; cases hNotOv
                      simp [ChildState.isOpen, hKeep3 _ hNotClK, hGet20]
                    have hSignsSplit : (flagSet flags FLAG_HAS_SYNC_BARRIER = true → ¬ (syncR < 0#i32)) ∧
                        (flagSet flags FLAG_REDIRECT_STDIO = true →
                          ¬ (inFd < 0#i32) ∧ ¬ (outFd < 0#i32) ∧ ¬ (errFd < 0#i32)) := by
                      unfold validSignsSpec at hSgT
                      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
                        decide_eq_true_eq] at hSgT
                      refine ⟨fun h => ?_, fun h => ?_⟩
                      · rcases hSgT.1 with hf | h0
                        · rw [h] at hf; cases hf
                        · scalar_tac
                      · rcases hSgT.2 with hf | ⟨⟨h0, h1⟩, h2⟩
                        · rw [h] at hf; cases hf
                        · exact ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
                    refine okPost_bind (probe_sync_fd_spec s3 hRun3 flags syncR) fun (r3, s4) hs4 => ?_
                    rcases hs4 with ⟨hRun4, hCfg4, hFds4, hDe4, hWl4, hCw4, hPg4, hSig4, hBlk4, hOrR3,
                      ⟨suf4, hTr4, hNoRd4⟩⟩
                    have hWl30 : s3.writeLog = s.writeLog := hWl3.trans (hWl2.trans hWl1)
                    by_cases hFailSync : (flagSet flags FLAG_HAS_SYNC_BARRIER && !s.isOpen syncR.val) = true
                    · have hFlagS : flagSet flags FLAG_HAS_SYNC_BARRIER = true := by
                        simp only [Bool.and_eq_true] at hFailSync; exact hFailSync.1
                      have hFailSync3 : (flagSet flags FLAG_HAS_SYNC_BARRIER && !s3.isOpen syncR.val) = true := by
                        simpa [hSyncEqOpen hFlagS] using hFailSync
                      have hR3 : r3 = .Err EBADF := by simpa [hFailSync3] using hOrR3 hOr3
                      simp only [hFailSync, Bool.true_or]
                      rw [hR3]
                      have hOr4 : s4.oracle = [] := hCfg4.oracle.trans hOr3
                      have hRepFd4 : s4.getFd repW.val = some repEnt := by
                        simpa [ChildState.getFd, hFds4] using hRepFd3
                      have hDe40 : s4.getDesc repEnt.desc = .stream rd true false rem := by
                        simpa [ChildState.getDesc, hDe4] using hDe30
                      refine okPost_bind
                        (report_and_exit_bytes s4 hRun4 hOr4 repW _ _ _ hRepGe hRepFd4 hDe40)
                        fun sExit ⟨hSt, hApp⟩ => ?_
                      have hNorm : normalizeErrnoSpec EBADF postfork.fd_ops.EBADF = EBADF := by rfl
                      rw [child_stage_fd_setup_eq, hNorm, hWl4, hWl30] at hApp
                      exact ⟨(false, sExit), rfl, rfl, hSt, hApp⟩
                    · have hFailSyncF : (flagSet flags FLAG_HAS_SYNC_BARRIER && !s.isOpen syncR.val) = false :=
                        Bool.eq_false_iff.mpr hFailSync
                      have hFailSync3F : (flagSet flags FLAG_HAS_SYNC_BARRIER && !s3.isOpen syncR.val) = false := by
                        by_cases hFlagS : flagSet flags FLAG_HAS_SYNC_BARRIER = true
                        · simpa [hSyncEqOpen hFlagS] using hFailSyncF
                        · have hf : flagSet flags FLAG_HAS_SYNC_BARRIER = false := Bool.eq_false_iff.mpr hFlagS
                          simp [hf]
                      have hR3 : r3 = .Ok () := by simpa [hFailSync3F] using hOrR3 hOr3
                      rw [hR3]
                      have hOr4 : s4.oracle = [] := hCfg4.oracle.trans hOr3
                      refine okPost_bind (probe_redir_stdio_spec s4 hRun4 flags syncR inFd outFd errFd)
                        fun (r4, s5) hs5 => ?_
                      rcases hs5 with ⟨hRun5, hCfg5, hFds5, hDe5, hWl5, hCw5, hPg5, hSig5, hBlk5, _, hOrR4,
                        ⟨suf5, hTr5, hNoRd5⟩⟩
                      have hGet43 : ∀ k, s4.getFd k = s3.getFd k := fun k => by simp [ChildState.getFd, hFds4]
                      by_cases hFailStd : (flagSet flags FLAG_REDIRECT_STDIO &&
                          (!s.isOpen inFd.val || !s.isOpen outFd.val || !s.isOpen errFd.val)) = true
                      · have hFlagR : flagSet flags FLAG_REDIRECT_STDIO = true := by
                          simp only [Bool.and_eq_true] at hFailStd; exact hFailStd.1
                        have hEq3 := hStdEqOpen hFlagR
                        have hNegS := hSignsSplit.2 hFlagR
                        have hFailStd4 :
                            (flagSet flags FLAG_REDIRECT_STDIO &&
                              (inFd < 0#i32 || outFd < 0#i32 || errFd < 0#i32 ||
                                !s4.isOpen inFd.val || !s4.isOpen outFd.val || !s4.isOpen errFd.val)) = true := by
                          have h4op : (!s4.isOpen inFd.val || !s4.isOpen outFd.val || !s4.isOpen errFd.val) = true := by
                            simp only [ChildState.isOpen, hGet43] at *
                            simpa [hFlagR, hEq3.1, hEq3.2.1, hEq3.2.2] using hFailStd
                          simp only [Bool.and_eq_true, hFlagR, true_and]
                          simp only [Bool.or_eq_true] at h4op ⊢
                          rcases h4op with (h1 | h2) | h3
                          · left; left; right; exact h1
                          · left; right; exact h2
                          · right; exact h3
                        have hR4 : r4 = .Err EBADF := by
                          have h4' : (flagSet flags FLAG_REDIRECT_STDIO &&
                              (decide (inFd < 0#i32) || decide (outFd < 0#i32) || decide (errFd < 0#i32) ||
                                !s4.isOpen inFd.val || !s4.isOpen outFd.val || !s4.isOpen errFd.val)) = true :=
                            hFailStd4
                          have hOr4' := hOrR4 hOr4
                          rw [h4'] at hOr4'
                          simpa using hOr4'
                        simp only [hFailSyncF, Bool.false_or, hFailStd, Bool.true_or, ↓reduceIte]
                        rw [hR4]
                        have hOr5 : s5.oracle = [] := hCfg5.oracle.trans hOr4
                        have hRepFd5 : s5.getFd repW.val = some repEnt := by
                          simpa [ChildState.getFd, hFds5, hFds4] using hRepFd3
                        have hDe50 : s5.getDesc repEnt.desc = .stream rd true false rem := by
                          simpa [ChildState.getDesc, hDe5, hDe4] using hDe30
                        refine okPost_bind
                          (report_and_exit_bytes s5 hRun5 hOr5 repW _ _ _ hRepGe hRepFd5 hDe50)
                          fun sExit ⟨hSt, hApp⟩ => ?_
                        have hNorm : normalizeErrnoSpec EBADF postfork.fd_ops.EBADF = EBADF := by rfl
                        rw [child_stage_fd_setup_eq, hNorm, hWl5, hWl4, hWl30] at hApp
                        exact ⟨(false, sExit), rfl, rfl, hSt, hApp⟩
                      · have hFailStdF : (flagSet flags FLAG_REDIRECT_STDIO &&
                            (!s.isOpen inFd.val || !s.isOpen outFd.val || !s.isOpen errFd.val)) = false :=
                          Bool.eq_false_iff.mpr hFailStd
                        have hR4 : r4 = .Ok () := by
                          by_cases hFlagR : flagSet flags FLAG_REDIRECT_STDIO = true
                          · have hEq3 := hStdEqOpen hFlagR
                            have hNegS := hSignsSplit.2 hFlagR
                            simp only [hFlagR, Bool.true_and, Bool.or_eq_false_iff,
                              Bool.not_eq_false'] at hFailStdF
                            rcases hFailStdF with ⟨⟨h1, h2⟩, h3⟩
                            have hNotC : (flagSet flags FLAG_REDIRECT_STDIO &&
                                (decide (inFd < 0#i32) || decide (outFd < 0#i32) || decide (errFd < 0#i32) ||
                                  !s4.isOpen inFd.val || !s4.isOpen outFd.val || !s4.isOpen errFd.val)) = false := by
                              have ho1 : s4.isOpen inFd.val = true := by
                                unfold ChildState.isOpen; rw [hGet43]
                                change s3.isOpen inFd.val = true; rw [hEq3.1]; exact h1
                              have ho2 : s4.isOpen outFd.val = true := by
                                unfold ChildState.isOpen; rw [hGet43]
                                change s3.isOpen outFd.val = true; rw [hEq3.2.1]; exact h2
                              have ho3 : s4.isOpen errFd.val = true := by
                                unfold ChildState.isOpen; rw [hGet43]
                                change s3.isOpen errFd.val = true; rw [hEq3.2.2]; exact h3
                              have hi0 : decide (inFd < 0#i32) = false := decide_eq_false hNegS.1
                              have ho0 : decide (outFd < 0#i32) = false := decide_eq_false hNegS.2.1
                              have he0 : decide (errFd < 0#i32) = false := decide_eq_false hNegS.2.2
                              rw [hFlagR, hi0, ho0, he0, ho1, ho2, ho3]; decide
                            have hOr4' := hOrR4 hOr4
                            rw [hNotC] at hOr4'
                            simpa using hOr4'
                          · have hFlagRF : flagSet flags FLAG_REDIRECT_STDIO = false := Bool.eq_false_iff.mpr hFlagR
                            have hOr4' := hOrR4 hOr4
                            rw [hFlagRF, Bool.false_and] at hOr4'
                            simpa using hOr4'
                        rw [hR4]
                        have hOr5 : s5.oracle = [] := hCfg5.oracle.trans hOr4
                        refine okPost_bind (probe_open_slice_pre_spec s5 hRun5 syncR keepFds)
                          fun (r5, s6) hs6 => ?_
                        rcases hs6 with ⟨hRun6, hCfg6, hFds6, hDe6, hWl6, hCw6, hPg6, hSig6, hBlk6, _, hOrR5,
                          ⟨suf6, hTr6, hNoRd6⟩⟩
                        have hKeepAnyEq :
                            keepFds.val.any (fun k => decide (0#i32 ≤ k) && !s5.isOpen k.val) =
                            keepFds.val.any (fun k => decide (0#i32 ≤ k) && !s.isOpen k.val) := by
                          apply Bool.eq_iff_iff.mpr
                          simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
                          constructor
                          · rintro ⟨k, hk, h0, ho⟩
                            refine ⟨k, hk, h0, ?_⟩
                            have heq := hKeepEqOpen k hk h0
                            have h5s : s5.isOpen k.val = s3.isOpen k.val := by
                              simp only [ChildState.isOpen, ChildState.getFd, hFds5, hFds4]
                            rw [h5s, heq] at ho
                            exact ho
                          · rintro ⟨k, hk, h0, ho⟩
                            refine ⟨k, hk, h0, ?_⟩
                            have heq := hKeepEqOpen k hk h0
                            have h5s : s5.isOpen k.val = s3.isOpen k.val := by
                              simp only [ChildState.isOpen, ChildState.getFd, hFds5, hFds4]
                            rw [h5s, heq]
                            exact ho
                        by_cases hFailKeep :
                            keepFds.val.any (fun k => decide (0#i32 ≤ k) && !s.isOpen k.val) = true
                        · have hR5 : r5 = .Err EBADF := by
                            have h5' := hOrR5 hOr5
                            simp only [hKeepAnyEq, hFailKeep, ↓reduceIte] at h5'
                            exact h5'
                          simp only [hFailSyncF, hFailStdF, hFailKeep, Bool.false_or, ↓reduceIte]
                          rw [hR5]
                          have hOr6 : s6.oracle = [] := hCfg6.oracle.trans hOr5
                          have hRepFd6 : s6.getFd repW.val = some repEnt := by
                            simpa [ChildState.getFd, hFds6, hFds5, hFds4] using hRepFd3
                          have hDe60 : s6.getDesc repEnt.desc = .stream rd true false rem := by
                            simpa [ChildState.getDesc, hDe6, hDe5, hDe4] using hDe30
                          refine okPost_bind
                            (report_and_exit_bytes s6 hRun6 hOr6 repW _ _ _ hRepGe hRepFd6 hDe60)
                            fun sExit ⟨hSt, hApp⟩ => ?_
                          have hNorm : normalizeErrnoSpec EBADF postfork.fd_ops.EBADF = EBADF := by rfl
                          rw [child_stage_fd_setup_eq, hNorm, hWl6, hWl5, hWl4, hWl30] at hApp
                          exact ⟨(false, sExit), rfl, rfl, hSt, hApp⟩
                        · have hFailKeepF :
                              keepFds.val.any (fun k => decide (0#i32 ≤ k) && !s.isOpen k.val) = false :=
                            Bool.eq_false_iff.mpr hFailKeep
                          have hR5 : r5 = .Ok () := by
                            have := hOrR5 hOr5
                            rw [hKeepAnyEq, hFailKeepF] at this
                            simpa using this
                          simp only [hFailSyncF, hFailStdF, hFailKeepF, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
                          rw [hR5]
                          have hSyncOpen : flagSet flags FLAG_HAS_SYNC_BARRIER = true → s.isOpen syncR.val = true := by
                            intro hFlagS
                            by_contra hNo
                            apply hFailSync
                            rw [hFlagS, Bool.eq_false_iff.mpr hNo]; decide
                          have hStdOpen : flagSet flags FLAG_REDIRECT_STDIO = true →
                              s.isOpen inFd.val = true ∧ s.isOpen outFd.val = true ∧ s.isOpen errFd.val = true := by
                            intro hFlagR
                            simp only [hFlagR, Bool.true_and, Bool.or_eq_false_iff,
                              Bool.not_eq_false'] at hFailStdF
                            rcases hFailStdF with ⟨⟨h1, h2⟩, h3⟩
                            exact ⟨h1, h2, h3⟩
                          have hKeepOpen : ∀ k ∈ keepFds.val, 0#i32 ≤ k → s.isOpen k.val = true := by
                            intro k hk h0
                            rw [List.any_eq_false] at hFailKeepF
                            have hkF := hFailKeepF k hk
                            have hd0 : decide (0#i32 ≤ k) = true := decide_eq_true h0
                            rw [hd0, Bool.true_and] at hkF
                            simpa using hkF
                          have hSignSync : !(flagSet flags FLAG_HAS_SYNC_BARRIER) || decide (0#i32 ≤ syncR) = true := by
                            simpa [validSignsSpec] using (Bool.and_eq_true _ _ |>.mp hSgT).1
                          let tA : List Event := suf1 ++ suf2 ++ suf3 ++ suf4 ++ suf5 ++ suf6
                          have hTrA : s6.trace = s.trace ++ tA := by
                            rw [hTr6, hTr5, hTr4, hTr3, hTr2, hTr1]; simp only [tA, List.append_assoc]
                          have hNoRdA : ∀ ev ∈ tA, ev.req ≠ .read1 syncR := by
                            intro ev hev
                            simp only [tA, List.mem_append] at hev
                            rcases hev with ((((h1 | h2) | h3) | h4) | h5) | h6
                            · exact hNoRd1 ev h1 syncR
                            · exact hNoRd2 ev h2 syncR
                            · rcases hEvs3 ev h3 with ⟨fd, out, rfl⟩; simp
                            · exact hNoRd4 ev h4
                            · exact hNoRd5 ev h5
                            · exact hNoRd6 ev h6
                          have hClosedA : ∀ cfd ∈ closeFds.val, 0#i32 ≤ cfd → ∃ out, Event.mk (.close cfd) out ∈ tA := by
                            intro cfd hc h0
                            rcases hClosed3 cfd hc h0 with ⟨out, hout⟩
                            exact ⟨out, by simp [tA, hout]⟩
                          have hCfg60 : SameChildConfig s6 s :=
                            hCfg6.trans (hCfg5.trans (hCfg4.trans (hCfg3.trans (hCfg2.trans hCfg1))))
                          have hFds63 : s6.fds = s3.fds := hFds6.trans (hFds5.trans hFds4)
                          have hDe60 : s6.descs = s.descs :=
                            hDe6.trans (hDe5.trans (hDe4.trans (hDe3.trans (hDe2.trans hDe1))))
                          have hWl60 : s6.writeLog = s.writeLog :=
                            hWl6.trans (hWl5.trans (hWl4.trans (hWl3.trans (hWl2.trans hWl1))))
                          have hCw60 : s6.cwd = s.cwd :=
                            hCw6.trans (hCw5.trans (hCw4.trans (hCw3.trans (hCw2.trans hCw1))))
                          have hPg62 : s6.pgid = s2.pgid := hPg6.trans (hPg5.trans (hPg4.trans hPg3))
                          have hSig62 : s6.sig = s2.sig := hSig6.trans (hSig5.trans (hSig4.trans hSig3))
                          have hBlk62 : s6.blockedSigs = s2.blockedSigs :=
                            hBlk6.trans (hBlk5.trans (hBlk4.trans hBlk3))
                          have hLen6 : s6.fds.length ≤ s.fds.length := by
                            rw [hFds63]; exact hLen3.trans_eq (congrArg List.length hFds20)
                          refine okPost_mono (await_sync_barrier_spec s6 hRun6 flags syncR hSignSync)
                            fun (b, sOut) ⟨hOrTrue, hAw⟩ => ?_
                          have mkPreOk :
                              b = true →
                              (hAwB :
                                sOut.status = .running ∧ SameChildConfig sOut s6 ∧
                                sOut.pgid = s6.pgid ∧ sOut.cwd = s6.cwd ∧ sOut.sig = s6.sig ∧
                                sOut.blockedSigs = s6.blockedSigs ∧ sOut.writeLog = s6.writeLog ∧
                                (oracleHasSeccomp s6.oracle = false → sOut.fds.length ≤ s6.fds.length) ∧
                                (oracleHasSeccomp s6.oracle = false →
                                  flagSet flags FLAG_HAS_SYNC_BARRIER = true → sOut.isOpen syncR.val = false) ∧
                                (∀ k : Int, (k ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false) →
                                  sOut.getFd k = s6.getFd k) ∧
                                (∀ d rd rem, s6.getDesc d = .stream rd true false rem →
                                  ∃ rd' rem', sOut.getDesc d = .stream rd' true false rem') ∧
                                (flagSet flags FLAG_HAS_SYNC_BARRIER = false → sOut.descs = s6.descs) ∧
                                (∃ suf, sOut.trace = s6.trace ++ suf) ∧
                                (flagSet flags FLAG_HAS_SYNC_BARRIER = true →
                                  ∃ e writable broken byte rest,
                                    s6.getFd syncR.val = some e ∧
                                    s6.getDesc e.desc = .stream true writable broken (byte :: rest))) →
                              PreSyncOkPost s flags syncR inFd outFd errFd repW closeFds.val keepFds.val sOut := by
                            intro hb ⟨hRunOut, hCfgOut, hPgOut, hCwOut, hSigOut, hBlkOut, hWlOut,
                              hLenOut, hClosedOut, hOtherOut, hDeOut, hDeFOut, ⟨suf7, hTrOut⟩, _⟩
                            refine ⟨hRunOut, hCfgOut.trans hCfg60, hWlOut.trans hWl60, hCwOut.trans hCw60,
                              hFlT, hRepGe, hSgT, hOvT,
                              fun hNs => (hLenOut (by rw [hCfg60.oracle]; exact hNs)).trans hLen6,
                              fun ht => by rw [hPgOut, hPg62, hPg2]; exact hPgT1 ht,
                              fun hf => by rw [hPgOut, hPg62, hPg2]; exact hPgF1' hf,
                              fun ht => by
                                rcases hSpT2 ht with ⟨h13, hB13⟩
                                refine ⟨?_, by rw [hBlkOut, hBlk62, hB13, hBlk1]⟩
                                calc sOut.getSig 13 = s6.getSig 13 := by simp [ChildState.getSig, hSigOut]
                                  _ = s2.getSig 13 := by simp [ChildState.getSig, hSig62]
                                  _ = Disp.default := h13,
                              fun hf => by
                                rcases hSpF2 hf with ⟨h13, hB13⟩
                                refine ⟨?_, by rw [hBlkOut, hBlk62, hB13, hBlk1]⟩
                                calc sOut.getSig 13 = s6.getSig 13 := by simp [ChildState.getSig, hSigOut]
                                  _ = s2.getSig 13 := by simp [ChildState.getSig, hSig62]
                                  _ = s1.getSig 13 := h13
                                  _ = s.getSig 13 := by simp [ChildState.getSig, hSig1],
                              fun g hg => by
                                calc sOut.getSig g = s6.getSig g := by simp [ChildState.getSig, hSigOut]
                                  _ = s2.getSig g := by simp [ChildState.getSig, hSig62]
                                  _ = s1.getSig g := hSpOth2 g hg
                                  _ = s.getSig g := by simp [ChildState.getSig, hSig1],
                              fun k hk hNotCl => by
                                rw [hOtherOut k hk, ChildState.getFd, hFds63, ← ChildState.getFd,
                                  hKeep3 k hNotCl, hGet20 k],
                              fun hNs k => by
                                have hNs6 : oracleHasSeccomp s6.oracle = false := by
                                  rw [hCfg60.oracle]; exact hNs
                                have hNs2 : oracleHasSeccomp s2.oracle = false := by
                                  rw [hCfg20.oracle]; exact hNs
                                by_cases hSyncK : (flagSet flags FLAG_HAS_SYNC_BARRIER && k == syncR.val) = true
                                · simp only [Bool.and_eq_true, beq_iff_eq] at hSyncK
                                  rcases hSyncK with ⟨hFlagS', rfl⟩
                                  simp only [hFlagS', beq_self_eq_true, Bool.and_true, Bool.or_true, ↓reduceIte]
                                  have hNotOp := hClosedOut hNs6 hFlagS'
                                  cases hgk : sOut.getFd syncR.val with
                                  | none => rfl
                                  | some _ => simp [ChildState.isOpen, hgk] at hNotOp
                                · have hNotSync : k ≠ syncR.val ∨ flagSet flags FLAG_HAS_SYNC_BARRIER = false := by
                                    by_cases hFlagS' : flagSet flags FLAG_HAS_SYNC_BARRIER = true
                                    · left; intro heq; apply hSyncK; simp [hFlagS', heq]
                                    · right; exact Bool.eq_false_iff.mpr hFlagS'
                                  have hSyncKF : (flagSet flags FLAG_HAS_SYNC_BARRIER && k == syncR.val) = false :=
                                    Bool.eq_false_iff.mpr hSyncK
                                  simp only [hSyncKF, Bool.or_false]
                                  rw [hOtherOut k hNotSync, ChildState.getFd, hFds63,
                                    ← ChildState.getFd, hSec3 hNs2 k]
                                  split <;> simp [hGet20],
                              fun d rd0 rem0 hD => hDeOut d rd0 rem0 (by
                                unfold ChildState.getDesc at hD ⊢; rw [hDe60]; exact hD),
                              fun hf => by rw [hDeFOut hf, hDe60],
                              hStdOpen, hKeepOpen,
                              ⟨tA, suf7, by rw [hTrOut, hTrA, List.append_assoc], hNoRdA, hClosedA⟩⟩
                          by_cases hFlagS : flagSet flags FLAG_HAS_SYNC_BARRIER = true
                          · simp only [hFlagS, ↓reduceIte]
                            have hSyncS : s.isOpen syncR.val = true := hSyncOpen hFlagS
                            have hSyncS6 : s6.getFd syncR.val = s.getFd syncR.val := by
                              have hNotClS : sliceContainsNonnegSpec closeFds.val syncR.val = false := by
                                cases h : sliceContainsNonnegSpec closeFds.val syncR.val
                                · rfl
                                · unfold validRunChildNoOverlap at hOvT; simp [hFlagS, h] at hOvT
                              rw [ChildState.getFd, hFds63, ← ChildState.getFd, hKeep3 syncR.val hNotClS,
                                hGet20 syncR.val]
                            cases hSF : s.getFd syncR.val with
                            | none => change True; trivial
                            | some syncEnt =>
                              dsimp only
                              cases hSD : s.getDesc syncEnt.desc with
                              | directory _ | procSelfFd _ => change True; trivial
                              | stream sr sw sb srem =>
                                cases sr
                                · change True; trivial
                                · cases srem with
                                  | nil =>
                                    cases b
                                    · change false = false ∧ sOut.status = .exited 125#i32 ∧
                                        sOut.writeLog = s.writeLog ∧
                                        closedBeforeSyncRead (sOut.trace.drop s.trace.length) closeFds.val syncR
                                      rcases hAw with ⟨_, hSt125, hWlOut, _, _, ⟨suf7, hTrOut⟩⟩
                                      have hDrop : sOut.trace.drop s.trace.length = tA ++ suf7 := by
                                        rw [hTrOut, hTrA, List.append_assoc, List.drop_left]
                                      refine ⟨rfl, hSt125, hWlOut.trans hWl60, ?_⟩
                                      rw [hDrop]
                                      exact closedBeforeSyncRead_append hNoRdA hClosedA
                                    · exfalso
                                      rcases hAw.2.2.2.2.2.2.2.2.2.2.2.2.2 hFlagS with
                                        ⟨e', w', b', hd', tl', he', hde'⟩
                                      rw [hSyncS6, hSF] at he'; cases he'
                                      unfold ChildState.getDesc at hde'
                                      rw [hDe60] at hde'
                                      change s.getDesc syncEnt.desc = _ at hde'
                                      rw [hSD] at hde'; cases hde'
                                  | cons bhd btl =>
                                    cases b
                                    · exfalso
                                      have hTrue := hOrTrue (hCfg60.oracle.trans hOr) hFlagS
                                        ⟨syncEnt, sw, sb, bhd, btl, by rw [hSyncS6, hSF], by
                                          unfold ChildState.getDesc; rw [hDe60]; exact hSD⟩
                                      cases hTrue
                                    · change true = true ∧
                                        PreSyncOkPost s flags syncR inFd outFd errFd repW closeFds.val keepFds.val sOut ∧
                                        s.isOpen syncR.val = true ∧
                                        (flagSet flags FLAG_REDIRECT_STDIO = true →
                                          s.isOpen inFd.val = true ∧ s.isOpen outFd.val = true ∧ s.isOpen errFd.val = true) ∧
                                        (∀ k ∈ keepFds.val, 0#i32 ≤ k → s.isOpen k.val = true)
                                      exact ⟨rfl, mkPreOk rfl hAw, hSyncS, hStdOpen, hKeepOpen⟩
                          · have hFlagSF : flagSet flags FLAG_HAS_SYNC_BARRIER = false := Bool.eq_false_iff.mpr hFlagS
                            simp only [hFlagSF, Bool.false_eq_true, ↓reduceIte]
                            cases b
                            · exfalso
                              exact absurd (hAw.1.symm.trans hFlagSF) (by decide)
                            · exact ⟨rfl, mkPreOk rfl hAw, hStdOpen, hKeepOpen⟩
          · exact okPost_mono hSafety (fun _ _ => by simp [hDesc])

/-- Pre-exec continuation specification for `run_child_pre_sync` under valid execution preconditions. -/
theorem run_child_pre_sync_exec_ok
    (s : ChildState) (hRun : s.status = .running) (hOr : s.oracle = [])
    (flags : U32) (syncR inFd outFd errFd repW : I32) (closeFds keepFds : Slice I32)
    (hFl : validFlagsSpec flags = true)
    (hRepGe : 0#i32 ≤ repW)
    (hSg : validSignsSpec flags syncR inFd outFd errFd = true)
    (hOv : validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds.val keepFds.val = true)
    (hPgPre : flagSet flags FLAG_SET_PGID = true → s.pid > 0 ∧ s.pid ≠ s.sid)
    (hStdOpen : flagSet flags FLAG_REDIRECT_STDIO = true →
      s.isOpen inFd.val = true ∧ s.isOpen outFd.val = true ∧ s.isOpen errFd.val = true)
    (hKpOpen : ∀ k ∈ keepFds.val, 0#i32 ≤ k → s.isOpen k.val = true)
    (hSyncStream : flagSet flags FLAG_HAS_SYNC_BARRIER = true →
      ∃ es ws bs b rest,
        s.getFd syncR.val = some es ∧
        s.getDesc es.desc = .stream true ws bs (b :: rest)) :
    OkPost
      (postfork.child.run_child_pre_sync s flags syncR inFd outFd errFd repW closeFds keepFds)
      fun (b, sOut) =>
        b = true ∧ PreSyncOkPost s flags syncR inFd outFd errFd repW closeFds.val keepFds.val sOut := by
  have hTrue : OkPost
      (postfork.child.run_child_pre_sync s flags syncR inFd outFd errFd repW closeFds keepFds)
      fun (b, _) => b = true := by
    unfold postfork.child.run_child_pre_sync
    have hRepF : ¬ repW < 0#i32 := by scalar_tac
    simp only [hRepF, ↓reduceIte]
    refine okPost_bind (validate_child_args_spec flags syncR inFd outFd errFd repW closeFds keepFds)
      fun rVal hrVal => ?_
    have hFlF : (!validFlagsSpec flags) = false := by simp [hFl]
    have hSgF : (!validSignsSpec flags syncR inFd outFd errFd) = false := by simp [hSg]
    have hOvF : (!validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds.val keepFds.val) = false := by
      simp [hOv]
    simp only [hFlF, hSgF, hOvF, Bool.false_eq_true, ↓reduceIte] at hrVal
    rw [hrVal]
    refine okPost_bind (apply_set_pgid_spec s hRun flags) fun (r1, s1) hs1 => ?_
    rcases hs1 with ⟨hRun1, hCfg1, hFds1, hDe1, _, _, _, _, _, hPgF1, hPgOr1, _⟩
    have hR1 : r1 = .Ok () := by
      by_cases hPg : flagSet flags FLAG_SET_PGID = true
      · have hCond : decide (s.pid > 0 ∧ s.pid = s.sid) = false := by
          simp only [decide_eq_false_iff_not, not_and]
          exact fun _ => (hPgPre hPg).2
        simpa [hCond] using hPgOr1 hOr hPg
      · exact hPgF1 (Bool.eq_false_iff.mpr hPg)
    rw [hR1]
    have hOr1 : s1.oracle = [] := hCfg1.oracle.trans hOr
    refine okPost_bind (apply_reset_sigpipe_spec s1 hRun1 flags) fun (r2, s2) hs2 => ?_
    rcases hs2 with ⟨hRun2, hCfg2, hFds2, hDe2, _, _, _, _, hOrR2, _⟩
    rw [hOrR2 hOr1]
    have hOr2 : s2.oracle = [] := hCfg2.oracle.trans hOr1
    refine okPost_bind (close_unused_slice_safety s2 hRun2 closeFds) fun s3 hs3 => ?_
    rcases hs3 with ⟨hRun3, hCfg3, _, _, _, hDe3, _, _, hKeep3, _, _⟩
    have hOr3 : s3.oracle = [] := hCfg3.oracle.trans hOr2
    have hS3Eq : ∀ k, sliceContainsNonnegSpec closeFds.val k = false → s3.getFd k = s.getFd k := by
      intro k hk
      rw [hKeep3 k hk, ChildState.getFd, hFds2, hFds1]; rfl
    have hSyncNotCl : flagSet flags FLAG_HAS_SYNC_BARRIER = true →
        sliceContainsNonnegSpec closeFds.val syncR.val = false := by
      intro hS
      cases h : sliceContainsNonnegSpec closeFds.val syncR.val
      · rfl
      · unfold validRunChildNoOverlap at hOv; simp [hS, h] at hOv
    have hSignSync : !(flagSet flags FLAG_HAS_SYNC_BARRIER) || decide (0#i32 ≤ syncR) = true := by
      simpa [validSignsSpec] using (Bool.and_eq_true _ _ |>.mp hSg).1
    refine okPost_bind (probe_sync_fd_spec s3 hRun3 flags syncR) fun (r3, s4) hs4 => ?_
    rcases hs4 with ⟨hRun4, hCfg4, hFds4, hDe4, _, _, _, _, _, hOrR3, _⟩
    have hR3 : r3 = .Ok () := by
      rw [hOrR3 hOr3]
      by_cases hS : flagSet flags FLAG_HAS_SYNC_BARRIER = true
      · rcases hSyncStream hS with ⟨es, _, _, _, _, hSyncFd, _⟩
        have hOpS3 : s3.isOpen syncR.val = true := by
          rw [ChildState.isOpen, hS3Eq syncR.val (hSyncNotCl hS), hSyncFd]; rfl
        simp [hS, hOpS3]
      · simp [Bool.eq_false_iff.mpr hS]
    rw [hR3]
    have hOr4 : s4.oracle = [] := hCfg4.oracle.trans hOr3
    refine okPost_bind (probe_redir_stdio_spec s4 hRun4 flags syncR inFd outFd errFd)
      fun (r4, s5) hs5 => ?_
    rcases hs5 with ⟨hRun5, hCfg5, hFds5, hDe5, _, _, _, _, _, _, hOrR4, _⟩
    have hR4 : r4 = .Ok () := by
      by_cases hR : flagSet flags FLAG_REDIRECT_STDIO = true
      · have hSgR := (Bool.and_eq_true _ _ |>.mp hSg).2
        simp only [Bool.or_eq_true, Bool.not_eq_true', hR, Bool.and_eq_true,
          decide_eq_true_eq] at hSgR
        have hNoStdCl : stdioInSliceSpec closeFds.val inFd outFd errFd = false := by
          cases h : stdioInSliceSpec closeFds.val inFd outFd errFd
          · rfl
          · unfold validRunChildNoOverlap at hOv; simp [hR, h] at hOv
        have hClI : sliceContainsNonnegSpec closeFds.val inFd.val = false := by
          cases h : sliceContainsNonnegSpec closeFds.val inFd.val <;>
            first | rfl | (unfold stdioInSliceSpec at hNoStdCl; simp [h] at hNoStdCl)
        have hClO : sliceContainsNonnegSpec closeFds.val outFd.val = false := by
          cases h : sliceContainsNonnegSpec closeFds.val outFd.val <;>
            first | rfl | (unfold stdioInSliceSpec at hNoStdCl; simp [h] at hNoStdCl)
        have hClE : sliceContainsNonnegSpec closeFds.val errFd.val = false := by
          cases h : sliceContainsNonnegSpec closeFds.val errFd.val <;>
            first | rfl | (unfold stdioInSliceSpec at hNoStdCl; simp [h] at hNoStdCl)
        rcases hStdOpen hR with ⟨hOi, hOo, hOe⟩
        have hOi4 : s4.isOpen inFd.val = true := by
          rw [ChildState.isOpen, ChildState.getFd, hFds4, ← ChildState.getFd, hS3Eq _ hClI]; exact hOi
        have hOo4 : s4.isOpen outFd.val = true := by
          rw [ChildState.isOpen, ChildState.getFd, hFds4, ← ChildState.getFd, hS3Eq _ hClO]; exact hOo
        have hOe4 : s4.isOpen errFd.val = true := by
          rw [ChildState.isOpen, ChildState.getFd, hFds4, ← ChildState.getFd, hS3Eq _ hClE]; exact hOe
        rcases hSgR with hImp | ⟨⟨hGeI, hGeO⟩, hGeE⟩
        · cases hImp
        have hni : decide (inFd < 0#i32) = false :=
          decide_eq_false (show ¬ inFd.val < 0 from by have : 0 ≤ inFd.val := hGeI; omega)
        have hno : decide (outFd < 0#i32) = false :=
          decide_eq_false (show ¬ outFd.val < 0 from by have : 0 ≤ outFd.val := hGeO; omega)
        have hne : decide (errFd < 0#i32) = false :=
          decide_eq_false (show ¬ errFd.val < 0 from by have : 0 ≤ errFd.val := hGeE; omega)
        rw [hOrR4 hOr4]
        simp only [hR, hni, hno, hne, hOi4, hOo4, hOe4, Bool.not_true, Bool.false_or, Bool.and_false,
          Bool.false_eq_true, ↓reduceIte]
      · simp [hOrR4 hOr4, Bool.eq_false_iff.mpr hR]
    rw [hR4]
    have hOr5 : s5.oracle = [] := hCfg5.oracle.trans hOr4
    refine okPost_bind (probe_open_slice_pre_spec s5 hRun5 syncR keepFds) fun (r5, s6) hs6 => ?_
    rcases hs6 with ⟨hRun6, hCfg6, hFds6, hDe6, _, _, _, _, _, _, hOrR5, _⟩
    have hR5 : r5 = .Ok () := by
      have hNone : keepFds.val.any (fun k => decide (0#i32 ≤ k) && !s5.isOpen k.val) = false := by
        rw [List.any_eq_false]
        intro k hk hBad
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hBad
        have hNotCl : sliceContainsNonnegSpec closeFds.val k.val = false := by
          by_contra hc
          simp only [Bool.not_eq_false, sliceContainsNonnegSpec, Bool.and_eq_true,
            decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hc
          rcases hc with ⟨_, c, hcM, hcEq⟩
          have hOvl : slicesOverlapNonnegSpec closeFds.val keepFds.val = true := by
            rw [slicesOverlapNonnegSpec, List.any_eq_true]
            exact ⟨c, hcM, by
              simp only [Bool.and_eq_true, decide_eq_true_eq, sliceContainsNonnegSpec, List.any_eq_true, beq_iff_eq]
              exact ⟨show 0 ≤ c.val from hcEq ▸ hBad.1, show 0 ≤ c.val from hcEq ▸ hBad.1, k, hk, hcEq.symm⟩⟩
          unfold validRunChildNoOverlap at hOv
          simp [hOvl] at hOv
        have hOp5 : s5.isOpen k.val = true := by
          rw [ChildState.isOpen, ChildState.getFd, hFds5, hFds4, ← ChildState.getFd, hS3Eq _ hNotCl]
          exact hKpOpen k hk hBad.1
        rw [hOp5] at hBad
        exact Bool.false_ne_true hBad.2.symm
      rw [hOrR5 hOr5, hNone]
      rfl
    rw [hR5]
    have hOr6 : s6.oracle = [] := hCfg6.oracle.trans hOr5
    refine okPost_mono (await_sync_barrier_spec s6 hRun6 flags syncR hSignSync)
      fun (b, _) ⟨hBTrue, hAw⟩ => ?_
    by_cases hS : flagSet flags FLAG_HAS_SYNC_BARRIER = true
    · rcases hSyncStream hS with ⟨es, ws, bs, hd, rest, hFd, hDesc⟩
      have hFd6 : s6.getFd syncR.val = some es := by
        rw [ChildState.getFd, hFds6, hFds5, hFds4, ← ChildState.getFd, hS3Eq _ (hSyncNotCl hS), hFd]
      have hDe6' : s6.getDesc es.desc = .stream true ws bs (hd :: rest) := by
        rw [ChildState.getDesc, hDe6, hDe5, hDe4, hDe3, hDe2, hDe1]
        exact hDesc
      exact hBTrue hOr6 hS ⟨es, ws, bs, hd, rest, hFd6, hDe6'⟩
    · cases b
      · exfalso
        exact absurd (hAw.1.symm.trans (Bool.eq_false_iff.mpr hS)) (by decide)
      · rfl
  refine okPost_mono
    (okPost_and hTrue (run_child_pre_sync_safety s hRun flags syncR inFd outFd errFd repW closeFds keepFds))
    fun (b, sOut) ⟨hb, hSafe⟩ => ?_
  subst hb
  exact ⟨rfl, hSafe⟩

/-- Non-running totality for `postfork.child.run_child_pre_sync`. -/
theorem run_child_pre_sync_total
    (s : ChildState) (flags : U32) (syncR inFd outFd errFd repW : I32) (closeFds keepFds : Slice I32) :
    OkPost (postfork.child.run_child_pre_sync s flags syncR inFd outFd errFd repW closeFds keepFds)
      (fun _ => True) := by
  by_cases hRun : s.status = .running
  · exact okPost_mono
      (run_child_pre_sync_safety s hRun flags syncR inFd outFd errFd repW closeFds keepFds)
      fun _ _ => trivial
  · have hPgidTot : ∀ x, OkPost (postfork.child.apply_set_pgid x flags) (fun _ => True) := fun x => by
      unfold postfork.child.apply_set_pgid
      simp only [lift, Aeneas.Std.lift, bind_ok]
      split <;> [exact okPost_mono (sys_setpgid_self_total x) (fun _ _ => trivial); exact ⟨_, rfl, trivial⟩]
    have hSigTot : ∀ x, OkPost (postfork.child.apply_reset_sigpipe x flags) (fun _ => True) := fun x => by
      unfold postfork.child.apply_reset_sigpipe
      simp only [lift, Aeneas.Std.lift, bind_ok]
      split
      · refine okPost_bind (sys_sig_dfl_total x postfork.child.SIGPIPE) fun (r, x1) _ => ?_
        cases r with
        | Ok _ => exact okPost_mono (sys_sig_unblock_total x1 postfork.child.SIGPIPE) fun _ _ => trivial
        | Err _ => exact ⟨_, rfl, trivial⟩
      · exact ⟨_, rfl, trivial⟩
    have hPrSyncTot : ∀ x, OkPost (postfork.child.probe_sync_fd x flags syncR) (fun _ => True) := fun x => by
      unfold postfork.child.probe_sync_fd
      simp only [lift, Aeneas.Std.lift, bind_ok]
      split
      · have hGetTot : OkPost (sys.fcntl_getfd x syncR) (fun _ => True) := by
          by_cases hxRun : x.status = .running
          · obtain ⟨r, x', hEq, _⟩ := sys_fcntl_getfd_running x hxRun syncR
            exact ⟨(r, x'), hEq, trivial⟩
          · unfold sys.fcntl_getfd
            cases x.getFd syncR.val <;>
              (dsimp only; rw [runI32Syscall_not_running x hxRun]; exact ⟨_, rfl, trivial⟩)
        refine okPost_bind hGetTot fun (r, x1) _ => ?_
        cases r <;> exact ⟨_, rfl, trivial⟩
      · exact ⟨_, rfl, trivial⟩
    have hPrStdTot : ∀ x, OkPost (postfork.child.probe_redir_stdio x flags inFd outFd errFd) (fun _ => True) :=
      fun x => by
        unfold postfork.child.probe_redir_stdio
        simp only [lift, Aeneas.Std.lift, bind_ok]
        split <;> [exact okPost_mono (probe_stdio_open_total x inFd outFd errFd) fun _ _ => trivial;
          exact ⟨_, rfl, trivial⟩]
    have hAwTot : ∀ x, OkPost (postfork.child.await_sync_barrier x flags syncR) (fun _ => True) := fun x => by
      unfold postfork.child.await_sync_barrier
      simp only [lift, Aeneas.Std.lift, bind_ok]
      split
      · refine okPost_bind (read_sync_byte_total x syncR) fun ⟨b, s1⟩ _ => ?_
        cases b
        · exact okPost_bind (sys_exit_total s1 _) fun _ _ => ⟨_, rfl, trivial⟩
        · exact ⟨_, rfl, trivial⟩
      · exact ⟨_, rfl, trivial⟩
    unfold postfork.child.run_child_pre_sync
    by_cases hRep : repW < 0#i32
    · simp only [hRep, ↓reduceIte, child_exit_exec_failed_eq]
      exact okPost_bind (sys_exit_total s 127#i32) fun _ _ => ⟨_, rfl, trivial⟩
    · simp only [hRep, ↓reduceIte]
      refine okPost_bind (validate_child_args_spec flags syncR inFd outFd errFd repW closeFds keepFds)
        fun rVal _ => ?_
      cases rVal with
      | Err _ => exact okPost_bind (report_and_exit_total s repW _ _ _) fun _ _ => ⟨_, rfl, trivial⟩
      | Ok _ =>
        refine okPost_bind (hPgidTot s) fun (r1, s1) _ => ?_
        cases r1 with
        | Err _ => exact okPost_bind (report_and_exit_total s1 repW _ _ _) fun _ _ => ⟨_, rfl, trivial⟩
        | Ok _ =>
          refine okPost_bind (hSigTot s1) fun (r2, s2) _ => ?_
          cases r2 with
          | Err _ => exact okPost_bind (report_and_exit_total s2 repW _ _ _) fun _ _ => ⟨_, rfl, trivial⟩
          | Ok _ =>
            refine okPost_bind (close_unused_slice_total s2 closeFds) fun s3 _ => ?_
            refine okPost_bind (hPrSyncTot s3) fun (r3, s4) _ => ?_
            cases r3 with
            | Err _ => exact okPost_bind (report_and_exit_total s4 repW _ _ _) fun _ _ => ⟨_, rfl, trivial⟩
            | Ok _ =>
              refine okPost_bind (hPrStdTot s4) fun (r4, s5) _ => ?_
              cases r4 with
              | Err _ => exact okPost_bind (report_and_exit_total s5 repW _ _ _) fun _ _ => ⟨_, rfl, trivial⟩
              | Ok _ =>
                refine okPost_bind (probe_open_slice_total s5 keepFds) fun (r5, s6) _ => ?_
                cases r5 with
                | Err _ => exact okPost_bind (report_and_exit_total s6 repW _ _ _) fun _ _ => ⟨_, rfl, trivial⟩
                | Ok _ => exact hAwTot s6

end PreSyncSteps

end LeanSwe.PostFork.Proofs
