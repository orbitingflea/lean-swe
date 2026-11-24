import LeanSwe.Process.Types
import LeanSwe.Process.Impl
import LeanSwe.Process.Proofs.SysBridge

/-!
Core `run` specification and `validateRequest` normalization lemmas over any `RawProcessOpsM`
satisfying `RawProcessLaws`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.Process

/-- Monadic bind unfolding helper for `StateM`. -/
theorem stateT_bind_run {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := by
  dsimp only [StateT.run, Bind.bind, StateT.bind]
  cases x s
  rfl

/-- Every error returned by `Internal.validateRequest` has kind `.invalidInput` and a non-empty message. -/
theorem validateRequest_err_spec (req : ExecRequest) (err : ProcessError)
    (h : Internal.validateRequest req = .error err) :
    err.kind = .invalidInput ∧ err.message ≠ "" := by
  unfold Internal.validateRequest at h
  by_cases h1 : req.program.isEmpty = true
  · rw [ite_eq_left h1, Except.error.injEq] at h; subst h; exact ⟨rfl, by simp⟩
  · rw [ite_eq_right h1] at h
    by_cases h2 : Internal.hasNul req.program = true
    · rw [ite_eq_left h2, Except.error.injEq] at h; subst h; exact ⟨rfl, by simp⟩
    · rw [ite_eq_right h2] at h
      by_cases h3 : req.args.toList.any Internal.hasNul = true
      · rw [ite_eq_left h3, Except.error.injEq] at h; subst h; exact ⟨rfl, by simp⟩
      · rw [ite_eq_right h3] at h
        cases hcwd : req.cwd with
        | none =>
          simp only [hcwd, Bool.false_eq_true, ↓reduceIte] at h
          by_cases h5 : req.env.toList.any Internal.isInvalidEnvEntry = true
          · rw [ite_eq_left h5, Except.error.injEq] at h; subst h; exact ⟨rfl, by simp⟩
          · rw [ite_eq_right h5] at h
            by_cases h6 : (req.timeoutMs == some 0) = true
            · rw [ite_eq_left h6, Except.error.injEq] at h; subst h; exact ⟨rfl, by simp⟩
            · rw [ite_eq_right h6] at h; cases h
        | some d =>
          simp only [hcwd] at h
          by_cases h4 : Internal.hasNul d = true
          · rw [ite_eq_left h4, Except.error.injEq] at h; subst h; exact ⟨rfl, by simp⟩
          · rw [ite_eq_right h4] at h
            by_cases h5 : req.env.toList.any Internal.isInvalidEnvEntry = true
            · rw [ite_eq_left h5, Except.error.injEq] at h; subst h; exact ⟨rfl, by simp⟩
            · rw [ite_eq_right h5] at h
              by_cases h6 : (req.timeoutMs == some 0) = true
              · rw [ite_eq_left h6, Except.error.injEq] at h; subst h; exact ⟨rfl, by simp⟩
              · rw [ite_eq_right h6] at h; cases h

private theorem validateRequest_ok_fields_preserved {req norm : ExecRequest}
    (h : Internal.validateRequest req = .ok norm) :
    norm.program = req.program ∧
    norm.timeoutMs = req.timeoutMs ∧
    norm.maxOutputBytes = req.maxOutputBytes := by
  unfold Internal.validateRequest at h
  repeat (first | (rw [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩) | split at h | cases h)

private theorem ensureNonEmpty_msg_and_kind (fb : String) (err : ProcessError) (hfb : fb ≠ "") :
    (Internal.ensureNonEmptyMsg fb err).message ≠ "" ∧
    (Internal.ensureNonEmptyMsg fb err).kind = err.kind := by
  unfold Internal.ensureNonEmptyMsg
  split
  · exact ⟨hfb, rfl⟩
  · next h =>
    refine ⟨?_, rfl⟩
    intro hem
    rw [hem] at h
    simp [String.isEmpty] at h

/-- Master behavioral and FD-conservation specification of `Internal.run raw` for any `raw` satisfying `RawProcessLaws openFds`. -/
theorem run_spec_of_RawProcessLaws {S fd : Type} {raw : RawProcessOpsM (StateM S)}
    (openFds : S → List fd) (hLaws : RawProcessLaws openFds raw) (s₀ : S) (req : ExecRequest) :
    let r := (Internal.run raw req).run s₀
    (raw.activeProcessCount.run r.2).1 = (raw.activeProcessCount.run s₀).1 ∧
    openFds r.2 = openFds s₀ ∧
    (∀ err, r.1 = .error err →
      err.message ≠ "" ∧
      (err.kind = .timedOut → req.timeoutMs.isSome = true ∧ err.program = some req.program) ∧
      (err.kind = .outputLimitExceeded → req.maxOutputBytes.isSome = true ∧ err.program = some req.program) ∧
      (err.kind = .terminatedBySignal → err.program = some req.program ∧ err.signal ≠ none)) ∧
    (∀ out, r.1 = .ok out →
      ∀ lim, req.maxOutputBytes = some lim → out.stdout.size + out.stderr.size ≤ lim) := by
  dsimp only
  unfold Internal.run
  cases hVal : Internal.validateRequest req with
  | error verr =>
    dsimp only [pure, StateT.pure, StateT.run]
    obtain ⟨hk, hm⟩ := validateRequest_err_spec req verr hVal
    refine ⟨rfl, rfl, ?_, (by intro _ h; cases h)⟩
    intro err hEq; injection hEq with hE; rw [← hE]
    refine ⟨hm, ?_, ?_, ?_⟩ <;> (intro hBad; rw [hk] at hBad; cases hBad)
  | ok norm =>
    obtain ⟨hProg, hToEq, hMaxEq⟩ := validateRequest_ok_fields_preserved hVal
    dsimp only
    rw [stateT_bind_run]
    cases hSp : (raw.spawn norm).run s₀ with
    | mk spRes s₁ =>
      cases spRes with
      | error spErr =>
        dsimp only [pure, StateT.pure, StateT.run]
        have hSpE := hLaws.spawn_err s₀ norm spErr (by rw [hSp])
        rw [hSp] at hSpE
        obtain ⟨hCnt, hOpen, _, hk1, hk2, hk3⟩ := hSpE
        obtain ⟨hMsg', hKind'⟩ := ensureNonEmpty_msg_and_kind "process spawn failed" spErr (by decide)
        refine ⟨hCnt, hOpen, ?_, (by intro _ h; cases h)⟩
        intro err hEq; injection hEq with hE; rw [← hE]
        refine ⟨hMsg', ?_, ?_, ?_⟩
        · intro hk; exact absurd (hKind'.symm.trans hk) hk1
        · intro hk; exact absurd (hKind'.symm.trans hk) hk2
        · intro hk; exact absurd (hKind'.symm.trans hk) hk3
      | ok h =>
        dsimp only
        obtain ⟨_, _, hAwErr, hAwEx, hAwSig, hAwTo, hAwLim⟩ := hLaws.spawn_lifecycle s₀ norm h s₁ hSp
        rw [stateT_bind_run]
        let aw := (raw.awaitOutput h norm.stdin norm.timeoutMs norm.maxOutputBytes).run s₁
        cases hAwFst : aw.1 with
        | error awErr =>
          dsimp only
          rw [stateT_bind_run, stateT_bind_run]
          dsimp only [pure, StateT.pure, StateT.run]
          obtain ⟨hk1, hk2, hk3, hCnt, hOpen⟩ := hAwErr awErr hAwFst
          obtain ⟨hMsg', hKind'⟩ := ensureNonEmpty_msg_and_kind "process I/O failed" awErr (by decide)
          refine ⟨hCnt, hOpen, ?_, (by intro _ h; cases h)⟩
          intro err hEq; injection hEq with hE; rw [← hE]
          refine ⟨hMsg', ?_, ?_, ?_⟩
          · intro hk; exact absurd (hKind'.symm.trans hk) hk1
          · intro hk; exact absurd (hKind'.symm.trans hk) hk2
          · intro hk; exact absurd (hKind'.symm.trans hk) hk3
        | ok outcome =>
          cases outcome with
          | exited res =>
            dsimp only
            rw [stateT_bind_run]
            obtain ⟨hCap, hCnt, hOpen, hRpErr⟩ := hAwEx res hAwFst
            cases hRp : ((raw.reap h).run aw.2).1 with
            | error rpErr =>
              dsimp only [pure, StateT.pure, StateT.run]
              obtain ⟨hk1, hk2, hk3⟩ := hRpErr rpErr hRp
              obtain ⟨hMsg', hKind'⟩ := ensureNonEmpty_msg_and_kind "process reap failed" rpErr (by decide)
              refine ⟨hCnt, hOpen, ?_, (by intro _ h; cases h)⟩
              intro err hEq; injection hEq with hE; rw [← hE]
              refine ⟨hMsg', ?_, ?_, ?_⟩
              · intro hk; exact absurd (hKind'.symm.trans hk) hk1
              · intro hk; exact absurd (hKind'.symm.trans hk) hk2
              · intro hk; exact absurd (hKind'.symm.trans hk) hk3
            | ok u =>
              dsimp only [pure, StateT.pure, StateT.run]
              refine ⟨hCnt, hOpen, (by intro _ h; cases h), ?_⟩
              intro out hEq lim hLim
              injection hEq with hO; rw [← hO]
              exact hCap lim (hMaxEq.trans hLim)
          | signaled sig outB errB =>
            dsimp only
            rw [stateT_bind_run, stateT_bind_run]
            dsimp only [pure, StateT.pure, StateT.run]
            obtain ⟨hCnt, hOpen⟩ := hAwSig sig outB errB hAwFst
            refine ⟨hCnt, hOpen, ?_, (by intro _ h; cases h)⟩
            intro err hEq; injection hEq with hE; rw [← hE]
            refine ⟨(by simp [String.append_eq_empty_iff, toString]),
              (by intro hk; cases hk),
              (by intro hk; cases hk),
              fun _ => ⟨by simp [hProg], by simp⟩⟩
          | timedOut outB errB =>
            dsimp only
            rw [stateT_bind_run, stateT_bind_run]
            dsimp only [pure, StateT.pure, StateT.run]
            obtain ⟨hSome, hCnt, hOpen⟩ := hAwTo outB errB hAwFst
            rw [hToEq] at hSome
            refine ⟨hCnt, hOpen, ?_, (by intro _ h; cases h)⟩
            intro err hEq; injection hEq with hE; rw [← hE]
            refine ⟨(by simp [String.append_eq_empty_iff, toString]),
              fun _ => ⟨hSome, by simp [hProg]⟩,
              (by intro hk; cases hk),
              (by intro hk; cases hk)⟩
          | outputLimitExceeded outB errB =>
            dsimp only
            rw [stateT_bind_run, stateT_bind_run]
            dsimp only [pure, StateT.pure, StateT.run]
            obtain ⟨hSome, _, hCnt, hOpen⟩ := hAwLim outB errB hAwFst
            rw [hMaxEq] at hSome
            refine ⟨hCnt, hOpen, ?_, (by intro _ h; cases h)⟩
            intro err hEq; injection hEq with hE; rw [← hE]
            refine ⟨(by simp [String.append_eq_empty_iff, toString]),
              (by intro hk; cases hk),
              fun _ => ⟨hSome, by simp [hProg]⟩,
              (by intro hk; cases hk)⟩

private def noDupEnvKeys : List (String × Option String) → Prop
  | [] => True
  | kv :: rest => rest.any (fun p => p.1 == kv.1) = false ∧ noDupEnvKeys rest

private theorem mem_dedupEnv {xs : List (String × Option String)} {x : String × Option String}
    (hx : x ∈ Internal.dedupEnvList xs) : x ∈ xs := by
  induction xs with
  | nil => simp [Internal.dedupEnvList] at hx
  | cons kv rest ih =>
    simp only [Internal.dedupEnvList] at hx
    split at hx
    · exact List.mem_cons_of_mem kv (ih hx)
    · rcases List.mem_cons.mp hx with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem kv (ih hr)

private theorem noDupEnvKeys_dedup (xs : List (String × Option String)) :
    noDupEnvKeys (Internal.dedupEnvList xs) := by
  induction xs with
  | nil => trivial
  | cons kv rest ih =>
    simp only [Internal.dedupEnvList]
    split
    · exact ih
    · next h =>
      refine ⟨?_, ih⟩
      cases hAny : (Internal.dedupEnvList rest).any (fun p => p.1 == kv.1)
      · rfl
      · exact absurd hAny h

private theorem dedupEnv_idempotent (xs : List (String × Option String)) :
    Internal.dedupEnvList (Internal.dedupEnvList xs) = Internal.dedupEnvList xs := by
  suffices ∀ ys, noDupEnvKeys ys → Internal.dedupEnvList ys = ys from
    this _ (noDupEnvKeys_dedup xs)
  intro ys h
  induction ys with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨hnot, hrest⟩ := h
    simp [Internal.dedupEnvList, ih hrest, hnot]

/-- `Internal.validateRequest` is idempotent on accepted requests. -/
theorem validateRequest_idempotent_ok {req norm : ExecRequest}
    (h : Internal.validateRequest req = .ok norm) :
    Internal.validateRequest norm = .ok norm := by
  unfold Internal.validateRequest at h
  by_cases h1 : req.program.isEmpty = true
  · rw [ite_eq_left h1] at h; cases h
  · rw [ite_eq_right h1] at h
    by_cases h2 : Internal.hasNul req.program = true
    · rw [ite_eq_left h2] at h; cases h
    · rw [ite_eq_right h2] at h
      by_cases h3 : req.args.toList.any Internal.hasNul = true
      · rw [ite_eq_left h3] at h; cases h
      · rw [ite_eq_right h3] at h
        have h1f := Bool.eq_false_iff.mpr h1
        have h2f := Bool.eq_false_iff.mpr h2
        have h3f := Bool.eq_false_iff.mpr h3
        cases hcwd : req.cwd with
        | none =>
          simp only [hcwd, Bool.false_eq_true, ↓reduceIte] at h
          by_cases h5 : req.env.toList.any Internal.isInvalidEnvEntry = true
          · rw [ite_eq_left h5] at h; cases h
          · rw [ite_eq_right h5] at h
            by_cases h6 : (req.timeoutMs == some 0) = true
            · rw [ite_eq_left h6] at h; cases h
            · rw [ite_eq_right h6, Except.ok.injEq] at h
              subst h
              have h5f := Bool.eq_false_iff.mpr h5
              have h6f := Bool.eq_false_iff.mpr h6
              have h5' : ((Internal.dedupEnvList req.env.toList).toArray).toList.any Internal.isInvalidEnvEntry = false := by
                have hArr : ((Internal.dedupEnvList req.env.toList).toArray).toList =
                    Internal.dedupEnvList req.env.toList := by simp
                rw [hArr, List.any_eq_false]
                intro x hx
                exact List.any_eq_false.mp h5f x (mem_dedupEnv hx)
              simp [Internal.validateRequest, h1f, h2f, h3f, h5', h6f, dedupEnv_idempotent]
        | some d =>
          simp only [hcwd] at h
          by_cases h4 : Internal.hasNul d = true
          · rw [ite_eq_left h4] at h; cases h
          · rw [ite_eq_right h4] at h
            by_cases h5 : req.env.toList.any Internal.isInvalidEnvEntry = true
            · rw [ite_eq_left h5] at h; cases h
            · rw [ite_eq_right h5] at h
              by_cases h6 : (req.timeoutMs == some 0) = true
              · rw [ite_eq_left h6] at h; cases h
              · rw [ite_eq_right h6, Except.ok.injEq] at h
                subst h
                have h4f := Bool.eq_false_iff.mpr h4
                have h5f := Bool.eq_false_iff.mpr h5
                have h6f := Bool.eq_false_iff.mpr h6
                have h5' : ((Internal.dedupEnvList req.env.toList).toArray).toList.any Internal.isInvalidEnvEntry = false := by
                  have hArr : ((Internal.dedupEnvList req.env.toList).toArray).toList =
                      Internal.dedupEnvList req.env.toList := by simp
                  rw [hArr, List.any_eq_false]
                  intro x hx
                  exact List.any_eq_false.mp h5f x (mem_dedupEnv hx)
                simp [Internal.validateRequest, h1f, h2f, h3f, h4f, h5', h6f, dedupEnv_idempotent]

end LeanSwe.Process.Proofs
