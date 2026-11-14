import LeanSwe.Process.Types
import LeanSwe.Process.Interface
import LeanSwe.Process.Impl
import LeanSwe.Process.SpecTests
import LeanSwe.Process.Raw.Impl

namespace LeanSwe.Process.Proofs

open Core
open Core.NondetTest
open LeanSwe.Process

private theorem nonEmptyMsg_ne_empty (fallback msg : String) (hf : fallback ≠ "") :
    Raw.Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Raw.Internal.nonEmptyMsg
  split
  · exact hf
  · next h =>
    intro hem
    subst hem
    simp [String.isEmpty] at h

private theorem append_head_ne_empty (pre rest : String) (hp : pre ≠ "") :
    pre ++ rest ≠ "" := by
  simp [String.append_eq_empty_iff, hp]

private theorem isEmpty_true_of_eq_empty {s : String} (h : s = "") : s.isEmpty = true := by
  subst h
  rfl

private theorem isEmpty_false_of_ne_empty {s : String} (h : s ≠ "") : s.isEmpty = false := by
  simp [String.isEmpty, h]

private theorem hasNul_eq_false_of_not_mem {s : String} (h : '\x00' ∉ s.toList) :
    Internal.hasNul s = false := by
  simp [Internal.hasNul, h]

private theorem hasNul_eq_true_of_mem {s : String} (h : '\x00' ∈ s.toList) :
    Internal.hasNul s = true := by
  simp [Internal.hasNul, h]

private theorem mem_dedupEnvList {xs : List (String × Option String)} {x : String × Option String}
    (hx : x ∈ Internal.dedupEnvList xs) : x ∈ xs := by
  induction xs with
  | nil => simp [Internal.dedupEnvList] at hx
  | cons kv rest ih =>
    simp only [Internal.dedupEnvList] at hx
    split at hx
    · exact List.mem_cons_of_mem kv (ih hx)
    · rcases List.mem_cons.mp hx with rfl | hrest
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem kv (ih hrest)

private def noDupKeys : List (String × Option String) → Prop
  | [] => True
  | kv :: rest => rest.any (fun p => p.1 == kv.1) = false ∧ noDupKeys rest

private theorem noDupKeys_dedupEnvList (xs : List (String × Option String)) :
    noDupKeys (Internal.dedupEnvList xs) := by
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

private theorem dedupEnvList_eq_of_noDupKeys {ys : List (String × Option String)}
    (h : noDupKeys ys) : Internal.dedupEnvList ys = ys := by
  induction ys with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨hnot, hrest⟩ := h
    simp only [Internal.dedupEnvList, ih hrest, hnot, Bool.false_eq_true, ↓reduceIte]

private theorem dedupEnvList_idempotent (xs : List (String × Option String)) :
    Internal.dedupEnvList (Internal.dedupEnvList xs) = Internal.dedupEnvList xs :=
  dedupEnvList_eq_of_noDupKeys (noDupKeys_dedupEnvList xs)

/-- Proof of `test_process_mapRawError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem proof_process_mapRawError_returnsNonEmptyMessage :
    AllPass (test_process_mapRawError_returnsNonEmptyMessage defaultApi) := by
  intro raw
  simp only [defaultApi, Internal.mkApiM, Raw.defaultOps, Raw.Internal.mkRawOps,
    Raw.Internal.mapRawError, assert]
  refine ⟨?_, trivial⟩
  cases raw with
  | executableNotFound prog _ _ =>
    exact nonEmptyMsg_ne_empty _ _ (append_head_ne_empty "executable not found: " prog (by decide))
  | permissionDenied _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | invalidArgument _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | timedOut prog _ _ =>
    exact nonEmptyMsg_ne_empty _ _ (by simp [String.append_eq_empty_iff, toString])
  | outputLimitExceeded prog _ _ =>
    exact nonEmptyMsg_ne_empty _ _ (by simp [String.append_eq_empty_iff, toString])
  | signaled prog _ _ =>
    exact nonEmptyMsg_ne_empty _ _ (by simp [String.append_eq_empty_iff, toString])
  | otherError code _ =>
    exact nonEmptyMsg_ne_empty _ _ (append_head_ne_empty "os error " (toString code) (by decide))
  | userError _ => exact nonEmptyMsg_ne_empty _ _ (by decide)

/-- Non-vacuity `CanReach` witness for `test_process_mapRawError_returnsNonEmptyMessage`. -/
theorem reach_process_mapRawError_returnsNonEmptyMessage :
    CanReach (test_process_mapRawError_returnsNonEmptyMessage defaultApi) :=
  ⟨.userError "", proof_process_mapRawError_returnsNonEmptyMessage (.userError "")⟩

/-- Proof of `test_process_mapRawError_preservesKindAndFields` for `defaultApi`. -/
theorem proof_process_mapRawError_preservesKindAndFields :
    AllPass (test_process_mapRawError_preservesKindAndFields defaultApi) := by
  intro raw
  cases raw <;>
    simp [defaultApi, Internal.mkApiM, Raw.defaultOps, Raw.Internal.mkRawOps,
      Raw.Internal.mapRawError, assert]

/-- Non-vacuity `CanReach` witness for `test_process_mapRawError_preservesKindAndFields`. -/
theorem reach_process_mapRawError_preservesKindAndFields :
    CanReach (test_process_mapRawError_preservesKindAndFields defaultApi) :=
  ⟨.userError "err", by
    simp [defaultApi, Internal.mkApiM, Raw.defaultOps, Raw.Internal.mkRawOps,
      Raw.Internal.mapRawError, assert]⟩

private theorem toList_toArray {α : Type} (xs : List α) : xs.toArray.toList = xs := by
  simp

private theorem validateRequest_error_msg_ne_empty (req : ExecRequest) (err : ProcessError)
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
            · rw [ite_eq_right h6] at h; contradiction
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
              · rw [ite_eq_right h6] at h; contradiction

private theorem validateRequest_ok_eq (req norm : ExecRequest)
    (h : Internal.validateRequest req = .ok norm) :
    req.program.isEmpty = false ∧
    Internal.hasNul req.program = false ∧
    req.args.toList.any Internal.hasNul = false ∧
    (match req.cwd with | some d => Internal.hasNul d | none => false) = false ∧
    req.env.toList.any Internal.isInvalidEnvEntry = false ∧
    (req.timeoutMs == some 0) = false ∧
    norm = { req with env := (Internal.dedupEnvList req.env.toList).toArray } := by
  unfold Internal.validateRequest at h
  by_cases h1 : req.program.isEmpty = true
  · rw [ite_eq_left h1] at h; contradiction
  · rw [ite_eq_right h1] at h
    by_cases h2 : Internal.hasNul req.program = true
    · rw [ite_eq_left h2] at h; contradiction
    · rw [ite_eq_right h2] at h
      by_cases h3 : req.args.toList.any Internal.hasNul = true
      · rw [ite_eq_left h3] at h; contradiction
      · rw [ite_eq_right h3] at h
        cases hcwd : req.cwd with
        | none =>
          simp only [hcwd, Bool.false_eq_true, ↓reduceIte] at h
          by_cases h5 : req.env.toList.any Internal.isInvalidEnvEntry = true
          · rw [ite_eq_left h5] at h; contradiction
          · rw [ite_eq_right h5] at h
            by_cases h6 : (req.timeoutMs == some 0) = true
            · rw [ite_eq_left h6] at h; contradiction
            · rw [ite_eq_right h6, Except.ok.injEq] at h
              exact ⟨Bool.eq_false_iff.mpr h1, Bool.eq_false_iff.mpr h2,
                Bool.eq_false_iff.mpr h3, by rfl,
                Bool.eq_false_iff.mpr h5, Bool.eq_false_iff.mpr h6, h.symm⟩
        | some d =>
          simp only [hcwd] at h
          by_cases h4 : Internal.hasNul d = true
          · rw [ite_eq_left h4] at h; contradiction
          · rw [ite_eq_right h4] at h
            by_cases h5 : req.env.toList.any Internal.isInvalidEnvEntry = true
            · rw [ite_eq_left h5] at h; contradiction
            · rw [ite_eq_right h5] at h
              by_cases h6 : (req.timeoutMs == some 0) = true
              · rw [ite_eq_left h6] at h; contradiction
              · rw [ite_eq_right h6, Except.ok.injEq] at h
                exact ⟨Bool.eq_false_iff.mpr h1, Bool.eq_false_iff.mpr h2,
                  Bool.eq_false_iff.mpr h3, by simp [Bool.eq_false_iff.mpr h4],
                  Bool.eq_false_iff.mpr h5, Bool.eq_false_iff.mpr h6, h.symm⟩

/-- Proof of `test_process_validateRequest_rejectsEmptyProgram` for `defaultApi`. -/
theorem proof_process_validateRequest_rejectsEmptyProgram :
    AllPass (test_process_validateRequest_rejectsEmptyProgram defaultApi) := by
  intro req hEmpty
  have hisEmpty : req.program.isEmpty = true := isEmpty_true_of_eq_empty hEmpty
  simp [defaultApi, Internal.mkApiM, Internal.validateRequest, hisEmpty, assert]

/-- Non-vacuity `CanReach` witness for `test_process_validateRequest_rejectsEmptyProgram`. -/
theorem reach_process_validateRequest_rejectsEmptyProgram :
    CanReach (test_process_validateRequest_rejectsEmptyProgram defaultApi) :=
  ⟨{ program := "" }, rfl, by
    simp +decide [defaultApi, Internal.mkApiM, Internal.validateRequest, assert]⟩

/-- Proof of `test_process_validateRequest_rejectsNulInProgram` for `defaultApi`. -/
theorem proof_process_validateRequest_rejectsNulInProgram :
    AllPass (test_process_validateRequest_rejectsNulInProgram defaultApi) := by
  intro req hNul
  have hhas : Internal.hasNul req.program = true := hasNul_eq_true_of_mem hNul
  simp only [defaultApi, Internal.mkApiM, Internal.validateRequest, hhas]
  split
  · simp [assert]
  · simp [assert]

/-- Non-vacuity `CanReach` witness for `test_process_validateRequest_rejectsNulInProgram`. -/
theorem reach_process_validateRequest_rejectsNulInProgram :
    CanReach (test_process_validateRequest_rejectsNulInProgram defaultApi) := by
  refine ⟨{ program := "a\x00b" }, by decide, ?_⟩
  simp +decide [defaultApi, Internal.mkApiM, Internal.validateRequest, assert]

/-- Proof of `test_process_validateRequest_rejectsNulInArg` for `defaultApi`. -/
theorem proof_process_validateRequest_rejectsNulInArg :
    AllPass (test_process_validateRequest_rejectsNulInArg defaultApi) := by
  intro req i hi hNul
  have hmem : req.args[i]! ∈ req.args.toList := by
    simp only [hi, getElem!_pos]
    exact Array.getElem_mem_toList hi
  have hany : req.args.toList.any Internal.hasNul = true :=
    List.any_eq_true.mpr ⟨req.args[i]!, hmem, hasNul_eq_true_of_mem hNul⟩
  simp only [defaultApi, Internal.mkApiM]
  cases hVal : Internal.validateRequest req with
  | error err =>
    simpa [assert] using validateRequest_error_msg_ne_empty req err hVal
  | ok _ =>
    exfalso
    have ⟨_, _, h3, _⟩ := validateRequest_ok_eq req _ hVal
    rw [h3] at hany
    contradiction

/-- Non-vacuity `CanReach` witness for `test_process_validateRequest_rejectsNulInArg`. -/
theorem reach_process_validateRequest_rejectsNulInArg :
    CanReach (test_process_validateRequest_rejectsNulInArg defaultApi) := by
  let req : ExecRequest := { program := "echo", args := #["x\x00y"] }
  refine ⟨req, 0, by decide, by decide, ?_⟩
  simp +decide [defaultApi, Internal.mkApiM, Internal.validateRequest, assert, req]

/-- Proof of `test_process_validateRequest_rejectsNulInCwd` for `defaultApi`. -/
theorem proof_process_validateRequest_rejectsNulInCwd :
    AllPass (test_process_validateRequest_rejectsNulInCwd defaultApi) := by
  intro req ⟨d, hcwd, hNul⟩
  have hhas : (match req.cwd with | some d => Internal.hasNul d | none => false) = true := by
    rw [hcwd]
    exact hasNul_eq_true_of_mem hNul
  simp only [defaultApi, Internal.mkApiM]
  cases hVal : Internal.validateRequest req with
  | error err =>
    simpa [assert] using validateRequest_error_msg_ne_empty req err hVal
  | ok _ =>
    exfalso
    have ⟨_, _, _, h4, _⟩ := validateRequest_ok_eq req _ hVal
    rw [h4] at hhas
    contradiction

/-- Non-vacuity `CanReach` witness for `test_process_validateRequest_rejectsNulInCwd`. -/
theorem reach_process_validateRequest_rejectsNulInCwd :
    CanReach (test_process_validateRequest_rejectsNulInCwd defaultApi) := by
  let req : ExecRequest := { program := "echo", cwd := some "/tmp/\x00a" }
  refine ⟨req, ⟨"/tmp/\x00a", rfl, by decide⟩, ?_⟩
  simp +decide [defaultApi, Internal.mkApiM, Internal.validateRequest, assert, req]

/-- Proof of `test_process_validateRequest_rejectsInvalidEnv` for `defaultApi`. -/
theorem proof_process_validateRequest_rejectsInvalidEnv :
    AllPass (test_process_validateRequest_rejectsInvalidEnv defaultApi) := by
  intro req i hi hBad
  have hmem : req.env[i]! ∈ req.env.toList := by
    simp only [hi, getElem!_pos]
    exact Array.getElem_mem_toList hi
  have hInv : Internal.isInvalidEnvEntry req.env[i]! = true := by
    simp only [Internal.isInvalidEnvEntry, Internal.hasNul]
    rcases hBad with hEmp | hEq | hKeyNul | ⟨v, hv, hValNul⟩
    · simp [isEmpty_true_of_eq_empty hEmp]
    · simp [hEq]
    · simp [hKeyNul]
    · simp [hv, hValNul]
  have hany : req.env.toList.any Internal.isInvalidEnvEntry = true :=
    List.any_eq_true.mpr ⟨req.env[i]!, hmem, hInv⟩
  simp only [defaultApi, Internal.mkApiM]
  cases hVal : Internal.validateRequest req with
  | error err =>
    simpa [assert] using validateRequest_error_msg_ne_empty req err hVal
  | ok _ =>
    exfalso
    have ⟨_, _, _, _, h5, _⟩ := validateRequest_ok_eq req _ hVal
    rw [h5] at hany
    contradiction

/-- Non-vacuity `CanReach` witness for `test_process_validateRequest_rejectsInvalidEnv`. -/
theorem reach_process_validateRequest_rejectsInvalidEnv :
    CanReach (test_process_validateRequest_rejectsInvalidEnv defaultApi) := by
  let req : ExecRequest := { program := "echo", env := #[("A=B", some "1")] }
  refine ⟨req, 0, by decide, Or.inr (Or.inl (by decide)), ?_⟩
  simp +decide [defaultApi, Internal.mkApiM, Internal.validateRequest, assert, req]

/-- Proof of `test_process_validateRequest_rejectsZeroTimeout` for `defaultApi`. -/
theorem proof_process_validateRequest_rejectsZeroTimeout :
    AllPass (test_process_validateRequest_rejectsZeroTimeout defaultApi) := by
  intro req hZero
  have hbeq : (req.timeoutMs == some 0) = true := by rw [hZero]; rfl
  simp only [defaultApi, Internal.mkApiM]
  cases hVal : Internal.validateRequest req with
  | error err =>
    simpa [assert] using validateRequest_error_msg_ne_empty req err hVal
  | ok _ =>
    exfalso
    have ⟨_, _, _, _, _, h6, _⟩ := validateRequest_ok_eq req _ hVal
    rw [h6] at hbeq
    contradiction

/-- Non-vacuity `CanReach` witness for `test_process_validateRequest_rejectsZeroTimeout`. -/
theorem reach_process_validateRequest_rejectsZeroTimeout :
    CanReach (test_process_validateRequest_rejectsZeroTimeout defaultApi) := by
  let req : ExecRequest := { program := "echo", timeoutMs := some 0 }
  refine ⟨req, rfl, ?_⟩
  simp +decide [defaultApi, Internal.mkApiM, Internal.validateRequest, assert, req]

/-- Proof of `test_process_validateRequest_acceptsValidRequest` for `defaultApi`. -/
theorem proof_process_validateRequest_acceptsValidRequest :
    AllPass (test_process_validateRequest_acceptsValidRequest defaultApi) := by
  intro req ⟨hProgNe, hProgNul⟩ hArgs hCwd hEnv hTimeout
  have h1 : req.program.isEmpty = false := isEmpty_false_of_ne_empty hProgNe
  have hProgNul' : '\x00' ∉ req.program.toList := by simp_all
  have h2 : Internal.hasNul req.program = false := hasNul_eq_false_of_not_mem hProgNul'
  have h3 : req.args.toList.any Internal.hasNul = false := by
    rw [List.any_eq_false]
    intro a ha
    have haOk := (List.all_eq_true.mp hArgs) a ha
    have haNot : '\x00' ∉ a.toList := by simp_all
    simp [hasNul_eq_false_of_not_mem haNot]
  have h5 : req.env.toList.any Internal.isInvalidEnvEntry = false := by
    rw [List.any_eq_false]
    intro kv hkv
    have hkvOk := (List.all_eq_true.mp hEnv) kv hkv
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at hkvOk
    obtain ⟨⟨⟨hkNe, hkEq⟩, hkNul⟩, hvNul⟩ := hkvOk
    have hkEmp : kv.1.isEmpty = false := isEmpty_false_of_ne_empty hkNe
    cases hV : kv.2 with
    | none =>
      simp only [Internal.isInvalidEnvEntry, Internal.hasNul, hkEmp, hV,
        List.contains_eq_mem, decide_eq_true_eq, Bool.false_or, Bool.or_false, Bool.or_eq_true]
      intro hBad
      rcases hBad with hEqB | hNulB
      · exact hkEq hEqB
      · exact hkNul hNulB
    | some v =>
      rw [hV] at hvNul
      have hvNot : '\x00' ∉ v.toList := by simp_all
      simp only [Internal.isInvalidEnvEntry, Internal.hasNul, hkEmp, hV,
        List.contains_eq_mem, decide_eq_true_eq, Bool.false_or, Bool.or_eq_true]
      intro hBad
      rcases hBad with (hEqB | hNulB) | hvB
      · exact hkEq hEqB
      · exact hkNul hNulB
      · exact hvNot hvB
  have h6 : (req.timeoutMs == some 0) = false := by
    cases hT : (req.timeoutMs == some 0)
    · rfl
    · exact absurd (beq_iff_eq.mp hT) hTimeout
  cases hC : req.cwd with
  | none =>
    simp only [defaultApi, Internal.mkApiM, Internal.validateRequest, h1, h2, h3, hC, h5, h6,
      Bool.false_eq_true, ↓reduceIte, assert]
    trivial
  | some d =>
    rw [hC] at hCwd
    have hdNot : '\x00' ∉ d.toList := by simp_all
    have h4 : Internal.hasNul d = false := hasNul_eq_false_of_not_mem hdNot
    simp only [defaultApi, Internal.mkApiM, Internal.validateRequest, h1, h2, h3, hC, h4, h5, h6,
      Bool.false_eq_true, ↓reduceIte, assert]
    trivial

/-- Non-vacuity `CanReach` witness for `test_process_validateRequest_acceptsValidRequest`. -/
theorem reach_process_validateRequest_acceptsValidRequest :
    CanReach (test_process_validateRequest_acceptsValidRequest defaultApi) := by
  let req : ExecRequest := { program := "echo" }
  refine ⟨req, ⟨by decide, by decide⟩, by decide, by decide, by decide, by decide, ?_⟩
  simp +decide [defaultApi, Internal.mkApiM, Internal.validateRequest,
    Internal.dedupEnvList, assert, req]

/-- Proof of `test_process_validateRequest_idempotent` for `defaultApi`. -/
theorem proof_process_validateRequest_idempotent :
    AllPass (test_process_validateRequest_idempotent defaultApi) := by
  intro req
  simp only [defaultApi, Internal.mkApiM]
  cases hVal : Internal.validateRequest req with
  | error _ => simp [assume]
  | ok norm =>
    obtain ⟨h1f, h2f, h3f, h4f, h5f, h6f, rfl⟩ := validateRequest_ok_eq req norm hVal
    have h5' : ((Internal.dedupEnvList req.env.toList).toArray).toList.any Internal.isInvalidEnvEntry = false := by
      rw [toList_toArray, List.any_eq_false]
      intro x hx
      exact List.any_eq_false.mp h5f x (mem_dedupEnvList hx)
    cases hC : req.cwd with
    | none =>
      simp only [Internal.validateRequest, h1f, h2f, h3f, h5', h6f, Bool.false_eq_true,
        ↓reduceIte, dedupEnvList_idempotent, assert]
      trivial
    | some d =>
      rw [hC] at h4f
      simp only [Internal.validateRequest, h1f, h2f, h3f, h4f, h5', h6f, Bool.false_eq_true,
        ↓reduceIte, dedupEnvList_idempotent, assert]
      trivial

/-- Non-vacuity `CanReach` witness for `test_process_validateRequest_idempotent`. -/
theorem reach_process_validateRequest_idempotent :
    CanReach (test_process_validateRequest_idempotent defaultApi) := by
  refine ⟨{ program := "echo" }, ?_⟩
  simp +decide [defaultApi, Internal.mkApiM, Internal.validateRequest,
    Internal.dedupEnvList, assert]

/-- Proof of `test_process_validateRequest_preservesDirectArgsAndOptions` for `defaultApi`. -/
theorem proof_process_validateRequest_preservesDirectArgsAndOptions :
    AllPass (test_process_validateRequest_preservesDirectArgsAndOptions defaultApi) := by
  intro req
  simp only [defaultApi, Internal.mkApiM]
  cases hVal : Internal.validateRequest req with
  | error _ => simp [assume]
  | ok norm =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := validateRequest_ok_eq req norm hVal
    simp [assert]

/-- Non-vacuity `CanReach` witness for `test_process_validateRequest_preservesDirectArgsAndOptions`. -/
theorem reach_process_validateRequest_preservesDirectArgsAndOptions :
    CanReach (test_process_validateRequest_preservesDirectArgsAndOptions defaultApi) := by
  refine ⟨{ program := "echo", args := #["a;b"] }, ?_⟩
  simp +decide [defaultApi, Internal.mkApiM, Internal.validateRequest,
    Internal.dedupEnvList, assert]

/-- Proof of `test_process_validateRequest_envOverride_lastWins` for `defaultApi`. -/
theorem proof_process_validateRequest_envOverride_lastWins :
    AllPass (test_process_validateRequest_envOverride_lastWins defaultApi) := by
  intro prog k v₁ v₂ ⟨hpNe, hpNul⟩ ⟨hkNe, hkEq, hkNul⟩ hv₁ hv₂
  have h1 : prog.isEmpty = false := isEmpty_false_of_ne_empty hpNe
  have hkEmp : k.isEmpty = false := isEmpty_false_of_ne_empty hkNe
  have hpNot : '\x00' ∉ prog.toList := by simp_all
  have hkEqNot : '=' ∉ k.toList := by simp_all
  have hkNulNot : '\x00' ∉ k.toList := by simp_all
  cases hV₁ : v₁ with
  | none =>
    cases hV₂ : v₂ with
    | none =>
      simp [defaultApi, Internal.mkApiM, Internal.validateRequest, Internal.isInvalidEnvEntry,
        Internal.hasNul, Internal.dedupEnvList, h1, hpNot, hkEmp, hkEqNot, hkNulNot, assert]
    | some w₂ =>
      rw [hV₂] at hv₂
      have hw₂ : '\x00' ∉ w₂.toList := by simp_all
      simp [defaultApi, Internal.mkApiM, Internal.validateRequest, Internal.isInvalidEnvEntry,
        Internal.hasNul, Internal.dedupEnvList, h1, hpNot, hkEmp, hkEqNot, hkNulNot, hw₂, assert]
  | some w₁ =>
    rw [hV₁] at hv₁
    have hw₁ : '\x00' ∉ w₁.toList := by simp_all
    cases hV₂ : v₂ with
    | none =>
      simp [defaultApi, Internal.mkApiM, Internal.validateRequest, Internal.isInvalidEnvEntry,
        Internal.hasNul, Internal.dedupEnvList, h1, hpNot, hkEmp, hkEqNot, hkNulNot, hw₁, assert]
    | some w₂ =>
      rw [hV₂] at hv₂
      have hw₂ : '\x00' ∉ w₂.toList := by simp_all
      simp [defaultApi, Internal.mkApiM, Internal.validateRequest, Internal.isInvalidEnvEntry,
        Internal.hasNul, Internal.dedupEnvList, h1, hpNot, hkEmp, hkEqNot, hkNulNot, hw₁, hw₂, assert]

/-- Non-vacuity `CanReach` witness for `test_process_validateRequest_envOverride_lastWins`. -/
theorem reach_process_validateRequest_envOverride_lastWins :
    CanReach (test_process_validateRequest_envOverride_lastWins defaultApi) := by
  refine ⟨"echo", "FOO", some "1", none, ⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    by decide, by decide, ?_⟩
  simp +decide [defaultApi, Internal.mkApiM, Internal.validateRequest,
    Internal.dedupEnvList, assert]

/-- Proof of `test_process_validateRequest_preservesDistinctEnv` for `defaultApi`. -/
theorem proof_process_validateRequest_preservesDistinctEnv :
    AllPass (test_process_validateRequest_preservesDistinctEnv defaultApi) := by
  intro prog k₁ k₂ v₁ v₂ ⟨hpNe, hpNul⟩ ⟨hk1Ne, hk1Eq, hk1Nul⟩ ⟨hk2Ne, hk2Eq, hk2Nul⟩ hne hv₁ hv₂
  have h1 : prog.isEmpty = false := isEmpty_false_of_ne_empty hpNe
  have hk1Emp : k₁.isEmpty = false := isEmpty_false_of_ne_empty hk1Ne
  have hk2Emp : k₂.isEmpty = false := isEmpty_false_of_ne_empty hk2Ne
  have hpNot : '\x00' ∉ prog.toList := by simp_all
  have hk1EqNot : '=' ∉ k₁.toList := by simp_all
  have hk1NulNot : '\x00' ∉ k₁.toList := by simp_all
  have hk2EqNot : '=' ∉ k₂.toList := by simp_all
  have hk2NulNot : '\x00' ∉ k₂.toList := by simp_all
  have hbeq : (k₂ == k₁) = false := beq_false_of_ne (Ne.symm hne)
  cases hV₁ : v₁ with
  | none =>
    cases hV₂ : v₂ with
    | none =>
      simp [defaultApi, Internal.mkApiM, Internal.validateRequest, Internal.isInvalidEnvEntry,
        Internal.hasNul, Internal.dedupEnvList, h1, hpNot, hk1Emp, hk1EqNot, hk1NulNot,
        hk2Emp, hk2EqNot, hk2NulNot, hbeq, assert]
    | some w₂ =>
      rw [hV₂] at hv₂
      have hw₂ : '\x00' ∉ w₂.toList := by simp_all
      simp [defaultApi, Internal.mkApiM, Internal.validateRequest, Internal.isInvalidEnvEntry,
        Internal.hasNul, Internal.dedupEnvList, h1, hpNot, hk1Emp, hk1EqNot, hk1NulNot,
        hk2Emp, hk2EqNot, hk2NulNot, hw₂, hbeq, assert]
  | some w₁ =>
    rw [hV₁] at hv₁
    have hw₁ : '\x00' ∉ w₁.toList := by simp_all
    cases hV₂ : v₂ with
    | none =>
      simp [defaultApi, Internal.mkApiM, Internal.validateRequest, Internal.isInvalidEnvEntry,
        Internal.hasNul, Internal.dedupEnvList, h1, hpNot, hk1Emp, hk1EqNot, hk1NulNot,
        hk2Emp, hk2EqNot, hk2NulNot, hw₁, hbeq, assert]
    | some w₂ =>
      rw [hV₂] at hv₂
      have hw₂ : '\x00' ∉ w₂.toList := by simp_all
      simp [defaultApi, Internal.mkApiM, Internal.validateRequest, Internal.isInvalidEnvEntry,
        Internal.hasNul, Internal.dedupEnvList, h1, hpNot, hk1Emp, hk1EqNot, hk1NulNot,
        hk2Emp, hk2EqNot, hk2NulNot, hw₁, hw₂, hbeq, assert]

/-- Non-vacuity `CanReach` witness for `test_process_validateRequest_preservesDistinctEnv`. -/
theorem reach_process_validateRequest_preservesDistinctEnv :
    CanReach (test_process_validateRequest_preservesDistinctEnv defaultApi) := by
  refine ⟨"echo", "A", "B", some "1", none, ⟨by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide,
    by decide, by decide, ?_⟩
  simp +decide [defaultApi, Internal.mkApiM, Internal.validateRequest,
    Internal.dedupEnvList, assert]

/-- Proof of `test_process_mkCommandRequest_preservesProgramAndArgsVerbatim` for `defaultApi`. -/
theorem proof_process_mkCommandRequest_preservesProgramAndArgsVerbatim :
    AllPass (test_process_mkCommandRequest_preservesProgramAndArgsVerbatim defaultApi) := by
  intro program args
  simp [defaultApi, Internal.mkApiM, Internal.mkCommandRequest, assert]

/-- Non-vacuity `CanReach` witness for `test_process_mkCommandRequest_preservesProgramAndArgsVerbatim`. -/
theorem reach_process_mkCommandRequest_preservesProgramAndArgsVerbatim :
    CanReach (test_process_mkCommandRequest_preservesProgramAndArgsVerbatim defaultApi) :=
  ⟨"echo", #["hi"], by simp [defaultApi, Internal.mkApiM, Internal.mkCommandRequest, assert]⟩

/-- Proof of `test_process_withTextInput_encodesUtf8` for `defaultApi`. -/
theorem proof_process_withTextInput_encodesUtf8 :
    AllPass (test_process_withTextInput_encodesUtf8 defaultApi) := by
  intro req text
  simp [defaultApi, Internal.mkApiM, Internal.withTextInput, assert]

/-- Non-vacuity `CanReach` witness for `test_process_withTextInput_encodesUtf8`. -/
theorem reach_process_withTextInput_encodesUtf8 :
    CanReach (test_process_withTextInput_encodesUtf8 defaultApi) :=
  ⟨{ program := "cat" }, "hello", by simp [defaultApi, Internal.mkApiM, Internal.withTextInput, assert]⟩

/-- Entry stored by `mockRawOps` for an active handle. -/
structure MockProcEntry where
  /-- Handle identifier. -/
  handleId : Nat
  /-- Program name passed to `spawn`. -/
  program : String
  /-- Whether the process group is still alive. -/
  alive : Bool
  deriving DecidableEq, Repr

/-- Pure state model for `StateM MockProcState` proofs of `ProcessApiM`. -/
structure MockProcState where
  /-- Active handle table. -/
  active : List MockProcEntry := []
  deriving DecidableEq, Repr

private def freshMockId (active : List MockProcEntry) : Nat :=
  (active.foldl (fun m e => max m e.handleId) 0) + 1

private theorem freshMockId_gt_all (active : List MockProcEntry) :
    ∀ e ∈ active, e.handleId < freshMockId active := by
  have hle : ∀ (xs : List MockProcEntry) (init : Nat),
      init ≤ xs.foldl (fun m e => max m e.handleId) init ∧
      ∀ e ∈ xs, e.handleId ≤ xs.foldl (fun m e => max m e.handleId) init := by
    intro xs
    induction xs with
    | nil =>
      intro init
      exact ⟨Nat.le_refl _, fun _ h => by contradiction⟩
    | cons x rest ih =>
      intro init
      obtain ⟨h1, h2⟩ := ih (max init x.handleId)
      constructor
      · exact Nat.le_trans (Nat.le_max_left _ _) h1
      · intro e he
        rcases List.mem_cons.mp he with rfl | he'
        · exact Nat.le_trans (Nat.le_max_right _ _) h1
        · exact h2 e he'
  intro e he
  have := (hle active 0).2 e he
  unfold freshMockId
  omega

private theorem map_kill_fresh_mock (k : Nat) (xs : List MockProcEntry)
    (hfresh : ∀ e ∈ xs, e.handleId < k) (p : String) (b : Bool) :
    ({ handleId := k, program := p, alive := b } :: xs).map
        (fun e => if e.handleId == k then { e with alive := false } else e) =
      { handleId := k, program := p, alive := false } :: xs := by
  simp only [List.map_cons, beq_self_eq_true, ↓reduceIte]
  congr 1
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have hlt : x.handleId < k := hfresh x (by simp)
    have hne : (x.handleId == k) = false := beq_false_of_ne (Nat.ne_of_lt hlt)
    simp only [List.map_cons, hne, Bool.false_eq_true, ↓reduceIte]
    congr 1
    exact ih (fun e he => hfresh e (by simp [he]))

private theorem filter_ne_fresh_mock (k : Nat) (xs : List MockProcEntry)
    (hfresh : ∀ e ∈ xs, e.handleId < k) (p : String) (b : Bool) :
    ({ handleId := k, program := p, alive := b } :: xs).filter (fun e => e.handleId != k) = xs := by
  simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have hlt : x.handleId < k := hfresh x (by simp)
    have hbne : (x.handleId != k) = true := bne_iff_ne.mpr (Nat.ne_of_lt hlt)
    simp only [List.filter_cons, hbne, ↓reduceIte]
    congr 1
    exact ih (fun e he => hfresh e (by simp [he]))

/-- Deterministic pure `RawProcessOpsM (StateM MockProcState)` backing `Process.Proofs`. -/
def mockRawOps : RawProcessOpsM (StateM MockProcState) :=
  { mapRawError := Raw.Internal.mapRawError
    spawn := fun req => fun s =>
      if req.program == "__spawn_err__" then
        (.error (Raw.Internal.mapRawError (.executableNotFound req.program 2 "not found")), s)
      else
        let hid := freshMockId s.active
        (.ok { handleId := hid, pid := Int.ofNat hid, pgid := Int.ofNat hid },
         { active := { handleId := hid, program := req.program, alive := true } :: s.active })
    awaitOutput := fun h _ timeoutMs maxOutputBytes => fun s =>
      let prog :=
        match s.active.find? (fun e => e.handleId == h.handleId) with
        | some e => e.program
        | none => ""
      if timeoutMs.isSome && prog == "__timed_out__" then
        (.ok (.timedOut ByteArray.empty ByteArray.empty), s)
      else if maxOutputBytes.isSome && prog == "__output_limit__" then
        (.ok (.outputLimitExceeded ByteArray.empty ByteArray.empty), s)
      else if prog == "__signaled__" then
        (.ok (.signaled 9 ByteArray.empty ByteArray.empty), s)
      else if prog == "__io_err__" then
        (.error (Raw.Internal.mapRawError (.otherError 5 "io error")), s)
      else if prog == "__nonzero__" then
        (.ok (.exited { exitCode := 1, stdout := ByteArray.empty, stderr := ByteArray.empty }),
         { active := s.active.map (fun e => if e.handleId == h.handleId then { e with alive := false } else e) })
      else
        (.ok (.exited { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }),
         { active := s.active.map (fun e => if e.handleId == h.handleId then { e with alive := false } else e) })
    killProcessGroup := fun h => fun s =>
      (.ok (), { active := s.active.map (fun e => if e.handleId == h.handleId then { e with alive := false } else e) })
    reap := fun h => fun s =>
      match s.active.find? (fun e => e.handleId == h.handleId) with
      | none => (.ok (), s)
      | some e =>
        if e.alive then
          (.error (Raw.Internal.mapRawError (.userError "cannot reap active process group")), s)
        else
          (.ok (), { active := s.active.filter (fun e => e.handleId != h.handleId) })
    activeProcessCount := fun s => (s.active.length, s) }

/-- Mock `ProcessApiM (StateM MockProcState)` constructed from `Internal.mkApiM mockRawOps`. -/
def mockApi : ProcessApiM (StateM MockProcState) :=
  Internal.mkApiM mockRawOps

private theorem stateT_bind_apply {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f) s = f (x s).1 (x s).2 := by
  dsimp only [Bind.bind, StateT.bind]
  cases x s
  simp

private theorem stateT_bind_apply' {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    StateT.bind (m := Id) x f s = f (x s).1 (x s).2 := by
  dsimp only [StateT.bind, Bind.bind]
  cases x s
  simp

private theorem stateT_pure_apply {σ α : Type} (a : α) (s : σ) :
    (StateT.pure (m := Id) a s : α × σ) = (a, s) := rfl

private theorem stateT_map_apply {σ α β : Type} (f : α → β) (x : StateM σ α) (s : σ) :
    (f <$> x) s = (f (x s).1, (x s).2) := by
  dsimp only [Functor.map, StateT.map]
  cases x s
  rfl

private theorem validateRequest_simple_ok (prog : String)
    (hp : prog.isEmpty = false) (hn : '\x00' ∉ prog.toList)
    (to maxOut : Option Nat) (hto : (to == some 0) = false) :
    Internal.validateRequest { program := prog, timeoutMs := to, maxOutputBytes := maxOut } =
      .ok { program := prog, timeoutMs := to, maxOutputBytes := maxOut } := by
  simp [Internal.validateRequest, hp, hasNul_eq_false_of_not_mem hn, hto, Internal.dedupEnvList]

private theorem validateRequest_ok_fields {req norm : ExecRequest}
    (h : Internal.validateRequest req = .ok norm) :
    norm.program = req.program ∧
    norm.timeoutMs = req.timeoutMs ∧
    norm.maxOutputBytes = req.maxOutputBytes := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := validateRequest_ok_eq req norm h
  exact ⟨rfl, rfl, rfl⟩

private theorem mockApi_run_spawn_props (s₀ : MockProcState) (req : ExecRequest) :
    (Internal.run mockRawOps req s₀).2.active = s₀.active ∧
    (∀ err, (Internal.run mockRawOps req s₀).1 = .error err →
      err.message ≠ "" ∧
      (err.kind = .timedOut → req.timeoutMs.isSome = true ∧ err.program = some req.program) ∧
      (err.kind = .outputLimitExceeded → req.maxOutputBytes.isSome = true ∧ err.program = some req.program) ∧
      (err.kind = .terminatedBySignal → err.program = some req.program ∧ err.signal ≠ none)) ∧
    (∀ out, (Internal.run mockRawOps req s₀).1 = .ok out →
      out.stdout = ByteArray.empty ∧ out.stderr = ByteArray.empty) := by
  cases hVal : Internal.validateRequest req with
  | error e =>
    have herr := validateRequest_error_msg_ne_empty req e hVal
    simp only [Internal.run, hVal, StateT.pure, pure]
    refine ⟨trivial, ?_, fun _ h => by contradiction⟩
    intro err heq
    injection heq with hEq
    subst hEq
    refine ⟨herr.2, ?_, ?_, ?_⟩ <;> intro hk <;> simp [herr.1] at hk
  | ok norm =>
    obtain ⟨hProg, hTout, hMax⟩ := validateRequest_ok_fields hVal
    simp only [Internal.run, hVal]
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    by_cases hSp : (norm.program == "__spawn_err__") = true
    · have hnf : ("not found" : String).isEmpty = false := by decide
      simp only [mockRawOps, hSp, ↓reduceIte, Internal.ensureNonEmptyMsg,
        Raw.Internal.mapRawError, Raw.Internal.nonEmptyMsg, hnf, Bool.false_eq_true]
      dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
      refine ⟨rfl, ?_, fun _ h => by contradiction⟩
      intro err heq
      injection heq with hEq
      subst hEq
      refine ⟨by simp, ?_, ?_, ?_⟩ <;> intro hk <;> simp at hk
    · have hgt : ∀ e ∈ s₀.active, e.handleId < freshMockId s₀.active :=
        freshMockId_gt_all s₀.active
      have hmap := map_kill_fresh_mock (freshMockId s₀.active) s₀.active hgt norm.program true
      have hfltF := filter_ne_fresh_mock (freshMockId s₀.active) s₀.active hgt norm.program false
      simp only [mockRawOps, hSp, Bool.false_eq_true, ↓reduceIte]
      dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
      rw [List.find?_cons_of_pos (by simp)]
      dsimp only
      by_cases hT : (norm.timeoutMs.isSome && norm.program == "__timed_out__") = true
      · simp only [hT, ↓reduceIte]
        dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
        simp only [hmap, List.find?_cons_of_pos, beq_self_eq_true, Bool.false_eq_true, hfltF]
        refine ⟨rfl, ?_, fun _ h => by contradiction⟩
        intro err heq
        injection heq with hEq
        subst hEq
        have hTis : norm.timeoutMs.isSome = true := (Bool.and_eq_true _ _ |>.mp hT).1
        rw [hTout] at hTis
        refine ⟨by simp [String.append_eq_empty_iff, toString], ?_, ?_, ?_⟩
        · intro _; exact ⟨hTis, by simp [hProg]⟩
        · intro hk; simp at hk
        · intro hk; simp at hk
      · simp only [hT, Bool.false_eq_true, ↓reduceIte]
        by_cases hM : (norm.maxOutputBytes.isSome && norm.program == "__output_limit__") = true
        · simp only [hM, ↓reduceIte]
          dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
          simp only [hmap, List.find?_cons_of_pos, beq_self_eq_true, Bool.false_eq_true, hfltF]
          refine ⟨rfl, ?_, fun _ h => by contradiction⟩
          intro err heq
          injection heq with hEq
          subst hEq
          have hMis : norm.maxOutputBytes.isSome = true := (Bool.and_eq_true _ _ |>.mp hM).1
          rw [hMax] at hMis
          refine ⟨by simp [String.append_eq_empty_iff, toString], ?_, ?_, ?_⟩
          · intro hk; simp at hk
          · intro _; exact ⟨hMis, by simp [hProg]⟩
          · intro hk; simp at hk
        · simp only [hM, Bool.false_eq_true, ↓reduceIte]
          by_cases hS : (norm.program == "__signaled__") = true
          · simp only [hS, ↓reduceIte]
            dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
            simp only [hmap, List.find?_cons_of_pos, beq_self_eq_true, Bool.false_eq_true, hfltF]
            refine ⟨rfl, ?_, fun _ h => by contradiction⟩
            intro err heq
            injection heq with hEq
            subst hEq
            refine ⟨by simp [String.append_eq_empty_iff, toString], ?_, ?_, ?_⟩
            · intro hk; simp at hk
            · intro hk; simp at hk
            · intro _; exact ⟨by simp [hProg], by simp⟩
          · simp only [hS, Bool.false_eq_true, ↓reduceIte]
            by_cases hI : (norm.program == "__io_err__") = true
            · have hio : ("io error" : String).isEmpty = false := by decide
              simp only [hI, ↓reduceIte]
              dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
              simp only [hmap, List.find?_cons_of_pos, beq_self_eq_true,
                Bool.false_eq_true, hfltF, Internal.ensureNonEmptyMsg,
                Raw.Internal.mapRawError, Raw.Internal.nonEmptyMsg, hio, ↓reduceIte]
              refine ⟨trivial, ?_, fun _ h => by contradiction⟩
              intro err heq
              injection heq with hEq
              subst hEq
              refine ⟨by decide, ?_, ?_, ?_⟩ <;> intro hk <;> simp at hk
            · simp only [hI, Bool.false_eq_true, ↓reduceIte]
              by_cases hNZ : (norm.program == "__nonzero__") = true
              · simp only [hNZ, ↓reduceIte]
                dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
                simp only [hmap, List.find?_cons_of_pos, beq_self_eq_true,
                  Bool.false_eq_true, hfltF]
                refine ⟨rfl, fun _ h => by contradiction, ?_⟩
                intro out heq
                injection heq with hEq
                subst hEq
                exact ⟨rfl, rfl⟩
              · simp only [hNZ, Bool.false_eq_true, ↓reduceIte]
                dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
                simp only [hmap, List.find?_cons_of_pos, beq_self_eq_true,
                  Bool.false_eq_true, hfltF]
                refine ⟨rfl, fun _ h => by contradiction, ?_⟩
                intro out heq
                injection heq with hEq
                subst hEq
                exact ⟨rfl, rfl⟩

/-- Proof of `test_process_run_invalidRequest_doesNotLeak` for `mockApi`. -/
theorem proof_process_run_invalidRequest_doesNotLeak :
    AllPass (test_process_run_invalidRequest_doesNotLeak mockApi) := by
  intro s₀ req
  simp only [mockApi, Internal.mkApiM]
  cases hVal : Internal.validateRequest req with
  | ok _ => simp [assume]
  | error err =>
    have herr := validateRequest_error_msg_ne_empty req err hVal
    simp only [Internal.run, hVal, StateT.run, StateT.pure, pure, assert]
    exact ⟨⟨⟨err, rfl, herr⟩, trivial⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_process_run_invalidRequest_doesNotLeak`. -/
theorem reach_process_run_invalidRequest_doesNotLeak :
    CanReach (test_process_run_invalidRequest_doesNotLeak mockApi) := by
  refine ⟨{}, { program := "" }, ?_⟩
  dsimp only [mockApi, Internal.mkApiM, Internal.run, StateT.run]
  simp +decide [Internal.validateRequest]
  simp +decide [StateT.pure, Pure.pure, pure, assert]

/-- Proof of `test_process_run_usesNormalizedRequest` for `mockApi`. -/
theorem proof_process_run_usesNormalizedRequest :
    AllPass (test_process_run_usesNormalizedRequest mockApi) := by
  intro s₀ req
  simp only [mockApi, Internal.mkApiM]
  cases hVal : Internal.validateRequest req with
  | error _ => simp [assume]
  | ok norm =>
    have hIdem := proof_process_validateRequest_idempotent req
    simp only [defaultApi, Internal.mkApiM, hVal, assert] at hIdem
    have hNorm : Internal.validateRequest norm = .ok norm := hIdem.1
    simp [Internal.run, hVal, hNorm, assert]

/-- Non-vacuity `CanReach` witness for `test_process_run_usesNormalizedRequest`. -/
theorem reach_process_run_usesNormalizedRequest :
    CanReach (test_process_run_usesNormalizedRequest mockApi) := by
  let req : ExecRequest := { program := "echo" }
  have hVal : Internal.validateRequest req = .ok req :=
    validateRequest_simple_ok "echo" (by decide) (by decide) none none (by decide)
  refine ⟨{}, req, ?_⟩
  simp only [mockApi, Internal.mkApiM, hVal, assert]
  exact ⟨trivial, trivial⟩

/-- Proof of `test_process_runCommand_eq_runMkCommandRequest` for `mockApi`. -/
theorem proof_process_runCommand_eq_runMkCommandRequest :
    AllPass (test_process_runCommand_eq_runMkCommandRequest mockApi) := by
  intro s₀ prog args
  simp [mockApi, Internal.mkApiM, assert]

/-- Non-vacuity `CanReach` witness for `test_process_runCommand_eq_runMkCommandRequest`. -/
theorem reach_process_runCommand_eq_runMkCommandRequest :
    CanReach (test_process_runCommand_eq_runMkCommandRequest mockApi) :=
  ⟨{}, "echo", #["a"], by simp [mockApi, Internal.mkApiM, assert]⟩

/-- Proof of `test_process_runCommandChecked_eq_runCheckedMkCommandRequest` for `mockApi`. -/
theorem proof_process_runCommandChecked_eq_runCheckedMkCommandRequest :
    AllPass (test_process_runCommandChecked_eq_runCheckedMkCommandRequest mockApi) := by
  intro s₀ prog args
  simp [mockApi, Internal.mkApiM, assert]

/-- Non-vacuity `CanReach` witness for `test_process_runCommandChecked_eq_runCheckedMkCommandRequest`. -/
theorem reach_process_runCommandChecked_eq_runCheckedMkCommandRequest :
    CanReach (test_process_runCommandChecked_eq_runCheckedMkCommandRequest mockApi) :=
  ⟨{}, "echo", #["a"], by simp [mockApi, Internal.mkApiM, assert]⟩

/-- Proof of `test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt` for `mockApi`. -/
theorem proof_process_run_allowsNonZeroExit_and_runChecked_rejectsIt :
    AllPass (test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt mockApi) := by
  intro s₀ req
  simp only [mockApi, Internal.mkApiM]
  cases hRun : Internal.run mockRawOps req s₀ with
  | mk res s₁ =>
    have hRunS : StateT.run (Internal.run mockRawOps req) s₀ = (res, s₁) := hRun
    rw [hRunS]
    cases res with
    | error _ => simp [assume]
    | ok out =>
      intro hnz
      have hbeq : (out.exitCode == 0) = false := beq_false_of_ne hnz
      simp only [Internal.runChecked, StateT.run, stateT_bind_apply, hRun, hbeq,
        Bool.false_eq_true, ↓reduceIte, StateT.pure, pure, assert]
      refine ⟨⟨⟨_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩, trivial⟩, trivial⟩
      simp [String.append_eq_empty_iff, toString]

/-- Non-vacuity `CanReach` witness for `test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt`. -/
theorem reach_process_run_allowsNonZeroExit_and_runChecked_rejectsIt :
    CanReach (test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt mockApi) := by
  let req : ExecRequest := { program := "__nonzero__" }
  let resOk : ExecResult := { exitCode := 1, stdout := ByteArray.empty, stderr := ByteArray.empty }
  let errNZ : ProcessError :=
    { kind := .nonZeroExit
      program := some "__nonzero__"
      exitCode := some 1
      stdout := some ByteArray.empty
      stderr := some ByteArray.empty
      message := "process '__nonzero__' exited with status 1" }
  have h1 : (mockApi.run req).run {} = (.ok resOk, {}) := by
    have hVal : Internal.validateRequest req = .ok req :=
      validateRequest_simple_ok "__nonzero__" (by decide) (by decide) none none (by decide)
    simp only [mockApi, Internal.mkApiM, Internal.run, hVal, mockRawOps, freshMockId, StateT.run]
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    simp +decide [req]
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    simp +decide
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    simp +decide [resOk]
    dsimp only [StateT.pure, Pure.pure]
  have h2 : (mockApi.runChecked req).run {} = (.error errNZ, {}) := by
    have hm : toString "process '" ++ toString "__nonzero__" ++ toString "' exited with status " ++
        Int.repr 1 = "process '__nonzero__' exited with status 1" := by decide
    simp only [mockApi, Internal.mkApiM] at h1 ⊢
    simp +decide [Internal.runChecked, StateT.run, stateT_bind_apply, StateT.pure, Pure.pure, pure,
      show Internal.run mockRawOps req {} = (.ok resOk, {}) from h1, resOk, errNZ, req, hm]
  refine ⟨{}, req, ?_⟩
  simp only [h1, h2, assume, assert]
  exact ⟨by decide, ⟨⟨errNZ, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩, trivial⟩, trivial⟩

/-- Proof of `test_process_runChecked_zeroExit_matchesRun` for `mockApi`. -/
theorem proof_process_runChecked_zeroExit_matchesRun :
    AllPass (test_process_runChecked_zeroExit_matchesRun mockApi) := by
  intro s₀ req
  simp only [mockApi, Internal.mkApiM]
  cases hRun : Internal.run mockRawOps req s₀ with
  | mk res s₁ =>
    have hRunS : StateT.run (Internal.run mockRawOps req) s₀ = (res, s₁) := hRun
    rw [hRunS]
    cases res with
    | error _ => simp [assume]
    | ok out =>
      intro hz
      simp [Internal.runChecked, StateT.run, stateT_bind_apply, StateT.pure, pure, hRun, hz, assert]

/-- Non-vacuity `CanReach` witness for `test_process_runChecked_zeroExit_matchesRun`. -/
theorem reach_process_runChecked_zeroExit_matchesRun :
    CanReach (test_process_runChecked_zeroExit_matchesRun mockApi) := by
  let req : ExecRequest := { program := "ok" }
  let resOk : ExecResult := { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
  have h1 : (mockApi.run req).run {} = (.ok resOk, {}) := by
    have hVal : Internal.validateRequest req = .ok req :=
      validateRequest_simple_ok "ok" (by decide) (by decide) none none (by decide)
    simp only [mockApi, Internal.mkApiM, Internal.run, hVal, mockRawOps, freshMockId, StateT.run]
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    simp +decide [req]
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    simp +decide
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    simp +decide [resOk]
    dsimp only [StateT.pure, Pure.pure]
  have h2 : (mockApi.runChecked req).run {} = (.ok resOk, {}) := by
    simp only [mockApi, Internal.mkApiM] at h1 ⊢
    simp [Internal.runChecked, StateT.run, stateT_bind_apply, StateT.pure, Pure.pure, pure,
      show Internal.run mockRawOps req {} = (.ok resOk, {}) from h1, resOk]
  refine ⟨{}, req, ?_⟩
  simp [h1, h2, assume, assert, resOk, Bind.bind]

/-- Proof of `test_process_runChecked_propagatesRunError` for `mockApi`. -/
theorem proof_process_runChecked_propagatesRunError :
    AllPass (test_process_runChecked_propagatesRunError mockApi) := by
  intro s₀ req
  simp only [mockApi, Internal.mkApiM]
  cases hRun : Internal.run mockRawOps req s₀ with
  | mk res s₁ =>
    have hRunS : StateT.run (Internal.run mockRawOps req) s₀ = (res, s₁) := hRun
    rw [hRunS]
    cases res with
    | ok _ => simp [assume]
    | error err =>
      simp only [Internal.runChecked, StateT.run, stateT_bind_apply, hRun, StateT.pure, pure,
        assert]
      trivial

/-- Non-vacuity `CanReach` witness for `test_process_runChecked_propagatesRunError`. -/
theorem reach_process_runChecked_propagatesRunError :
    CanReach (test_process_runChecked_propagatesRunError mockApi) := by
  let req : ExecRequest := { program := "__spawn_err__" }
  let errSp : ProcessError :=
    { kind := .notFound
      program := some "__spawn_err__"
      errnoCode := some 2
      message := "not found" }
  have h1 : (mockApi.run req).run {} = (.error errSp, {}) := by
    have hVal : Internal.validateRequest req = .ok req :=
      validateRequest_simple_ok "__spawn_err__" (by decide) (by decide) none none (by decide)
    simp only [mockApi, Internal.mkApiM, Internal.run, hVal, mockRawOps,
      Internal.ensureNonEmptyMsg, Raw.Internal.mapRawError, Raw.Internal.nonEmptyMsg, StateT.run]
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    simp +decide [req, errSp]
    dsimp only [StateT.pure, Pure.pure]
  have h2 : (mockApi.runChecked req).run {} = (.error errSp, {}) := by
    simp only [mockApi, Internal.mkApiM] at h1 ⊢
    simp [Internal.runChecked, StateT.run, stateT_bind_apply, StateT.pure, Pure.pure, pure,
      show Internal.run mockRawOps req {} = (.error errSp, {}) from h1]
  refine ⟨{}, req, ?_⟩
  simp [h1, h2, assert]

/-- Proof of `test_process_run_neverLeaksProcesses` for `mockApi`. -/
theorem proof_process_run_neverLeaksProcesses :
    AllPass (test_process_run_neverLeaksProcesses mockApi) := by
  intro s₀ req
  have hAct := (mockApi_run_spawn_props s₀ req).1
  simp only [mockApi, Internal.mkApiM, mockRawOps, StateT.run, assert]
  exact ⟨congrArg List.length hAct, trivial⟩

private theorem mockApi_run_ok_eq :
    (mockApi.run { program := "ok" }).run {} =
      (.ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }, {}) := by
  have hVal : Internal.validateRequest { program := "ok" } = .ok { program := "ok" } :=
    validateRequest_simple_ok "ok" (by decide) (by decide) none none (by decide)
  simp only [mockApi, Internal.mkApiM, Internal.run, hVal, mockRawOps, freshMockId, StateT.run]
  dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
  simp +decide
  dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
  simp +decide
  dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
  simp +decide
  dsimp only [StateT.pure, Pure.pure]

/-- Non-vacuity `CanReach` witness for `test_process_run_neverLeaksProcesses`. -/
theorem reach_process_run_neverLeaksProcesses :
    CanReach (test_process_run_neverLeaksProcesses mockApi) := by
  refine ⟨{}, { program := "ok" }, ?_⟩
  dsimp only
  rw [mockApi_run_ok_eq]
  simp [mockApi, Internal.mkApiM, mockRawOps, StateT.run, assert]

/-- Proof of `test_process_runChecked_neverLeaksProcesses` for `mockApi`. -/
theorem proof_process_runChecked_neverLeaksProcesses :
    AllPass (test_process_runChecked_neverLeaksProcesses mockApi) := by
  intro s₀ req
  have hAct := (mockApi_run_spawn_props s₀ req).1
  simp only [mockApi, Internal.mkApiM, Internal.runChecked, StateT.run, stateT_bind_apply]
  cases hRun : Internal.run mockRawOps req s₀ with
  | mk res s₁ =>
    rw [hRun] at hAct
    cases res with
    | error _ =>
      simp only [mockRawOps, StateT.pure, pure, assert]
      exact ⟨congrArg List.length hAct, trivial⟩
    | ok out =>
      dsimp only
      split <;> (simp only [mockRawOps, StateT.pure, pure, assert]; exact ⟨congrArg List.length hAct, trivial⟩)

/-- Non-vacuity `CanReach` witness for `test_process_runChecked_neverLeaksProcesses`. -/
theorem reach_process_runChecked_neverLeaksProcesses :
    CanReach (test_process_runChecked_neverLeaksProcesses mockApi) := by
  refine ⟨{}, { program := "ok" }, ?_⟩
  dsimp only
  simp only [mockApi, Internal.mkApiM, Internal.runChecked, StateT.run, stateT_bind_apply]
  have h1 : Internal.run mockRawOps { program := "ok" } {} =
      (.ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }, {}) :=
    mockApi_run_ok_eq
  rw [h1]
  simp +decide [StateT.pure, Pure.pure, pure, assert]

/-- Proof of `test_process_timeout_cleansUpAndErrors` for `mockApi`. -/
theorem proof_process_timeout_cleansUpAndErrors :
    AllPass (test_process_timeout_cleansUpAndErrors mockApi) := by
  intro s₀ req _
  have hProps := mockApi_run_spawn_props s₀ req
  simp only [mockApi, Internal.mkApiM]
  cases hRun : Internal.run mockRawOps req s₀ with
  | mk res s₁ =>
    have hRunS : StateT.run (Internal.run mockRawOps req) s₀ = (res, s₁) := hRun
    rw [hRunS]
    cases res with
    | ok _ => simp [assume]
    | error err =>
      intro hk
      rw [hRun] at hProps
      have hT := (hProps.2.1 err rfl).2.1 hk
      simp only [mockRawOps, StateT.run, assert]
      exact ⟨⟨hT.2, (hProps.2.1 err rfl).1, congrArg List.length hProps.1⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_process_timeout_cleansUpAndErrors`. -/
theorem reach_process_timeout_cleansUpAndErrors :
    CanReach (test_process_timeout_cleansUpAndErrors mockApi) := by
  let req : ExecRequest := { program := "__timed_out__", timeoutMs := some 10 }
  let errTO : ProcessError :=
    { kind := .timedOut
      program := some "__timed_out__"
      stdout := some ByteArray.empty
      stderr := some ByteArray.empty
      message := "process '__timed_out__' timed out" }
  have h1 : (mockApi.run req).run {} = (.error errTO, {}) := by
    have hVal : Internal.validateRequest req = .ok req :=
      validateRequest_simple_ok "__timed_out__" (by decide) (by decide) (some 10) none (by decide)
    simp only [mockApi, Internal.mkApiM, Internal.run, hVal, mockRawOps, freshMockId, StateT.run]
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    simp +decide [req]
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    simp +decide
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    have hm : toString "process '" ++ toString "__timed_out__" ++ toString "' timed out" =
        "process '__timed_out__' timed out" := by decide
    simp +decide [errTO, hm]
  refine ⟨{}, req, by decide, ?_⟩
  simp only [mockApi, Internal.mkApiM, StateT.run] at h1 ⊢
  rw [h1]
  simp [mockRawOps, assume, assert, errTO, Bind.bind, req]

/-- Proof of `test_process_run_noTimeout_neverTimesOut` for `mockApi`. -/
theorem proof_process_run_noTimeout_neverTimesOut :
    AllPass (test_process_run_noTimeout_neverTimesOut mockApi) := by
  intro s₀ req hNone
  have hProps := mockApi_run_spawn_props s₀ req
  simp only [mockApi, Internal.mkApiM]
  cases hRun : Internal.run mockRawOps req s₀ with
  | mk res s₁ =>
    have hRunS : StateT.run (Internal.run mockRawOps req) s₀ = (res, s₁) := hRun
    rw [hRunS]
    cases res with
    | ok _ => trivial
    | error err =>
      rw [hRun] at hProps
      simp only [assert]
      refine ⟨?_, trivial⟩
      intro hk
      have hTis := ((hProps.2.1 err rfl).2.1 hk).1
      simp [hNone] at hTis

/-- Non-vacuity `CanReach` witness for `test_process_run_noTimeout_neverTimesOut`. -/
theorem reach_process_run_noTimeout_neverTimesOut :
    CanReach (test_process_run_noTimeout_neverTimesOut mockApi) := by
  let req : ExecRequest := { program := "ok", timeoutMs := none }
  refine ⟨{}, req, rfl, ?_⟩
  dsimp only
  rw [show (mockApi.run req).run {} = _ from mockApi_run_ok_eq]
  simp [Pure.pure, pure]

/-- Proof of `test_process_outputLimit_cleansUpAndErrors` for `mockApi`. -/
theorem proof_process_outputLimit_cleansUpAndErrors :
    AllPass (test_process_outputLimit_cleansUpAndErrors mockApi) := by
  intro s₀ req _
  have hProps := mockApi_run_spawn_props s₀ req
  simp only [mockApi, Internal.mkApiM]
  cases hRun : Internal.run mockRawOps req s₀ with
  | mk res s₁ =>
    have hRunS : StateT.run (Internal.run mockRawOps req) s₀ = (res, s₁) := hRun
    rw [hRunS]
    cases res with
    | ok _ => simp [assume]
    | error err =>
      intro hk
      rw [hRun] at hProps
      have hM := (hProps.2.1 err rfl).2.2.1 hk
      simp only [mockRawOps, StateT.run, assert]
      exact ⟨⟨hM.2, (hProps.2.1 err rfl).1, congrArg List.length hProps.1⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_process_outputLimit_cleansUpAndErrors`. -/
theorem reach_process_outputLimit_cleansUpAndErrors :
    CanReach (test_process_outputLimit_cleansUpAndErrors mockApi) := by
  let req : ExecRequest := { program := "__output_limit__", maxOutputBytes := some 10 }
  let errOL : ProcessError :=
    { kind := .outputLimitExceeded
      program := some "__output_limit__"
      stdout := some ByteArray.empty
      stderr := some ByteArray.empty
      message := "process '__output_limit__' exceeded output byte limit" }
  have h1 : (mockApi.run req).run {} = (.error errOL, {}) := by
    have hVal : Internal.validateRequest req = .ok req :=
      validateRequest_simple_ok "__output_limit__" (by decide) (by decide) none (some 10) (by decide)
    simp only [mockApi, Internal.mkApiM, Internal.run, hVal, mockRawOps, freshMockId, StateT.run]
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    simp +decide [req]
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    simp +decide
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    have hm : toString "process '" ++ toString "__output_limit__" ++
        toString "' exceeded output byte limit" =
        "process '__output_limit__' exceeded output byte limit" := by decide
    simp +decide [errOL, hm]
  refine ⟨{}, req, by decide, ?_⟩
  simp only [mockApi, Internal.mkApiM, StateT.run] at h1 ⊢
  rw [h1]
  simp [mockRawOps, assume, assert, errOL, Bind.bind, req]

/-- Proof of `test_process_run_noOutputLimit_neverExceedsLimit` for `mockApi`. -/
theorem proof_process_run_noOutputLimit_neverExceedsLimit :
    AllPass (test_process_run_noOutputLimit_neverExceedsLimit mockApi) := by
  intro s₀ req hNone
  have hProps := mockApi_run_spawn_props s₀ req
  simp only [mockApi, Internal.mkApiM]
  cases hRun : Internal.run mockRawOps req s₀ with
  | mk res s₁ =>
    have hRunS : StateT.run (Internal.run mockRawOps req) s₀ = (res, s₁) := hRun
    rw [hRunS]
    cases res with
    | ok _ => trivial
    | error err =>
      rw [hRun] at hProps
      simp only [assert]
      refine ⟨?_, trivial⟩
      intro hk
      have hMis := ((hProps.2.1 err rfl).2.2.1 hk).1
      simp [hNone] at hMis

/-- Non-vacuity `CanReach` witness for `test_process_run_noOutputLimit_neverExceedsLimit`. -/
theorem reach_process_run_noOutputLimit_neverExceedsLimit :
    CanReach (test_process_run_noOutputLimit_neverExceedsLimit mockApi) := by
  let req : ExecRequest := { program := "ok", maxOutputBytes := none }
  refine ⟨{}, req, rfl, ?_⟩
  dsimp only
  rw [show (mockApi.run req).run {} = _ from mockApi_run_ok_eq]
  simp [Pure.pure, pure]

/-- Proof of `test_process_run_respectsMaxOutputBytes` for `mockApi`. -/
theorem proof_process_run_respectsMaxOutputBytes :
    AllPass (test_process_run_respectsMaxOutputBytes mockApi) := by
  intro s₀ req limit _
  have hProps := mockApi_run_spawn_props s₀ req
  simp only [mockApi, Internal.mkApiM]
  cases hRun : Internal.run mockRawOps req s₀ with
  | mk res s₁ =>
    have hRunS : StateT.run (Internal.run mockRawOps req) s₀ = (res, s₁) := hRun
    rw [hRunS]
    cases res with
    | error _ => simp [assume]
    | ok out =>
      rw [hRun] at hProps
      have ⟨ho, he⟩ := hProps.2.2 out rfl
      simp [ho, he, assert]

/-- Non-vacuity `CanReach` witness for `test_process_run_respectsMaxOutputBytes`. -/
theorem reach_process_run_respectsMaxOutputBytes :
    CanReach (test_process_run_respectsMaxOutputBytes mockApi) := by
  let req : ExecRequest := { program := "ok", maxOutputBytes := some 10 }
  let resOk : ExecResult := { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
  have h1 : (mockApi.run req).run {} = (.ok resOk, {}) := by
    have hVal : Internal.validateRequest req = .ok req :=
      validateRequest_simple_ok "ok" (by decide) (by decide) none (some 10) (by decide)
    simp only [mockApi, Internal.mkApiM, Internal.run, hVal, mockRawOps, freshMockId, StateT.run]
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    simp +decide [req]
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    simp +decide
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    simp +decide [resOk]
    dsimp only [StateT.pure, Pure.pure]
  refine ⟨{}, req, 10, rfl, ?_⟩
  simp [h1, assert, resOk]

/-- Proof of `test_process_signaled_cleansUpAndErrors` for `mockApi`. -/
theorem proof_process_signaled_cleansUpAndErrors :
    AllPass (test_process_signaled_cleansUpAndErrors mockApi) := by
  intro s₀ req
  have hProps := mockApi_run_spawn_props s₀ req
  simp only [mockApi, Internal.mkApiM]
  cases hRun : Internal.run mockRawOps req s₀ with
  | mk res s₁ =>
    have hRunS : StateT.run (Internal.run mockRawOps req) s₀ = (res, s₁) := hRun
    rw [hRunS]
    cases res with
    | ok _ => simp [assume]
    | error err =>
      intro hk
      rw [hRun] at hProps
      have hS := (hProps.2.1 err rfl).2.2.2 hk
      simp only [mockRawOps, StateT.run, assert]
      exact ⟨⟨hS.1, hS.2, (hProps.2.1 err rfl).1, congrArg List.length hProps.1⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_process_signaled_cleansUpAndErrors`. -/
theorem reach_process_signaled_cleansUpAndErrors :
    CanReach (test_process_signaled_cleansUpAndErrors mockApi) := by
  let req : ExecRequest := { program := "__signaled__" }
  let errSig : ProcessError :=
    { kind := .terminatedBySignal
      program := some "__signaled__"
      signal := some 9
      stdout := some ByteArray.empty
      stderr := some ByteArray.empty
      message := "process '__signaled__' terminated by signal 9" }
  have h1 : (mockApi.run req).run {} = (.error errSig, {}) := by
    have hVal : Internal.validateRequest req = .ok req :=
      validateRequest_simple_ok "__signaled__" (by decide) (by decide) none none (by decide)
    simp only [mockApi, Internal.mkApiM, Internal.run, hVal, mockRawOps, freshMockId, StateT.run]
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    simp +decide [req]
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    simp +decide
    dsimp only [StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map]
    have hm : toString "process '" ++ toString "__signaled__" ++ toString "' terminated by signal " ++
        Int.repr 9 = "process '__signaled__' terminated by signal 9" := by decide
    simp +decide [errSig, hm]
  refine ⟨{}, req, ?_⟩
  simp only [mockApi, Internal.mkApiM, StateT.run] at h1 ⊢
  rw [h1]
  simp [mockRawOps, assume, assert, errSig, Bind.bind, req]

/-- Proof of `test_process_run_onError_returnsNonEmptyMessage` for `mockApi`. -/
theorem proof_process_run_onError_returnsNonEmptyMessage :
    AllPass (test_process_run_onError_returnsNonEmptyMessage mockApi) := by
  intro s₀ req
  have hProps := mockApi_run_spawn_props s₀ req
  simp only [mockApi, Internal.mkApiM]
  cases hRun : Internal.run mockRawOps req s₀ with
  | mk res s₁ =>
    have hRunS : StateT.run (Internal.run mockRawOps req) s₀ = (res, s₁) := hRun
    rw [hRunS]
    cases res with
    | ok _ => simp [assume]
    | error err =>
      rw [hRun] at hProps
      simp [(hProps.2.1 err rfl).1, assert]

/-- Non-vacuity `CanReach` witness for `test_process_run_onError_returnsNonEmptyMessage`. -/
theorem reach_process_run_onError_returnsNonEmptyMessage :
    CanReach (test_process_run_onError_returnsNonEmptyMessage mockApi) := by
  let req : ExecRequest := { program := "" }
  refine ⟨{}, req, ?_⟩
  dsimp only [mockApi, Internal.mkApiM, Internal.run, StateT.run]
  simp +decide [Internal.validateRequest, req]
  simp +decide [StateT.pure, Pure.pure, pure, assert]

/-- Proof of `test_process_runChecked_onError_returnsNonEmptyMessage` for `mockApi`. -/
theorem proof_process_runChecked_onError_returnsNonEmptyMessage :
    AllPass (test_process_runChecked_onError_returnsNonEmptyMessage mockApi) := by
  intro s₀ req
  have hProps := mockApi_run_spawn_props s₀ req
  simp only [mockApi, Internal.mkApiM, Internal.runChecked, StateT.run, stateT_bind_apply]
  cases hRun : Internal.run mockRawOps req s₀ with
  | mk res s₁ =>
    cases res with
    | error err =>
      rw [hRun] at hProps
      simp only [StateT.pure, pure, assert]
      exact ⟨(hProps.2.1 err rfl).1, trivial⟩
    | ok out =>
      dsimp only
      split
      · simp [StateT.pure, pure, assume]
      · simp [StateT.pure, pure, String.append_eq_empty_iff, toString, assert]

/-- Non-vacuity `CanReach` witness for `test_process_runChecked_onError_returnsNonEmptyMessage`. -/
theorem reach_process_runChecked_onError_returnsNonEmptyMessage :
    CanReach (test_process_runChecked_onError_returnsNonEmptyMessage mockApi) := by
  let req : ExecRequest := { program := "" }
  refine ⟨{}, req, ?_⟩
  simp [mockApi, Internal.mkApiM, Internal.runChecked, Internal.run, Internal.validateRequest,
    StateT.run, stateT_bind_apply, StateT.pure, pure, assert, String.isEmpty, req]

end LeanSwe.Process.Proofs
