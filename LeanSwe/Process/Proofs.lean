import LeanSwe.Process.Types
import LeanSwe.Process.SysBridge
import LeanSwe.Process.Interface
import LeanSwe.Process.Impl
import LeanSwe.Process.SpecTests
import LeanSwe.Process.Proofs.EndToEnd

namespace LeanSwe.Process.Proofs

open Core
open Core.NondetTest
open LeanSwe.Process

private theorem nonEmptyMsg_ne_empty (fallback msg : String) (hf : fallback ≠ "") :
    SysBridge.nonEmptyMsg fallback msg ≠ "" := by
  unfold SysBridge.nonEmptyMsg
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
  simp only [defaultApi, Internal.mkApiM, SysBridge.defaultOps, SysBridge.mkRawOpsM,
    SysBridge.mapRawError, assert]
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
    simp [defaultApi, Internal.mkApiM, SysBridge.defaultOps, SysBridge.mkRawOpsM,
      SysBridge.mapRawError, assert]

/-- Non-vacuity `CanReach` witness for `test_process_mapRawError_preservesKindAndFields`. -/
theorem reach_process_mapRawError_preservesKindAndFields :
    CanReach (test_process_mapRawError_preservesKindAndFields defaultApi) :=
  ⟨.userError "err", by
    simp [defaultApi, Internal.mkApiM, SysBridge.defaultOps, SysBridge.mkRawOpsM,
      SysBridge.mapRawError, assert]⟩

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

/-- Proof of `test_process_run_invalidRequest_doesNotLeak` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_run_invalidRequest_doesNotLeak :
    AllPass (test_process_run_invalidRequest_doesNotLeak healthySimApi) :=
  healthySimApi_allStatefulSpecs.1

/-- Non-vacuity `CanReach` witness for `test_process_run_invalidRequest_doesNotLeak`. -/
theorem reach_process_run_invalidRequest_doesNotLeak :
    CanReach (test_process_run_invalidRequest_doesNotLeak healthySimApi) :=
  ⟨{}, { program := "" }, proof_process_run_invalidRequest_doesNotLeak {} { program := "" }⟩

/-- Proof of `test_process_run_usesNormalizedRequest` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_run_usesNormalizedRequest :
    AllPass (test_process_run_usesNormalizedRequest healthySimApi) :=
  healthySimApi_allStatefulSpecs.2.1

/-- Non-vacuity `CanReach` witness for `test_process_run_usesNormalizedRequest`. -/
theorem reach_process_run_usesNormalizedRequest :
    CanReach (test_process_run_usesNormalizedRequest healthySimApi) :=
  ⟨{}, { program := "/bin/true" }, proof_process_run_usesNormalizedRequest {} { program := "/bin/true" }⟩

/-- Proof of `test_process_runCommand_eq_runMkCommandRequest` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_runCommand_eq_runMkCommandRequest :
    AllPass (test_process_runCommand_eq_runMkCommandRequest healthySimApi) :=
  healthySimApi_allStatefulSpecs.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_runCommand_eq_runMkCommandRequest`. -/
theorem reach_process_runCommand_eq_runMkCommandRequest :
    CanReach (test_process_runCommand_eq_runMkCommandRequest healthySimApi) :=
  ⟨{}, "/bin/true", #["a"], proof_process_runCommand_eq_runMkCommandRequest {} "/bin/true" #["a"]⟩

/-- Proof of `test_process_runCommandChecked_eq_runCheckedMkCommandRequest` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_runCommandChecked_eq_runCheckedMkCommandRequest :
    AllPass (test_process_runCommandChecked_eq_runCheckedMkCommandRequest healthySimApi) :=
  healthySimApi_allStatefulSpecs.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_runCommandChecked_eq_runCheckedMkCommandRequest`. -/
theorem reach_process_runCommandChecked_eq_runCheckedMkCommandRequest :
    CanReach (test_process_runCommandChecked_eq_runCheckedMkCommandRequest healthySimApi) :=
  ⟨{}, "/bin/true", #["a"], proof_process_runCommandChecked_eq_runCheckedMkCommandRequest {} "/bin/true" #["a"]⟩

/-- Proof of `test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_run_allowsNonZeroExit_and_runChecked_rejectsIt :
    AllPass (test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt healthySimApi) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt`. -/
theorem reach_process_run_allowsNonZeroExit_and_runChecked_rejectsIt :
    CanReach (test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt healthySimApi) := by
  let req : ExecRequest := { program := "/bin/exit1", inheritEnv := false }
  refine ⟨{}, req, ?_⟩
  have hAll := proof_process_run_allowsNonZeroExit_and_runChecked_rejectsIt {} req
  dsimp only [AllPass, CanReach, test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt, nondet, bind] at hAll ⊢
  cases hRun : (healthySimApi.run req).run {} with
  | mk res s₁ =>
    cases res with
    | error _ =>
      have hOk : ((healthySimApi.run req).run {}).1.isOk = true := by decide +kernel
      rw [hRun] at hOk; cases hOk
    | ok out =>
      have hNz : out.exitCode ≠ 0 := by
        have hb : (match ((healthySimApi.run req).run {}).1 with | .ok o => o.exitCode != 0 | .error _ => false) = true := by
          decide +kernel
        rw [hRun] at hb; exact bne_iff_ne.mp hb
      cases hChk : (healthySimApi.runChecked req).run {} with
      | mk cr s₂ =>
        rw [hRun, hChk] at hAll
        dsimp only [assume, assert] at hAll ⊢
        exact ⟨hNz, hAll hNz⟩

/-- Proof of `test_process_runChecked_zeroExit_matchesRun` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_runChecked_zeroExit_matchesRun :
    AllPass (test_process_runChecked_zeroExit_matchesRun healthySimApi) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_runChecked_zeroExit_matchesRun`. -/
theorem reach_process_runChecked_zeroExit_matchesRun :
    CanReach (test_process_runChecked_zeroExit_matchesRun healthySimApi) := by
  let req : ExecRequest := { program := "/bin/true", inheritEnv := false }
  refine ⟨{}, req, ?_⟩
  have hAll := proof_process_runChecked_zeroExit_matchesRun {} req
  dsimp only [AllPass, CanReach, test_process_runChecked_zeroExit_matchesRun, nondet, bind] at hAll ⊢
  cases hRun : (healthySimApi.run req).run {} with
  | mk res s₁ =>
    cases res with
    | error _ =>
      have hOk : ((healthySimApi.run req).run {}).1.isOk = true := by decide +kernel
      rw [hRun] at hOk; cases hOk
    | ok out =>
      have hZ : out.exitCode = 0 := by
        have hb : (match ((healthySimApi.run req).run {}).1 with | .ok o => o.exitCode == 0 | .error _ => false) = true := by
          decide +kernel
        rw [hRun] at hb; exact beq_iff_eq.mp hb
      rw [hRun] at hAll
      dsimp only [assume, assert] at hAll ⊢
      exact ⟨hZ, hAll hZ⟩

/-- Proof of `test_process_runChecked_propagatesRunError` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_runChecked_propagatesRunError :
    AllPass (test_process_runChecked_propagatesRunError healthySimApi) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_runChecked_propagatesRunError`. -/
theorem reach_process_runChecked_propagatesRunError :
    CanReach (test_process_runChecked_propagatesRunError healthySimApi) :=
  ⟨{}, { program := "" }, proof_process_runChecked_propagatesRunError {} { program := "" }⟩

/-- Proof of `test_process_run_neverLeaksProcesses` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_run_neverLeaksProcesses :
    AllPass (test_process_run_neverLeaksProcesses healthySimApi) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_run_neverLeaksProcesses`. -/
theorem reach_process_run_neverLeaksProcesses :
    CanReach (test_process_run_neverLeaksProcesses healthySimApi) :=
  ⟨{}, { program := "" }, proof_process_run_neverLeaksProcesses {} { program := "" }⟩

/-- Proof of `test_process_runChecked_neverLeaksProcesses` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_runChecked_neverLeaksProcesses :
    AllPass (test_process_runChecked_neverLeaksProcesses healthySimApi) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_runChecked_neverLeaksProcesses`. -/
theorem reach_process_runChecked_neverLeaksProcesses :
    CanReach (test_process_runChecked_neverLeaksProcesses healthySimApi) :=
  ⟨{}, { program := "" }, proof_process_runChecked_neverLeaksProcesses {} { program := "" }⟩

/-- Proof of `test_process_timeout_cleansUpAndErrors` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_timeout_cleansUpAndErrors :
    AllPass (test_process_timeout_cleansUpAndErrors healthySimApi) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_timeout_cleansUpAndErrors`. -/
theorem reach_process_timeout_cleansUpAndErrors :
    CanReach (test_process_timeout_cleansUpAndErrors healthySimApi) := by
  let req : ExecRequest := { program := "/bin/hang", inheritEnv := false, timeoutMs := some 1 }
  have hNe : req.timeoutMs ≠ none := by decide
  refine ⟨{}, req, ?_⟩
  have hAll := proof_process_timeout_cleansUpAndErrors {} req hNe
  dsimp only [AllPass, CanReach, test_process_timeout_cleansUpAndErrors, nondet, bind] at hAll ⊢
  refine ⟨hNe, ?_⟩
  cases hRun : (healthySimApi.run req).run {} with
  | mk res s₁ =>
    cases res with
    | ok _ =>
      have hErr : ((healthySimApi.run req).run {}).1.isOk = false := by decide +kernel
      rw [hRun] at hErr; cases hErr
    | error err =>
      have hK : err.kind = .timedOut := by
        have hb : (match ((healthySimApi.run req).run {}).1 with | .error e => decide (e.kind = .timedOut) | .ok _ => false) = true := by
          decide +kernel
        rw [hRun] at hb; exact of_decide_eq_true hb
      rw [hRun] at hAll
      dsimp only [assume, assert] at hAll ⊢
      exact ⟨hK, hAll hK⟩

/-- Proof of `test_process_run_noTimeout_neverTimesOut` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_run_noTimeout_neverTimesOut :
    AllPass (test_process_run_noTimeout_neverTimesOut healthySimApi) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_run_noTimeout_neverTimesOut`. -/
theorem reach_process_run_noTimeout_neverTimesOut :
    CanReach (test_process_run_noTimeout_neverTimesOut healthySimApi) :=
  ⟨{}, { program := "", timeoutMs := none }, rfl,
    proof_process_run_noTimeout_neverTimesOut {} { program := "", timeoutMs := none } rfl⟩

/-- Proof of `test_process_outputLimit_cleansUpAndErrors` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_outputLimit_cleansUpAndErrors :
    AllPass (test_process_outputLimit_cleansUpAndErrors healthySimApi) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_outputLimit_cleansUpAndErrors`. -/
theorem reach_process_outputLimit_cleansUpAndErrors :
    CanReach (test_process_outputLimit_cleansUpAndErrors healthySimApi) := by
  let req : ExecRequest := { program := "/bin/bigout", inheritEnv := false, maxOutputBytes := some 4 }
  have hNe : req.maxOutputBytes ≠ none := by decide
  refine ⟨{}, req, ?_⟩
  have hAll := proof_process_outputLimit_cleansUpAndErrors {} req hNe
  dsimp only [AllPass, CanReach, test_process_outputLimit_cleansUpAndErrors, nondet, bind] at hAll ⊢
  refine ⟨hNe, ?_⟩
  cases hRun : (healthySimApi.run req).run {} with
  | mk res s₁ =>
    cases res with
    | ok _ =>
      have hErr : ((healthySimApi.run req).run {}).1.isOk = false := by decide +kernel
      rw [hRun] at hErr; cases hErr
    | error err =>
      have hK : err.kind = .outputLimitExceeded := by
        have hb : (match ((healthySimApi.run req).run {}).1 with | .error e => decide (e.kind = .outputLimitExceeded) | .ok _ => false) = true := by
          decide +kernel
        rw [hRun] at hb; exact of_decide_eq_true hb
      rw [hRun] at hAll
      dsimp only [assume, assert] at hAll ⊢
      exact ⟨hK, hAll hK⟩

/-- Proof of `test_process_run_noOutputLimit_neverExceedsLimit` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_run_noOutputLimit_neverExceedsLimit :
    AllPass (test_process_run_noOutputLimit_neverExceedsLimit healthySimApi) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_run_noOutputLimit_neverExceedsLimit`. -/
theorem reach_process_run_noOutputLimit_neverExceedsLimit :
    CanReach (test_process_run_noOutputLimit_neverExceedsLimit healthySimApi) :=
  ⟨{}, { program := "", maxOutputBytes := none }, rfl,
    proof_process_run_noOutputLimit_neverExceedsLimit {} { program := "", maxOutputBytes := none } rfl⟩

/-- Proof of `test_process_run_respectsMaxOutputBytes` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_run_respectsMaxOutputBytes :
    AllPass (test_process_run_respectsMaxOutputBytes healthySimApi) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_run_respectsMaxOutputBytes`. -/
theorem reach_process_run_respectsMaxOutputBytes :
    CanReach (test_process_run_respectsMaxOutputBytes healthySimApi) := by
  let req : ExecRequest := { program := "/bin/true", inheritEnv := false, maxOutputBytes := some 10 }
  refine ⟨{}, req, 10, rfl, ?_⟩
  have hAll := proof_process_run_respectsMaxOutputBytes {} req 10 rfl
  dsimp only [AllPass, CanReach, test_process_run_respectsMaxOutputBytes, nondet, bind] at hAll ⊢
  cases hRun : (healthySimApi.run req).run {} with
  | mk res s₁ =>
    cases res with
    | error _ =>
      have hOk : ((healthySimApi.run req).run {}).1.isOk = true := by decide +kernel
      rw [hRun] at hOk; cases hOk
    | ok out =>
      rw [hRun] at hAll
      exact hAll

/-- Proof of `test_process_signaled_cleansUpAndErrors` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_signaled_cleansUpAndErrors :
    AllPass (test_process_signaled_cleansUpAndErrors healthySimApi) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_signaled_cleansUpAndErrors`. -/
theorem reach_process_signaled_cleansUpAndErrors :
    CanReach (test_process_signaled_cleansUpAndErrors healthySimApi) := by
  let req : ExecRequest := { program := "/bin/sig9", inheritEnv := false }
  refine ⟨{}, req, ?_⟩
  have hAll := proof_process_signaled_cleansUpAndErrors {} req
  dsimp only [AllPass, CanReach, test_process_signaled_cleansUpAndErrors, nondet, bind] at hAll ⊢
  cases hRun : (healthySimApi.run req).run {} with
  | mk res s₁ =>
    cases res with
    | ok _ =>
      have hErr : ((healthySimApi.run req).run {}).1.isOk = false := by decide +kernel
      rw [hRun] at hErr; cases hErr
    | error err =>
      have hK : err.kind = .terminatedBySignal := by
        have hb : (match ((healthySimApi.run req).run {}).1 with | .error e => decide (e.kind = .terminatedBySignal) | .ok _ => false) = true := by
          decide +kernel
        rw [hRun] at hb; exact of_decide_eq_true hb
      rw [hRun] at hAll
      dsimp only [assume, assert] at hAll ⊢
      exact ⟨hK, hAll hK⟩

/-- Proof of `test_process_run_onError_returnsNonEmptyMessage` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_run_onError_returnsNonEmptyMessage :
    AllPass (test_process_run_onError_returnsNonEmptyMessage healthySimApi) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_run_onError_returnsNonEmptyMessage`. -/
theorem reach_process_run_onError_returnsNonEmptyMessage :
    CanReach (test_process_run_onError_returnsNonEmptyMessage healthySimApi) :=
  ⟨{}, { program := "" }, proof_process_run_onError_returnsNonEmptyMessage {} { program := "" }⟩

/-- Proof of `test_process_runChecked_onError_returnsNonEmptyMessage` via `SysBridge.mkRawOpsM` (`healthySimApi`). -/
theorem proof_process_runChecked_onError_returnsNonEmptyMessage :
    AllPass (test_process_runChecked_onError_returnsNonEmptyMessage healthySimApi) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Non-vacuity `CanReach` witness for `test_process_runChecked_onError_returnsNonEmptyMessage`. -/
theorem reach_process_runChecked_onError_returnsNonEmptyMessage :
    CanReach (test_process_runChecked_onError_returnsNonEmptyMessage healthySimApi) :=
  ⟨{}, { program := "" }, proof_process_runChecked_onError_returnsNonEmptyMessage {} { program := "" }⟩

/-- Proof of `test_process_sysBridge_resolveExecutablePath_relativeCwdAndPathRules` for `SysBridge.resolveExecutablePath`. -/
theorem proof_process_sysBridge_resolveExecutablePath_relativeCwdAndPathRules :
    AllPass (test_process_sysBridge_resolveExecutablePath_relativeCwdAndPathRules
      (@SysBridge.resolveExecutablePath (StateM PathProbeState) _ Nat)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

/-- Proof of `test_process_sysBridge_validateWorkingDir_chdirSemantics` for `SysBridge.validateWorkingDir`. -/
theorem proof_process_sysBridge_validateWorkingDir_chdirSemantics :
    AllPass (test_process_sysBridge_validateWorkingDir_chdirSemantics
      SysBridge.probePathBytes
      (@SysBridge.validateWorkingDir (StateM PathProbeState) _ Nat)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

/-- Proof of `test_process_sysBridge_streamPipes_shortReadWriteEagainEintrReassembly` for `SysBridge.streamPipesLoop`. -/
theorem proof_process_sysBridge_streamPipes_shortReadWriteEagainEintrReassembly :
    AllPass (test_process_sysBridge_streamPipes_shortReadWriteEagainEintrReassembly
      (@SysBridge.streamPipesLoop (StateM PipeScriptState) _ Nat)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

/-- Proof of `test_process_sysBridge_streamPipes_drainsStdinAfterOutErrEof` for `SysBridge.streamPipesLoop`. -/
theorem proof_process_sysBridge_streamPipes_drainsStdinAfterOutErrEof :
    AllPass (test_process_sysBridge_streamPipes_drainsStdinAfterOutErrEof
      (@SysBridge.streamPipesLoop (StateM PipeScriptState) _ Nat)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

/-- Proof of `test_process_sysBridge_maxOutputBytes_truncatesKillsAndReaps` for `SysBridge.mkRawOpsM`. -/
theorem proof_process_sysBridge_maxOutputBytes_truncatesKillsAndReaps :
    AllPass (test_process_sysBridge_maxOutputBytes_truncatesKillsAndReaps
      (@SysBridge.stateProcTableOps CapSimState Nat)
      (@SysBridge.mkRawOpsM (StateM CapSimState) _ Nat)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

/-- Proof of `test_process_sysBridge_partialPipe2Failure_cleansUpAllocatedFds` for `SysBridge.spawnPure`. -/
theorem proof_process_sysBridge_partialPipe2Failure_cleansUpAllocatedFds :
    AllPass (test_process_sysBridge_partialPipe2Failure_cleansUpAllocatedFds
      (@SysBridge.stateProcTableOps PipeFailSimState Nat)
      (@SysBridge.spawnPure (StateM PipeFailSimState) _ Nat)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

/-- Proof of `test_process_mkApiM_preservesExactAwaitOutcomes` for `Internal.mkApiM`. -/
theorem proof_process_mkApiM_preservesExactAwaitOutcomes :
    AllPass (test_process_mkApiM_preservesExactAwaitOutcomes
      SysBridge.mapRawError
      (@Internal.mkApiM (StateM OutcomeScriptState) _)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

/-- Proof of `test_process_sysBridge_spawnCwdIsolationKillPgid1AndChdirError` for `SysBridge.mkRawOpsM`. -/
theorem proof_process_sysBridge_spawnCwdIsolationKillPgid1AndChdirError :
    AllPass (test_process_sysBridge_spawnCwdIsolationKillPgid1AndChdirError
      (@SysBridge.stateProcTableOps SpawnAuditState Nat)
      (@SysBridge.mkRawOpsM (StateM SpawnAuditState) _ Nat)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

end LeanSwe.Process.Proofs
