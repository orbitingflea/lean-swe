import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.Interface
import LeanSwe.ProcessSandbox.SpecTests

namespace LeanSwe.ProcessSandbox.Proofs

open Core
open Core.NondetTest
open LeanSwe.ProcessSandbox
open LeanSwe.ProcessSandbox.Model

private theorem isEmpty_true_of_eq_empty {s : String} (h : s = "") : s.isEmpty = true := by
  subst h
  rfl

private theorem hasNulChar_iff (cs : List Char) :
    hasNulChar cs = true ↔ '\x00' ∈ cs := by
  induction cs with
  | nil => simp [hasNulChar]
  | cons c rest ih =>
    simp only [hasNulChar, Bool.or_eq_true, beq_iff_eq, List.mem_cons, ih]
    constructor
    · intro h
      rcases h with hc | hr
      · exact Or.inl hc.symm
      · exact Or.inr hr
    · intro h
      rcases h with hc | hr
      · exact Or.inl hc.symm
      · exact Or.inr hr

private theorem hasNulChar_eq_true_of_mem {cs : List Char} (h : '\x00' ∈ cs) :
    hasNulChar cs = true :=
  (hasNulChar_iff cs).mpr h

private theorem parseCleanAbsSegs_eq_none_of_normalize_eq_none {p : String}
    (h : normalizeCleanAbsPath p = none) : parseCleanAbsSegs p = none := by
  unfold normalizeCleanAbsPath at h
  cases hP : parseCleanAbsSegs p with
  | none => rfl
  | some segs => simp [hP] at h

private theorem validateAndNormalizeMount_error_props (m : SandboxMount) (e : SandboxError)
    (h : validateAndNormalizeMount m = .error e) :
    e.kind = .invalidInput ∧ e.message ≠ "" := by
  cases m with
  | readOnly hp bp =>
    unfold validateAndNormalizeMount at h
    cases h1 : parseCleanAbsSegs hp with
    | none =>
      simp only [h1] at h
      cases h
      exact ⟨rfl, by simp⟩
    | some _ =>
      cases h2 : parseCleanAbsSegs bp with
      | none =>
        simp only [h1, h2] at h
        cases h
        exact ⟨rfl, by simp⟩
      | some bSegs =>
        simp only [h1, h2] at h
        by_cases hRes : isReservedBoxSegs bSegs = true
        · simp only [hRes, ↓reduceIte] at h
          cases h
          exact ⟨rfl, by simp⟩
        · simp only [hRes, Bool.false_eq_true, ↓reduceIte] at h
          cases h
  | readWrite hp bp =>
    unfold validateAndNormalizeMount at h
    cases h1 : parseCleanAbsSegs hp with
    | none =>
      simp only [h1] at h
      cases h
      exact ⟨rfl, by simp⟩
    | some _ =>
      cases h2 : parseCleanAbsSegs bp with
      | none =>
        simp only [h1, h2] at h
        cases h
        exact ⟨rfl, by simp⟩
      | some bSegs =>
        simp only [h1, h2] at h
        by_cases hRes : isReservedBoxSegs bSegs = true
        · simp only [hRes, ↓reduceIte] at h
          cases h
          exact ⟨rfl, by simp⟩
        · simp only [hRes, Bool.false_eq_true, ↓reduceIte] at h
          cases h
  | scratch bp =>
    unfold validateAndNormalizeMount at h
    cases h2 : parseCleanAbsSegs bp with
    | none =>
      simp only [h2] at h
      cases h
      exact ⟨rfl, by simp⟩
    | some bSegs =>
      simp only [h2] at h
      by_cases hRes : isReservedBoxSegs bSegs = true
      · simp only [hRes, ↓reduceIte] at h
        cases h
        exact ⟨rfl, by simp⟩
      · simp only [hRes, Bool.false_eq_true, ↓reduceIte] at h
        cases h

private theorem validateMountsList_error_props (ms : List SandboxMount) (e : SandboxError)
    (h : validateMountsList ms = .error e) :
    e.kind = .invalidInput ∧ e.message ≠ "" := by
  induction ms with
  | nil => simp [validateMountsList] at h
  | cons m rest ih =>
    unfold validateMountsList at h
    dsimp only [bind, Except.bind] at h
    cases hm : validateAndNormalizeMount m with
    | error e₁ =>
      simp only [hm] at h
      cases h
      exact validateAndNormalizeMount_error_props m e hm
    | ok _ =>
      simp only [hm] at h
      cases hr : validateMountsList rest with
      | error e₂ =>
        simp only [hr] at h
        cases h
        exact ih hr
      | ok _ =>
        simp only [hr] at h
        cases h

private theorem validateSpecPure_error_props (spec : BoxSpec) (e : SandboxError)
    (h : validateSpecPure spec = .error e) :
    e.kind = .invalidInput ∧ e.message ≠ "" := by
  unfold validateSpecPure at h
  dsimp only [bind, Except.bind] at h
  by_cases h1 : spec.program.isEmpty = true
  · simp only [h1, ↓reduceIte] at h; cases h; exact ⟨rfl, by simp⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    by_cases h2 : hasNulChar spec.program.toList = true
    · simp only [h2, ↓reduceIte] at h; cases h; exact ⟨rfl, by simp⟩
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h3 : spec.args.toList.any (fun a => hasNulChar a.toList) = true
      · simp only [h3, ↓reduceIte] at h; cases h; exact ⟨rfl, by simp⟩
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
        cases hCwd : spec.cwd <;> simp only [hCwd] at h
        · cases hm : validateMountsList spec.mounts.toList <;> simp only [hm] at h
          · cases h; exact validateMountsList_error_props _ _ hm
          · repeat (first | cases h | exact ⟨rfl, by simp⟩ | split at h)
        · next d =>
          cases hNorm : normalizeCleanAbsPath d <;> simp only [hNorm] at h
          · cases h; exact ⟨rfl, by simp⟩
          · cases hm : validateMountsList spec.mounts.toList <;> simp only [hm] at h
            · cases h; exact validateMountsList_error_props _ _ hm
            · repeat (first | cases h | exact ⟨rfl, by simp⟩ | split at h)

private theorem validateSpecPure_ok_props {spec : BoxSpec} {valid : ValidBoxSpec}
    (h : validateSpecPure spec = .ok valid) :
    spec.program.isEmpty = false ∧
    hasNulChar spec.program.toList = false ∧
    spec.args.toList.any (fun a => hasNulChar a.toList) = false ∧
    (∀ d, spec.cwd = some d → (normalizeCleanAbsPath d).isSome = true) ∧
    spec.env.toList.all isValidEnvPair = true := by
  unfold validateSpecPure at h
  dsimp only [bind, Except.bind] at h
  by_cases h1 : spec.program.isEmpty = true
  · simp only [h1, ↓reduceIte] at h; cases h
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    by_cases h2 : hasNulChar spec.program.toList = true
    · simp only [h2, ↓reduceIte] at h; cases h
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h3 : spec.args.toList.any (fun a => hasNulChar a.toList) = true
      · simp only [h3, ↓reduceIte] at h; cases h
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
        refine ⟨Bool.eq_false_iff.mpr h1, Bool.eq_false_iff.mpr h2, Bool.eq_false_iff.mpr h3, ?_, ?_⟩
        · intro d hd
          simp only [hd] at h
          cases hNorm : normalizeCleanAbsPath d with
          | none => simp only [hNorm] at h; cases h
          | some _ => rfl
        · by_cases hEnv : spec.env.toList.all isValidEnvPair = true
          · exact hEnv
          · have hNotEnv : (!spec.env.toList.all isValidEnvPair) = true := by simp [hEnv]
            cases hCwd : spec.cwd <;> simp only [hCwd] at h
            · cases hm : validateMountsList spec.mounts.toList <;> simp only [hm] at h
              · cases h
              · simp only [hNotEnv, ↓reduceIte] at h
                repeat (first | cases h | split at h)
            · next d =>
              cases hNorm : normalizeCleanAbsPath d <;> simp only [hNorm] at h
              · cases h
              · cases hm : validateMountsList spec.mounts.toList <;> simp only [hm] at h
                · cases h
                · simp only [hNotEnv, ↓reduceIte] at h
                  repeat (first | cases h | split at h)

private theorem hasNulChar_binTrue :
    hasNulChar ['/', 'b', 'i', 'n', '/', 't', 'r', 'u', 'e'] = false := rfl

private theorem allDistinct_nil_str :
    allDistinct ([] : List String) = true := rfl

private theorem beq_invalidInput :
    ((.invalidInput : SandboxErrorKind) == .invalidInput) = true := rfl

/-- Proof of `test_psandbox_validateSpec_rejectsEmptyOrNulProgramAndArgs` for `defaultApi`. -/
theorem proof_psandbox_validateSpec_rejectsEmptyOrNulProgramAndArgs :
    AllPass (test_psandbox_validateSpec_rejectsEmptyOrNulProgramAndArgs defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_psandbox_validateSpec_rejectsEmptyOrNulProgramAndArgs,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert]
  intro specEmpty hEmpty
  have hValEmpty : validateSpecPure specEmpty =
      .error { kind := .invalidInput, message := "program must not be empty" } := by
    simp [validateSpecPure, isEmpty_true_of_eq_empty hEmpty]
  simp only [defaultApi, Internal.mkApiM, Internal.validateSpec, hValEmpty]
  refine ⟨⟨trivial, by simp⟩, ?_⟩
  intro specNulProg hNulProg
  cases hValProg : validateSpecPure specNulProg with
  | ok validProg =>
    exfalso
    have hOk := validateSpecPure_ok_props hValProg
    have hHas := hasNulChar_eq_true_of_mem hNulProg
    rw [hOk.2.1] at hHas
    cases hHas
  | error eProg =>
    refine ⟨validateSpecPure_error_props specNulProg eProg hValProg, ?_⟩
    intro specNulArg idx hIdx hNulArg
    cases hValArg : validateSpecPure specNulArg with
    | ok validArg =>
      exfalso
      have hOk := validateSpecPure_ok_props hValArg
      have hMem : specNulArg.args[idx]! ∈ specNulArg.args.toList := by
        simp only [hIdx, getElem!_pos]
        exact Array.getElem_mem_toList hIdx
      have hAny : specNulArg.args.toList.any (fun a => hasNulChar a.toList) = true :=
        List.any_eq_true.mpr ⟨specNulArg.args[idx]!, hMem, hasNulChar_eq_true_of_mem hNulArg⟩
      rw [hOk.2.2.1] at hAny
      cases hAny
    | error eArg =>
      exact ⟨validateSpecPure_error_props specNulArg eArg hValArg, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_psandbox_validateSpec_rejectsEmptyOrNulProgramAndArgs`. -/
theorem reach_psandbox_validateSpec_rejectsEmptyOrNulProgramAndArgs :
    CanReach (test_psandbox_validateSpec_rejectsEmptyOrNulProgramAndArgs defaultApi) := by
  dsimp only [CanReach, CanReachRun, test_psandbox_validateSpec_rejectsEmptyOrNulProgramAndArgs,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert]
  have h := proof_psandbox_validateSpec_rejectsEmptyOrNulProgramAndArgs { program := "" } rfl
  dsimp only [AllPass, AllPassRun, test_psandbox_validateSpec_rejectsEmptyOrNulProgramAndArgs,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert] at h
  have hProg := h.2 { program := "a\x00b" } (by decide)
  have hArg := hProg.2 { program := "/bin/echo", args := #["x\x00y"] } 0 (by decide) (by decide)
  exact ⟨{ program := "" }, rfl, h.1, { program := "a\x00b" }, by decide, hProg.1,
    { program := "/bin/echo", args := #["x\x00y"] }, 0, by decide, by decide, hArg⟩

/-- Proof of `test_psandbox_validateSpec_rejectsInvalidCwd` for `defaultApi`. -/
theorem proof_psandbox_validateSpec_rejectsInvalidCwd :
    AllPass (test_psandbox_validateSpec_rejectsInvalidCwd defaultApi) := by
  intro spec d hCwd hNorm
  simp only [defaultApi, Internal.mkApiM, Internal.validateSpec]
  cases hVal : validateSpecPure spec with
  | error e =>
    exact ⟨validateSpecPure_error_props spec e hVal, trivial⟩
  | ok valid =>
    exfalso
    have hOk := validateSpecPure_ok_props hVal
    have hSome := hOk.2.2.2.1 d hCwd
    rw [hNorm] at hSome
    cases hSome

/-- Non-vacuity `CanReach` witness for `test_psandbox_validateSpec_rejectsInvalidCwd`. -/
theorem reach_psandbox_validateSpec_rejectsInvalidCwd :
    CanReach (test_psandbox_validateSpec_rejectsInvalidCwd defaultApi) := by
  dsimp only [CanReach, CanReachRun, test_psandbox_validateSpec_rejectsInvalidCwd,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert]
  have h := proof_psandbox_validateSpec_rejectsInvalidCwd
    { program := "/bin/true", cwd := some "relative/dir" } "relative/dir" rfl (by decide)
  dsimp only [AllPass, AllPassRun, test_psandbox_validateSpec_rejectsInvalidCwd,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert] at h
  exact ⟨{ program := "/bin/true", cwd := some "relative/dir" }, "relative/dir", rfl, by decide, h⟩

/-- Proof of `test_psandbox_validateSpec_rejectsInvalidMountPaths` for `defaultApi`. -/
theorem proof_psandbox_validateSpec_rejectsInvalidMountPaths :
    AllPass (test_psandbox_validateSpec_rejectsInvalidMountPaths defaultApi) := by
  intro badPath hBad
  have hSegs : parseCleanAbsSegs badPath = none :=
    parseCleanAbsSegs_eq_none_of_normalize_eq_none hBad
  have hProg : ("/bin/true" : String).isEmpty = false := by decide
  have hWork : parseCleanAbsSegs "/work" = some ["work"] := rfl
  have hHostSrc : parseCleanAbsSegs "/host/src" = some ["host", "src"] := rfl
  simp [defaultApi, Internal.mkApiM, Internal.validateSpec, validateSpecPure,
    validateMountsList, validateAndNormalizeMount, hSegs, hProg, hasNulChar_binTrue,
    hWork, hHostSrc, bind, Except.bind, beq_invalidInput, assert]

/-- Non-vacuity `CanReach` witness for `test_psandbox_validateSpec_rejectsInvalidMountPaths`. -/
theorem reach_psandbox_validateSpec_rejectsInvalidMountPaths :
    CanReach (test_psandbox_validateSpec_rejectsInvalidMountPaths defaultApi) := by
  dsimp only [CanReach, CanReachRun, test_psandbox_validateSpec_rejectsInvalidMountPaths,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert]
  have h := proof_psandbox_validateSpec_rejectsInvalidMountPaths "../escape" (by decide)
  dsimp only [AllPass, AllPassRun, test_psandbox_validateSpec_rejectsInvalidMountPaths,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert] at h
  exact ⟨"../escape", by decide, h⟩

/-- Proof of `test_psandbox_validateSpec_rejectsDuplicateBoxPath` for `defaultApi`. -/
theorem proof_psandbox_validateSpec_rejectsDuplicateBoxPath :
    AllPass (test_psandbox_validateSpec_rejectsDuplicateBoxPath defaultApi) := by
  intro m₁ m₂ canonBp hm₁ hm₂
  simp only [defaultApi, Internal.mkApiM, Internal.validateSpec]
  cases hV₁ : validateAndNormalizeMount m₁ with
  | error e₁ => simp [hV₁, Except.map] at hm₁
  | ok nm₁ =>
    cases hV₂ : validateAndNormalizeMount m₂ with
    | error e₂ => simp [hV₂, Except.map] at hm₂
    | ok nm₂ =>
      simp only [hV₁, Except.map] at hm₁
      simp only [hV₂, Except.map] at hm₂
      injection hm₁ with hBp₁
      injection hm₂ with hBp₂
      have hMounts : validateMountsList [m₁, m₂] = .ok [nm₁, nm₂] := by
        simp [validateMountsList, hV₁, hV₂, bind, Except.bind]
      have hNotDist : allDistinct [mountBoxPath nm₁, mountBoxPath nm₂] = false := by
        simp [hBp₁, hBp₂, allDistinct]
      have hProg : ("/bin/true" : String).isEmpty = false := by decide
      simp [validateSpecPure, hProg, hasNulChar_binTrue, hMounts, hNotDist, bind, Except.bind, assert]

/-- Non-vacuity `CanReach` witness for `test_psandbox_validateSpec_rejectsDuplicateBoxPath`. -/
theorem reach_psandbox_validateSpec_rejectsDuplicateBoxPath :
    CanReach (test_psandbox_validateSpec_rejectsDuplicateBoxPath defaultApi) := by
  dsimp only [CanReach, CanReachRun, test_psandbox_validateSpec_rejectsDuplicateBoxPath,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert]
  have h := proof_psandbox_validateSpec_rejectsDuplicateBoxPath
    (.scratch "/work") (.scratch "/work/") "/work" rfl rfl
  dsimp only [AllPass, AllPassRun, test_psandbox_validateSpec_rejectsDuplicateBoxPath,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert] at h
  exact ⟨.scratch "/work", .scratch "/work/", "/work", rfl, rfl, h⟩

/-- Proof of `test_psandbox_validateSpec_rejectsProtectedSystemBoxPaths` for `defaultApi`. -/
theorem proof_psandbox_validateSpec_rejectsProtectedSystemBoxPaths :
    AllPass (test_psandbox_validateSpec_rejectsProtectedSystemBoxPaths defaultApi) := by
  intro bp bSegs hParse hRes
  have hProg : ("/bin/true" : String).isEmpty = false := by decide
  have hVar : parseCleanAbsSegs "/var/data" = some ["var", "data"] := rfl
  simp [defaultApi, Internal.mkApiM, Internal.validateSpec, validateSpecPure,
    validateMountsList, validateAndNormalizeMount, hParse, hRes, hProg, hasNulChar_binTrue, hVar,
    bind, Except.bind, beq_invalidInput, assert]

/-- Non-vacuity `CanReach` witness for `test_psandbox_validateSpec_rejectsProtectedSystemBoxPaths`. -/
theorem reach_psandbox_validateSpec_rejectsProtectedSystemBoxPaths :
    CanReach (test_psandbox_validateSpec_rejectsProtectedSystemBoxPaths defaultApi) := by
  dsimp only [CanReach, CanReachRun, test_psandbox_validateSpec_rejectsProtectedSystemBoxPaths,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert]
  have h := proof_psandbox_validateSpec_rejectsProtectedSystemBoxPaths "/usr/bin" ["usr", "bin"] rfl rfl
  dsimp only [AllPass, AllPassRun, test_psandbox_validateSpec_rejectsProtectedSystemBoxPaths,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert] at h
  exact ⟨"/usr/bin", ["usr", "bin"], rfl, rfl, h⟩

/-- Proof of `test_psandbox_validateSpec_rejectsZeroAndDuplicatePorts` for `defaultApi`. -/
theorem proof_psandbox_validateSpec_rejectsZeroAndDuplicatePorts :
    AllPass (test_psandbox_validateSpec_rejectsZeroAndDuplicatePorts defaultApi) := by
  intro p hp
  have hpNe : p ≠ 0 := bne_iff_ne.mp hp
  have hpZero : (p == 0) = false := beq_false_of_ne hpNe
  have hProg : ("/bin/true" : String).isEmpty = false := by decide
  simp only [defaultApi, Internal.mkApiM, Internal.validateSpec, assert]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [validateSpecPure, validateMountsList, hProg, hasNulChar_binTrue, allDistinct_nil_str,
      bind, Except.bind, beq_invalidInput]
  · simp [validateSpecPure, validateMountsList, hProg, hasNulChar_binTrue, allDistinct_nil_str,
      bind, Except.bind, beq_invalidInput]
  · simp [validateSpecPure, validateMountsList, allDistinct, hProg, hasNulChar_binTrue, hpZero,
      bind, Except.bind, beq_invalidInput]
  · intro p₂ ⟨hp₂Nz, hp₂Ne⟩
    have hp₂Zero : (p₂ == 0) = false := beq_false_of_ne (bne_iff_ne.mp hp₂Nz)
    refine ⟨?_, trivial⟩
    simp [validateSpecPure, validateMountsList, allDistinct, hProg, hasNulChar_binTrue,
      hpZero, hp₂Zero, Ne.symm hp₂Ne, bind, Except.bind, Except.isOk, Except.toBool]

/-- Non-vacuity `CanReach` witness for `test_psandbox_validateSpec_rejectsZeroAndDuplicatePorts`. -/
theorem reach_psandbox_validateSpec_rejectsZeroAndDuplicatePorts :
    CanReach (test_psandbox_validateSpec_rejectsZeroAndDuplicatePorts defaultApi) := by
  dsimp only [CanReach, CanReachRun, test_psandbox_validateSpec_rejectsZeroAndDuplicatePorts,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert]
  have h := proof_psandbox_validateSpec_rejectsZeroAndDuplicatePorts 8080 (by decide)
  dsimp only [AllPass, AllPassRun, test_psandbox_validateSpec_rejectsZeroAndDuplicatePorts,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert] at h
  exact ⟨8080, by decide, h.1, h.2.1, h.2.2.1, 8081, ⟨by decide, by decide⟩, h.2.2.2 8081 ⟨by decide, by decide⟩⟩

/-- Proof of `test_psandbox_validateSpec_limitsRules` for `defaultApi`. -/
theorem proof_psandbox_validateSpec_limitsRules :
    AllPass (test_psandbox_validateSpec_limitsRules defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_psandbox_validateSpec_limitsRules,
    Bind.bind, Pure.pure, NondetTest.assert]
  exact ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_psandbox_validateSpec_limitsRules`. -/
theorem reach_psandbox_validateSpec_limitsRules :
    CanReach (test_psandbox_validateSpec_limitsRules defaultApi) := by
  dsimp only [CanReach, CanReachRun, test_psandbox_validateSpec_limitsRules,
    Bind.bind, Pure.pure, NondetTest.assert]
  exact ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- Proof of `test_psandbox_validateSpec_rejectsInvalidEnv` for `defaultApi`. -/
theorem proof_psandbox_validateSpec_rejectsInvalidEnv :
    AllPass (test_psandbox_validateSpec_rejectsInvalidEnv defaultApi) := by
  intro spec idx hIdx hBad
  have hMem : spec.env[idx]! ∈ spec.env.toList := by
    simp only [hIdx, getElem!_pos]
    exact Array.getElem_mem_toList hIdx
  have hAllFalse : spec.env.toList.all isValidEnvPair = false := by
    cases hAll : spec.env.toList.all isValidEnvPair with
    | false => rfl
    | true =>
      have hPair := (List.all_eq_true.mp hAll) spec.env[idx]! hMem
      rw [hPair] at hBad
      cases hBad
  simp only [defaultApi, Internal.mkApiM, Internal.validateSpec]
  cases hVal : validateSpecPure spec with
  | error e =>
    exact ⟨validateSpecPure_error_props spec e hVal, trivial⟩
  | ok valid =>
    exfalso
    have hOk := validateSpecPure_ok_props hVal
    rw [hOk.2.2.2.2] at hAllFalse
    cases hAllFalse

/-- Non-vacuity `CanReach` witness for `test_psandbox_validateSpec_rejectsInvalidEnv`. -/
theorem reach_psandbox_validateSpec_rejectsInvalidEnv :
    CanReach (test_psandbox_validateSpec_rejectsInvalidEnv defaultApi) := by
  dsimp only [CanReach, CanReachRun, test_psandbox_validateSpec_rejectsInvalidEnv,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert]
  let spec : BoxSpec := { program := "/bin/true", env := #[("BAD=KEY", "1")] }
  have h := proof_psandbox_validateSpec_rejectsInvalidEnv spec 0 (by decide) (by decide)
  dsimp only [AllPass, AllPassRun, test_psandbox_validateSpec_rejectsInvalidEnv,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert] at h
  exact ⟨spec, 0, by decide, by decide, h⟩

/-- Proof of `test_psandbox_validateSpec_defaultsOverridesAndIdempotence` for `defaultApi`. -/
theorem proof_psandbox_validateSpec_defaultsOverridesAndIdempotence :
    AllPass (test_psandbox_validateSpec_defaultsOverridesAndIdempotence defaultApi) := by
  intro k v₁ v₂ ⟨hKv₁, hKv₂⟩ hkNePath
  have hkPath : (k == "PATH") = false := beq_false_of_ne hkNePath
  have hProg1 : ("python3" : String).isEmpty = false := by decide
  have hProg1Nul : hasNulChar ("python3" : String).toList = false := by decide
  have hArgs1Nul : (["-c", "pass"] : List String).any (fun a => hasNulChar a.toList) = false := by decide
  have hMnt1 : validateMountsList [.readOnly "/work/src" "/workspace/"] =
      .ok [.readOnly "/work/src" "/workspace"] := rfl
  have hDist1 : allDistinct (([.readOnly "/work/src" "/workspace"] : List SandboxMount).map mountBoxPath) = true := rfl
  have hTmp1 : ([.readOnly "/work/src" "/workspace"] : List SandboxMount).any (fun m => mountBoxPath m == "/tmp") = false := rfl
  have hPathValid : isValidEnvPair ("PATH", "/usr/bin:/bin") = true := by decide
  have hMnt1Id : validateMountsList [.scratch "/tmp", .readOnly "/work/src" "/workspace"] =
      .ok [.scratch "/tmp", .readOnly "/work/src" "/workspace"] := rfl
  have hDist1Id : allDistinct (([.scratch "/tmp", .readOnly "/work/src" "/workspace"] : List SandboxMount).map mountBoxPath) = true := rfl
  have hTmp1Id : ([.scratch "/tmp", .readOnly "/work/src" "/workspace"] : List SandboxMount).any (fun m => mountBoxPath m == "/tmp") = true := rfl
  have hCwdTmp : normalizeCleanAbsPath "/tmp" = some "/tmp" := rfl
  have hPort0 : ([] : List PortForward).any (fun pf => pf.boxPort == 0 || pf.hostPort == 0) = false := rfl
  have hPortD : allDistinct (([] : List PortForward).map (·.boxPort)) = true := rfl
  have hTo : ((60000 : Nat) == 0) = false := rfl
  have hMem : ((some (8 * 1024 ^ 3) : Option Nat) == some 0) = false := rfl
  have hPids : ((some 512 : Option Nat) == some 0) = false := rfl
  have hSpecDef :
      validateSpecPure
        { program := "python3"
          args := #["-c", "pass"]
          cwd := none
          mounts := #[.readOnly "/work/src" "/workspace/"]
          env := #[(k, v₁), (k, v₂)] } =
      .ok
        { program := "python3"
          args := #["-c", "pass"]
          cwd := "/tmp"
          stdin := ByteArray.empty
          mounts := #[.scratch "/tmp", .readOnly "/work/src" "/workspace"]
          allowBoxLocalhost := false
          portForwards := #[]
          env := #[("PATH", "/usr/bin:/bin"), (k, v₂)]
          limits := {} } := by
    simp only [validateSpecPure, hProg1, hProg1Nul, hArgs1Nul, hMnt1, hDist1, hTmp1,
      hPort0, hPortD, hTo, hMem, hPids,
      defaultSandboxCwd, defaultSandboxPath, dedupEnvPairs,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil,
      hKv₁, hKv₂, hkPath, beq_self_eq_true,
      Bool.false_eq_true, Bool.not_true, Bool.and_true, Bool.or_false,
      ↓reduceIte, bind, Except.bind]
  have hSpecDefId :
      validateSpecPure
        (validBoxSpecToBoxSpec
          { program := "python3"
            args := #["-c", "pass"]
            cwd := "/tmp"
            stdin := ByteArray.empty
            mounts := #[.scratch "/tmp", .readOnly "/work/src" "/workspace"]
            allowBoxLocalhost := false
            portForwards := #[]
            env := #[("PATH", "/usr/bin:/bin"), (k, v₂)]
            limits := {} }) =
      .ok
        { program := "python3"
          args := #["-c", "pass"]
          cwd := "/tmp"
          stdin := ByteArray.empty
          mounts := #[.scratch "/tmp", .readOnly "/work/src" "/workspace"]
          allowBoxLocalhost := false
          portForwards := #[]
          env := #[("PATH", "/usr/bin:/bin"), (k, v₂)]
          limits := {} } := by
    simp only [validBoxSpecToBoxSpec, validateSpecPure, hProg1, hProg1Nul, hArgs1Nul, hCwdTmp,
      hMnt1Id, hDist1Id, hTmp1Id, hPort0, hPortD, hTo, hMem, hPids,
      dedupEnvPairs, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
      hPathValid, hKv₂, hkPath, beq_self_eq_true,
      Bool.false_eq_true, Bool.not_true, Bool.and_true, Bool.or_false,
      ↓reduceIte, bind, Except.bind]
  simp only [defaultApi, Internal.mkApiM, Internal.validateSpec, hSpecDef, assert]
  refine ⟨trivial, trivial, trivial, hSpecDefId, ?_⟩
  intro customPath hCustom
  have hNoNul : hasNulChar customPath.toList = false :=
    Bool.eq_false_iff.mpr (fun ht => by simp [ht] at hCustom)
  have hProg2 : ("/usr/bin/env" : String).isEmpty = false := by decide
  have hProg2Nul : hasNulChar ("/usr/bin/env" : String).toList = false := by decide
  have hCwd2 : normalizeCleanAbsPath "/workspace/sub/" = some "/workspace/sub" := rfl
  have hCwd2Id : normalizeCleanAbsPath "/workspace/sub" = some "/workspace/sub" := rfl
  have hMnt2 : validateMountsList [.readWrite "/host/tmp" "/tmp/"] =
      .ok [.readWrite "/host/tmp" "/tmp"] := rfl
  have hMnt2Id : validateMountsList [.readWrite "/host/tmp" "/tmp"] =
      .ok [.readWrite "/host/tmp" "/tmp"] := rfl
  have hDist2 : allDistinct (([.readWrite "/host/tmp" "/tmp"] : List SandboxMount).map mountBoxPath) = true := rfl
  have hTmp2 : ([.readWrite "/host/tmp" "/tmp"] : List SandboxMount).any (fun m => mountBoxPath m == "/tmp") = true := rfl
  have hPathKey : isValidEnvPair ("PATH", customPath) = true := by
    simp [isValidEnvPair, hNoNul]
    decide
  have hSpecCust :
      validateSpecPure
        { program := "/usr/bin/env"
          cwd := some "/workspace/sub/"
          mounts := #[.readWrite "/host/tmp" "/tmp/"]
          env := #[("PATH", customPath)] } =
      .ok
        { program := "/usr/bin/env"
          args := #[]
          cwd := "/workspace/sub"
          stdin := ByteArray.empty
          mounts := #[.readWrite "/host/tmp" "/tmp"]
          allowBoxLocalhost := false
          portForwards := #[]
          env := #[("PATH", customPath)]
          limits := {} } := by
    simp only [validateSpecPure, hProg2, hProg2Nul, hCwd2, hMnt2, hDist2, hTmp2,
      hPort0, hPortD, hTo, hMem, hPids,
      dedupEnvPairs, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
      hPathKey, beq_self_eq_true,
      Bool.false_eq_true, Bool.not_true, Bool.and_true, Bool.or_false,
      ↓reduceIte, bind, Except.bind]
  have hSpecCustId :
      validateSpecPure
        (validBoxSpecToBoxSpec
          { program := "/usr/bin/env"
            args := #[]
            cwd := "/workspace/sub"
            stdin := ByteArray.empty
            mounts := #[.readWrite "/host/tmp" "/tmp"]
            allowBoxLocalhost := false
            portForwards := #[]
            env := #[("PATH", customPath)]
            limits := {} }) =
      .ok
        { program := "/usr/bin/env"
          args := #[]
          cwd := "/workspace/sub"
          stdin := ByteArray.empty
          mounts := #[.readWrite "/host/tmp" "/tmp"]
          allowBoxLocalhost := false
          portForwards := #[]
          env := #[("PATH", customPath)]
          limits := {} } := by
    simp only [validBoxSpecToBoxSpec, validateSpecPure, hProg2, hProg2Nul, hCwd2Id,
      hMnt2Id, hDist2, hTmp2, hPort0, hPortD, hTo, hMem, hPids,
      dedupEnvPairs, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
      hPathKey, beq_self_eq_true,
      Bool.false_eq_true, Bool.not_true, Bool.and_true, Bool.or_false,
      ↓reduceIte, bind, Except.bind]
  simp only [hSpecCust]
  exact ⟨trivial, trivial, trivial, hSpecCustId, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_psandbox_validateSpec_defaultsOverridesAndIdempotence`. -/
theorem reach_psandbox_validateSpec_defaultsOverridesAndIdempotence :
    CanReach (test_psandbox_validateSpec_defaultsOverridesAndIdempotence defaultApi) := by
  dsimp only [CanReach, CanReachRun,
    test_psandbox_validateSpec_defaultsOverridesAndIdempotence,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert]
  have h := proof_psandbox_validateSpec_defaultsOverridesAndIdempotence
    "FOO" "1" "2" ⟨by decide, by decide⟩ (by decide)
  dsimp only [AllPass, AllPassRun,
    test_psandbox_validateSpec_defaultsOverridesAndIdempotence,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assume, NondetTest.assert] at h
  exact ⟨"FOO", "1", "2", ⟨by decide, by decide⟩, by decide,
    h.1, h.2.1, h.2.2.1, h.2.2.2.1, "/custom/bin", by decide, h.2.2.2.2 "/custom/bin" (by decide)⟩

end LeanSwe.ProcessSandbox.Proofs
