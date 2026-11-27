import LeanSwe.ProcessSandbox.Types
import LeanSweProofs.ProcessSandbox.Model

namespace ModelMutants.ProcessSandbox

open LeanSwe.ProcessSandbox
open LeanSwe.ProcessSandbox.Model

/-- Execute `s.guest` on projected `GuestInput` and commit only permitted write-backs. -/
def runValidGuest (s : HostWorld) (valid : ValidBoxSpec) :
    Except SandboxError SandboxResult × HostWorld :=
  let (rawOutcome, rawStdout, rawStderr, rawFsAfter, rawNonFsAfter) :=
    s.guest (projectGuestInput s valid)
  let sNext := commitGuestState s valid rawFsAfter rawNonFsAfter
  match valid.maxOutputBytes with
  | some cap =>
    if rawStdout.size + rawStderr.size ≤ cap then
      (.ok { outcome := rawOutcome, stdout := rawStdout, stderr := rawStderr }, sNext)
    else
      (.ok { outcome := .outputLimitExceeded, stdout := ByteArray.empty, stderr := ByteArray.empty }, sNext)
  | none =>
    (.ok { outcome := rawOutcome, stdout := rawStdout, stderr := rawStderr }, sNext)

/-- Clean reference implementation matching `LeanSwe.ProcessSandbox.Model` directly. -/
def referenceSandboxRunner : SandboxRunner where
  validateSpec := validateSpecPure
  run s spec :=
    match validateSpecPure spec with
    | .error e => (.error e, s)
    | .ok valid =>
      if !s.available then
        (.error { kind := .unavailable, message := "sandbox unavailable on host" }, s)
      else
        match s.hostError valid with
        | some k =>
          if isHostErrorKind k then
            (.error { kind := k, message := "host pre-execution failure" }, s)
          else runValidGuest s valid
        | none => runValidGuest s valid
  isAvailable s := s.available

private theorem invalidInput_kind_msg (msg : String) (p : Option String)
    (hNonEmpty : !msg.isEmpty = true) :
    (invalidInput msg p).kind = .invalidInput ∧ !(invalidInput msg p).message.isEmpty = true :=
  ⟨rfl, hNonEmpty⟩

private theorem validateAndNormalizeMount_err_kind_msg (m : SandboxMount) (e : SandboxError)
    (h : validateAndNormalizeMount m = .error e) :
    e.kind = .invalidInput ∧ !e.message.isEmpty = true := by
  cases m with
  | readOnly hp bp | readWrite hp bp =>
    simp only [validateAndNormalizeMount, validateHostBoxPair] at h
    cases h1 : parseCleanAbsSegs hp <;> cases h2 : parseCleanAbsSegs bp <;> simp [h1, h2] at h
    · subst h; exact invalidInput_kind_msg _ _ (by decide)
    · subst h; exact invalidInput_kind_msg _ _ (by decide)
    · subst h; exact invalidInput_kind_msg _ _ (by decide)
    · split at h <;> simp at h
      subst h; exact invalidInput_kind_msg _ _ (by decide)
  | scratch bp =>
    simp only [validateAndNormalizeMount] at h
    cases h1 : parseCleanAbsSegs bp <;> simp [h1] at h
    · subst h; exact invalidInput_kind_msg _ _ (by decide)
    · split at h <;> simp at h
      subst h; exact invalidInput_kind_msg _ _ (by decide)

private theorem validateMountsList_err_kind_msg :
    ∀ (ms : List SandboxMount) (e : SandboxError),
      validateMountsList ms = .error e →
      e.kind = .invalidInput ∧ !e.message.isEmpty = true
  | [], e, h => by simp [validateMountsList] at h
  | m :: rest, e, h => by
    unfold validateMountsList at h
    cases hm : validateAndNormalizeMount m with
    | error em =>
      simp [hm, Bind.bind, Except.bind] at h
      subst h
      exact validateAndNormalizeMount_err_kind_msg m em hm
    | ok _ =>
      cases hr : validateMountsList rest with
      | error er =>
        simp [hm, hr, Bind.bind, Except.bind] at h
        subst h
        exact validateMountsList_err_kind_msg rest er hr
      | ok _ =>
        simp [hm, hr, Bind.bind, Except.bind] at h

private theorem validateSpecPure_err_kind_msg (spec : BoxSpec) (e : SandboxError)
    (h : validateSpecPure spec = .error e) :
    e.kind = .invalidInput ∧ !e.message.isEmpty = true := by
  unfold validateSpecPure at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · injection h with h; subst h; exact invalidInput_kind_msg _ _ (by decide)
  split at h
  · injection h with h; subst h; exact invalidInput_kind_msg _ _ (by decide)
  split at h
  · injection h with h; subst h; exact invalidInput_kind_msg _ _ (by decide)
  split at h
  · injection h with h; subst h; exact invalidInput_kind_msg _ _ (by decide)
  split at h
  · injection h with h; subst h; exact invalidInput_kind_msg _ _ (by decide)
  split at h
  · injection h with h; subst h; exact invalidInput_kind_msg _ _ (by decide)
  cases hCwd : spec.cwd with
  | none =>
    simp only [hCwd] at h
    cases hm : validateMountsList spec.mounts.toList with
    | error em =>
      simp only [hm] at h; injection h with h; subst h
      exact validateMountsList_err_kind_msg _ em hm
    | ok normMounts =>
      simp only [hm] at h
      split at h
      · injection h with h; subst h; exact invalidInput_kind_msg _ _ (by decide)
      split at h
      · injection h with h; subst h; exact invalidInput_kind_msg _ _ (by decide)
      · contradiction
  | some d =>
    simp only [hCwd] at h
    cases hNorm : normalizeCleanAbsPath d with
    | none =>
      simp only [hNorm] at h; injection h with h; subst h
      exact invalidInput_kind_msg _ _ (by decide)
    | some cleanD =>
      simp only [hNorm] at h
      cases hm : validateMountsList spec.mounts.toList with
      | error em =>
        simp only [hm] at h; injection h with h; subst h
        exact validateMountsList_err_kind_msg _ em hm
      | ok normMounts =>
        simp only [hm] at h
        split at h
        · injection h with h; subst h; exact invalidInput_kind_msg _ _ (by decide)
        split at h
        · injection h with h; subst h; exact invalidInput_kind_msg _ _ (by decide)
        · contradiction

private theorem runValidGuest_satisfies (s : HostWorld) (valid : ValidBoxSpec) :
    let r := runValidGuest s valid
    allowedGuestRun s valid r.1 r.2 := by
  dsimp only [runValidGuest, allowedGuestRun]
  cases hCap : valid.maxOutputBytes with
  | none =>
    exact Or.inl ⟨by simp [withinOutputCap], rfl, rfl⟩
  | some cap =>
    by_cases hLe :
      (s.guest (projectGuestInput s valid)).2.1.size +
      (s.guest (projectGuestInput s valid)).2.2.1.size ≤ cap
    · simp only [hLe, ↓reduceIte]
      exact Or.inl ⟨by simpa [withinOutputCap] using hLe, trivial, trivial⟩
    · simp only [hLe, ↓reduceIte]
      refine Or.inr (Or.inl ⟨cap,
        { outcome := .outputLimitExceeded, stdout := ByteArray.empty, stderr := ByteArray.empty },
        (s.guest (projectGuestInput s valid)).2.2.2.1,
        (s.guest (projectGuestInput s valid)).2.2.2.2,
        rfl, Nat.lt_of_not_le hLe, rfl, rfl, Nat.zero_le cap, rfl⟩)

/-- Satisfiability witness: `referenceSandboxRunner` satisfies `obeys_sandbox_model` unconditionally. -/
theorem referenceSandboxRunner_obeys_model : obeys_sandbox_model referenceSandboxRunner := by
  refine ⟨?_, ?_, ?_⟩
  · intro s spec
    dsimp only [allowedSandboxStep, referenceSandboxRunner]
    refine ⟨rfl, ?_⟩
    cases hv : validateSpecPure spec with
    | ok _ => rfl
    | error e => exact ⟨rfl, (validateSpecPure_err_kind_msg spec e hv).2⟩
  · intro s spec
    dsimp only [allowedSandboxStep, allowedRun, referenceSandboxRunner]
    cases hv : validateSpecPure spec with
    | error e =>
      have hErr := validateSpecPure_err_kind_msg spec e hv
      exact ⟨e, rfl, hErr.1, hErr.2, rfl⟩
    | ok valid =>
      cases hAvail : s.available with
      | false =>
        exact ⟨{ kind := .unavailable, message := "sandbox unavailable on host" }, rfl, rfl, by decide, rfl⟩
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases hErr : s.hostError valid with
        | none => exact runValidGuest_satisfies s valid
        | some k =>
          cases hk : isHostErrorKind k with
          | true =>
            simp only [hk, ↓reduceIte]
            refine ⟨{ kind := k, message := "host pre-execution failure" }, rfl, rfl, ?_, trivial⟩
            change !("host pre-execution failure".isEmpty) = true
            decide
          | false =>
            simp only [hk, Bool.false_eq_true, ↓reduceIte]
            exact runValidGuest_satisfies s valid
  · intro s
    exact ⟨rfl, rfl⟩

/-- Trivial Mutant 1: validates input and returns `.exited 0` without running `HostWorld.guest`. -/
def noRunDummy : SandboxRunner where
  validateSpec := validateSpecPure
  run s spec :=
    match validateSpecPure spec with
    | .error e => (.error e, s)
    | .ok _ =>
      if !s.available then
        (.error { kind := .unavailable, message := "sandbox unavailable on host" }, s)
      else
        (.ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty }, s)
  isAvailable s := s.available

/-- Trivial Mutant 2: runs `HostWorld.guest` directly against host `fs` and `nonFs` with no isolation. -/
def unsandboxedHostRunner : SandboxRunner where
  validateSpec := validateSpecPure
  run s spec :=
    match validateSpecPure spec with
    | .error e => (.error e, s)
    | .ok valid =>
      if !s.available then
        (.error { kind := .unavailable, message := "sandbox unavailable on host" }, s)
      else
        let rawInp : GuestInput :=
          { program := valid.program
            args := valid.args
            cwd := valid.cwd
            stdin := valid.stdin
            fs := s.fs
            nonFs := s.nonFs }
        let (outcome, stdout, stderr, nextFs, nextNonFs) := s.guest rawInp
        (.ok { outcome, stdout, stderr }, { s with fs := nextFs, nonFs := nextNonFs })
  isAvailable s := s.available

private def cleanHostWorld (guest : GuestProgram) : HostWorld where
  fs := fun _ => none
  presetFs := fun _ => none
  nonFs := { env := [("HOST_SECRET", "keep")], processes := ["init"], network := [], orphanCount := 0 }
  available := true
  allowTimeout := false
  hostError := fun _ => none
  guest := guest

private instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => if h : a = b then isTrue (congrArg Except.ok h) else isFalse (by intro hEq; injection hEq; exact h ‹_›)
  | .error a, .error b => if h : a = b then isTrue (congrArg Except.error h) else isFalse (by intro hEq; injection hEq; exact h ‹_›)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

/-- Mutant 1 (`noRunDummy`) fails `obeys_sandbox_model`, witnessed by a guest exiting with `1`. -/
theorem noRunDummy_fails_model : ¬ obeys_sandbox_model noRunDummy := by
  intro hObeys
  let spec : BoxSpec := { program := "/bin/false" }
  let f : GuestProgram := fun inp =>
    (.exited 1, ByteArray.empty, ByteArray.empty, inp.fs, inp.nonFs)
  have hStep := hObeys.2.1 (cleanHostWorld f) spec
  have hVal : validateSpecPure spec = .ok
      { program := "/bin/false"
        args := #[]
        env := #[("PATH", "/usr/bin:/bin")]
        cwd := "/tmp"
        stdin := ByteArray.empty
        mounts := #[.scratch "/tmp"]
        network := .closed
        timeoutMs := none
        maxOutputBytes := none } := by
    decide
  simp [allowedSandboxStep, allowedRun, allowedGuestRun, noRunDummy, cleanHostWorld, hVal, f] at hStep

/-- Mutant 2 (`unsandboxedHostRunner`) fails `obeys_sandbox_model`, witnessed by a guest overwriting a read-only host path and host env/network. -/
theorem unsandboxedHostRunner_fails_model : ¬ obeys_sandbox_model unsandboxedHostRunner := by
  intro hObeys
  let spec : BoxSpec :=
    { program := "/bin/sh"
      mounts := #[.readOnly "/host/secret" "/ro"]
      network := .closed }
  let payload : ByteArray := ByteArray.mk #[1]
  let f : GuestProgram := fun inp =>
    ( .exited 0
    , ByteArray.empty
    , ByteArray.empty
    , (fun p => if p == "/host/secret" then some payload else inp.fs p)
    , { inp.nonFs with env := [], network := ["exfiltrated"] } )
  have hStep := hObeys.2.1 (cleanHostWorld f) spec
  have hVal : validateSpecPure spec = .ok
      { program := "/bin/sh"
        args := #[]
        env := #[("PATH", "/usr/bin:/bin")]
        cwd := "/tmp"
        stdin := ByteArray.empty
        mounts := #[.scratch "/tmp", .readOnly "/host/secret" "/ro"]
        network := .closed
        timeoutMs := none
        maxOutputBytes := none } := by
    decide
  simp only [allowedSandboxStep, allowedRun, allowedGuestRun, unsandboxedHostRunner, cleanHostWorld,
    hVal, f, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome_none, reduceCtorEq,
    false_and, exists_false, or_false, withinOutputCap, true_and] at hStep
  have hFsEq := congrArg (fun (w : HostWorld) => w.fs "/host/secret") hStep
  dsimp only [commitGuestState] at hFsEq
  have hNotRw : isCoveredByReadWrite [SandboxMount.scratch "/tmp", SandboxMount.readOnly "/host/secret" "/ro"] "/host/secret" = false := by
    decide
  rw [applyWriteBack_eq_of_not_readWrite _ _ _ "/host/secret" hNotRw] at hFsEq
  simp [payload] at hFsEq

end ModelMutants.ProcessSandbox
