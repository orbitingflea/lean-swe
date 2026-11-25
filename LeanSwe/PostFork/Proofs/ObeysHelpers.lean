import Core.Obeys
import LeanSwe.PostFork.Impl
import LeanSwe.PostFork.Model.Refines

/-!
Step-preservation and error-well-formedness helper lemmas for `LeanSwe.PostFork` host
orchestrator combinators (`loopPow2`, `writeAllRetryEintr`, `readAllRetryEintr`,
`waitRetryEintr`, descriptor probing/closing, `awaitExecOrFailure`, and `performFork`).
-/

namespace LeanSwe.PostFork.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork
open LeanSwe.PostFork.Model
open LeanSwe.PostFork.Impl.Internal

/-- Relational invariant across host sub-steps: preserves `rawStepWf` and monotonic `nextHandle`. -/
def HostInv {W : Type} (proj : W → HostStepState) (w₀ w₁ : W) : Prop :=
  rawStepWf (proj w₁) = true ∧ (proj w₀).nextHandle ≤ (proj w₁).nextHandle

/-- Reflexivity of `HostInv` at any well-formed state. -/
theorem hostInv_refl {W : Type} {proj : W → HostStepState} {w : W}
    (hwf : rawStepWf (proj w) = true) : HostInv proj w w :=
  ⟨hwf, Nat.le_refl _⟩

/-- Transitivity of `HostInv` across sequential host steps. -/
theorem hostInv_trans {W : Type} {proj : W → HostStepState} {w₀ w₁ w₂ : W}
    (h₁ : HostInv proj w₀ w₁) (h₂ : HostInv proj w₁ w₂) : HostInv proj w₀ w₂ :=
  ⟨h₂.1, Nat.le_trans h₁.2 h₂.2⟩

/-- Any `mkSysErr` built from a valid Linux `Errno` and non-empty message satisfies `validSysErrProp`. -/
theorem mkSysErr_valid (code : UInt32) (msg : String)
    (hCode : validHostErrnoProp code) (hMsg : !msg.isEmpty = true) :
    validSysErrProp (mkSysErr code msg) :=
  ⟨rfl, rfl, hMsg, code, rfl, hCode⟩

/-- Structural induction rule for `loopPow2`: preserves `HostInv` and `post` on `.inr` termination. -/
theorem loopPow2_preserves {W σ α : Type} (proj : W → HostStepState)
    (step : σ → StateM W (Sum σ α)) (post : α → Prop)
    (hStep : ∀ (s : σ) (w : W), rawStepWf (proj w) = true →
      let r := (step s).run w; HostInv proj w r.2 ∧ (∀ a, r.1 = .inr a → post a))
    (d : Nat) :
    ∀ (s : σ) (w : W), rawStepWf (proj w) = true →
      let r := (loopPow2 step d s).run w; HostInv proj w r.2 ∧ (∀ a, r.1 = .inr a → post a) := by
  induction d with
  | zero => intro s w hwf; exact hStep s w hwf
  | succ d ih =>
    intro s w hwf
    have h₁ := ih s w hwf
    try dsimp only [loopPow2, Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at h₁ ⊢
    cases hCall : loopPow2 step d s w with
    | mk res₁ w₁ =>
      rw [hCall] at h₁
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at h₁ ⊢
      cases res₁ with
      | inr done =>
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        exact ⟨h₁.1, fun a ha => h₁.2 a ha⟩
      | inl next =>
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        have h₂ := ih next w₁ h₁.1.1
        try dsimp only [StateT.run] at h₂
        cases hCall₂ : loopPow2 step d next w₁ with
        | mk res₂ w₂ =>
          rw [hCall₂] at h₂
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at h₂ ⊢
          exact ⟨hostInv_trans h₁.1 h₂.1, h₂.2⟩

private def writeRetryStep {W : Type} (raw : RawHostOpsM (StateM W))
    (h : Nat) (data : ByteArray) (curOff : Nat) :
    StateM W (Sum Nat (Except PostForkError Unit)) :=
  if curOff ≥ data.size then pure (.inr (.ok ()))
  else do
    let rem := data.size - curOff
    match ← raw.writeOnce h data (UInt64.ofNat curOff) (UInt64.ofNat rem) with
    | .ok n =>
      if n == 0 then pure (.inr (.error (mkSysErr 5 "host write returned zero bytes")))
      else pure (.inl (curOff + n.toNat))
    | .error e =>
      if e == 4 then pure (.inl curOff)
      else pure (.inr (.error (mkSysErr e "host write failed")))

/-- Soundness of `writeAllRetryEintr`: preserves `HostInv` and yields `validSysErrProp` on errors. -/
theorem writeAllRetryEintr_sound {W : Type} {proj : W → HostStepState} {raw : RawHostOpsM (StateM W)}
    (hRaw : Core.ObeysStep proj rawStepWf (execRawStep raw) allowedRawStep)
    (h : Nat) (data : ByteArray) (off depth : Nat) (w : W) (hwf : rawStepWf (proj w) = true) :
    let r := (writeAllRetryEintr raw h data off depth).run w
    HostInv proj w r.2 ∧ (∀ err, r.1 = .error err → validSysErrProp err) := by
  have hStep : ∀ (curOff : Nat) (w₀ : W), rawStepWf (proj w₀) = true →
      let r := (writeRetryStep raw h data curOff).run w₀
      HostInv proj w₀ r.2 ∧ (∀ (out : Except PostForkError Unit), r.1 = .inr out →
        ∀ err, out = .error err → validSysErrProp err) := by
    intro curOff w₀ hwf₀
    unfold writeRetryStep
    by_cases hGe : curOff ≥ data.size
    · simp only [hGe, ↓reduceIte]
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
      exact ⟨hostInv_refl hwf₀, (fun _ hInr _ hErr => by cases hInr; cases hErr)⟩
    · simp only [hGe, ↓reduceIte]
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
      have hCallStep := hRaw w₀
        (.writeOnce h data (UInt64.ofNat curOff) (UInt64.ofNat (data.size - curOff))) hwf₀
      try dsimp only [allowedRawStep, execRawStep, Functor.map, StateT.map,
        Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCallStep
      cases hCall : raw.writeOnce h data (UInt64.ofNat curOff) (UInt64.ofNat (data.size - curOff)) w₀ with
      | mk res w₁ =>
        rw [hCall] at hCallStep
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCallStep ⊢
        rcases hCallStep with ⟨_, hwf₁, hLe₁, hPay⟩
        cases res with
        | ok n =>
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          by_cases hn0 : (n == 0) = true
          · simp only [hn0, ↓reduceIte]
            try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
            exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hInr _ hErr => by
              cases hInr; cases hErr; exact mkSysErr_valid 5 _ ⟨by decide, by decide⟩ rfl)⟩
          · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
            try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
            exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hInr => nomatch hInr)⟩
        | error e =>
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPay ⊢
          by_cases he4 : (e == 4) = true
          · simp only [he4, ↓reduceIte]
            try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
            exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hInr => nomatch hInr)⟩
          · simp only [he4, Bool.false_eq_true, ↓reduceIte]
            try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
            exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hInr _ hErr => by
              cases hInr; cases hErr; exact mkSysErr_valid e _ hPay rfl)⟩
  have hRunEq : writeAllRetryEintr raw h data off depth = (do
      let res ← loopPow2 (writeRetryStep raw h data) depth off
      match res with
      | .inr out => pure out
      | .inl finalOff =>
        if finalOff ≥ data.size then pure (.ok ())
        else pure (.error (mkSysErr 5 "host write exceeded retry fuel"))) := rfl
  rw [hRunEq]
  have hLoop := loopPow2_preserves proj (writeRetryStep raw h data)
    (fun out => ∀ err, out = .error err → validSysErrProp err) hStep depth off w hwf
  try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hLoop ⊢
  cases hL : loopPow2 (writeRetryStep raw h data) depth off w with
  | mk lres w₁ =>
    rw [hL] at hLoop
    try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hLoop ⊢
    cases lres with
    | inr out =>
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
      exact ⟨hLoop.1, hLoop.2 out rfl⟩
    | inl finalOff =>
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
      by_cases hf : finalOff ≥ data.size
      · simp only [hf, ↓reduceIte]
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        exact ⟨hLoop.1, (fun _ hErr => nomatch hErr)⟩
      · simp only [hf, ↓reduceIte]
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        exact ⟨hLoop.1, (fun _ hErr => by
          cases hErr; exact mkSysErr_valid 5 _ ⟨by decide, by decide⟩ rfl)⟩

private def readRetryStep {W : Type} (raw : RawHostOpsM (StateM W))
    (h : Nat) (chunkCap : UInt64) (curChunks : Array ByteArray) :
    StateM W (Sum (Array ByteArray) (Except PostForkError ByteArray)) := do
  match ← raw.readOnce h chunkCap with
  | .ok chunk =>
    if chunk.size == 0 then pure (.inr (.ok (concatByteChunks curChunks)))
    else pure (.inl (curChunks.push chunk))
  | .error e =>
    if e == 4 then pure (.inl curChunks)
    else pure (.inr (.error (mkSysErr e "host read failed")))

/-- Soundness of `readAllRetryEintr`: preserves `HostInv` and yields `validSysErrProp` on errors. -/
theorem readAllRetryEintr_sound {W : Type} {proj : W → HostStepState} {raw : RawHostOpsM (StateM W)}
    (hRaw : Core.ObeysStep proj rawStepWf (execRawStep raw) allowedRawStep)
    (h : Nat) (chunkCap : UInt64) (acc : ByteArray) (depth : Nat) (w : W) (hwf : rawStepWf (proj w) = true) :
    let r := (readAllRetryEintr raw h chunkCap acc depth).run w
    HostInv proj w r.2 ∧ (∀ err, r.1 = .error err → validSysErrProp err) := by
  have hStep : ∀ (curChunks : Array ByteArray) (w₀ : W), rawStepWf (proj w₀) = true →
      let r := (readRetryStep raw h chunkCap curChunks).run w₀
      HostInv proj w₀ r.2 ∧ (∀ (out : Except PostForkError ByteArray), r.1 = .inr out →
        ∀ err, out = .error err → validSysErrProp err) := by
    intro curChunks w₀ hwf₀
    try dsimp only [readRetryStep, Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
    have hCallStep := hRaw w₀ (.readOnce h chunkCap) hwf₀
    try dsimp only [allowedRawStep, execRawStep, Functor.map, StateT.map,
      Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCallStep
    cases hCall : raw.readOnce h chunkCap w₀ with
    | mk res w₁ =>
      rw [hCall] at hCallStep
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCallStep ⊢
      rcases hCallStep with ⟨_, hwf₁, hLe₁, hPay⟩
      cases res with
      | ok chunk =>
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        by_cases hc0 : (chunk.size == 0) = true
        · simp only [hc0, ↓reduceIte]
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hInr _ hErr => by cases hInr; cases hErr)⟩
        · simp only [hc0, Bool.false_eq_true, ↓reduceIte]
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hInr => nomatch hInr)⟩
      | error e =>
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPay ⊢
        by_cases he4 : (e == 4) = true
        · simp only [he4, ↓reduceIte]
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hInr => nomatch hInr)⟩
        · simp only [he4, Bool.false_eq_true, ↓reduceIte]
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hInr _ hErr => by
            cases hInr; cases hErr; exact mkSysErr_valid e _ hPay rfl)⟩
  let initChunks : Array ByteArray := if acc.size == 0 then #[] else #[acc]
  have hRunEq : readAllRetryEintr raw h chunkCap acc depth = (do
      let res ← loopPow2 (readRetryStep raw h chunkCap) depth initChunks
      match res with
      | .inr out => pure out
      | .inl _ => pure (.error (mkSysErr 5 "host read exceeded retry fuel"))) := rfl
  rw [hRunEq]
  have hLoop := loopPow2_preserves proj (readRetryStep raw h chunkCap)
    (fun out => ∀ err, out = .error err → validSysErrProp err) hStep depth initChunks w hwf
  try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hLoop ⊢
  cases hL : loopPow2 (readRetryStep raw h chunkCap) depth initChunks w with
  | mk lres w₁ =>
    rw [hL] at hLoop
    try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hLoop ⊢
    cases lres with
    | inr out =>
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
      exact ⟨hLoop.1, hLoop.2 out rfl⟩
    | inl _ =>
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
      exact ⟨hLoop.1, (fun _ hErr => by
        cases hErr; exact mkSysErr_valid 5 _ ⟨by decide, by decide⟩ rfl)⟩

private def waitRetryStep {W : Type} (raw : RawHostOpsM (StateM W)) (pid : Pid) (_ : Unit) :
    StateM W (Sum Unit (Except PostForkError ChildWaitStatus)) := do
  match ← raw.waitOnce pid with
  | .ok st => pure (.inr (.ok st))
  | .error e =>
    if e == 4 then pure (.inl ()) else pure (.inr (.error (mkSysErr e "waitpid failed")))

/-- Soundness of `waitRetryEintr`: preserves `HostInv` and validates `ChildWaitStatus` or `PostForkError`. -/
theorem waitRetryEintr_sound {W : Type} {proj : W → HostStepState} {raw : RawHostOpsM (StateM W)}
    (hRaw : Core.ObeysStep proj rawStepWf (execRawStep raw) allowedRawStep)
    (pid : Pid) (depth : Nat) (w : W) (hwf : rawStepWf (proj w) = true) :
    let r := (waitRetryEintr raw pid depth).run w
    HostInv proj w r.2 ∧ (∀ wst, r.1 = .ok wst → validWaitStatusProp wst) ∧
      (∀ err, r.1 = .error err → validSysErrProp err) := by
  have hStep : ∀ (u : Unit) (w₀ : W), rawStepWf (proj w₀) = true →
      let r := (waitRetryStep raw pid u).run w₀
      HostInv proj w₀ r.2 ∧ (∀ (out : Except PostForkError ChildWaitStatus), r.1 = .inr out →
        (∀ wst, out = .ok wst → validWaitStatusProp wst) ∧
        (∀ err, out = .error err → validSysErrProp err)) := by
    intro _ w₀ hwf₀
    try dsimp only [waitRetryStep, Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
    have hCallStep := hRaw w₀ (.waitOnce pid) hwf₀
    try dsimp only [allowedRawStep, execRawStep, Functor.map, StateT.map,
      Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCallStep
    cases hCall : raw.waitOnce pid w₀ with
    | mk res w₁ =>
      rw [hCall] at hCallStep
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCallStep ⊢
      rcases hCallStep with ⟨_, hwf₁, hLe₁, hPay⟩
      cases res with
      | ok st =>
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPay ⊢
        exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hInr => by
          cases hInr; exact ⟨(fun _ hOk => by cases hOk; exact hPay), (fun _ hErr => nomatch hErr)⟩)⟩
      | error e =>
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPay ⊢
        by_cases he4 : (e == 4) = true
        · simp only [he4, ↓reduceIte]
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hInr => nomatch hInr)⟩
        · simp only [he4, Bool.false_eq_true, ↓reduceIte]
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hInr => by
            cases hInr; exact ⟨(fun _ hOk => nomatch hOk),
              (fun _ hErr => by cases hErr; exact mkSysErr_valid e _ hPay rfl)⟩)⟩
  have hRunEq : waitRetryEintr raw pid depth = (do
      let res ← loopPow2 (waitRetryStep raw pid) depth ()
      match res with
      | .inr out => pure out
      | .inl () => pure (.error (mkSysErr 4 "waitpid exceeded EINTR retry fuel"))) := rfl
  rw [hRunEq]
  have hLoop := loopPow2_preserves proj (waitRetryStep raw pid)
    (fun out => (∀ wst, out = .ok wst → validWaitStatusProp wst) ∧
      (∀ err, out = .error err → validSysErrProp err)) hStep depth () w hwf
  try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hLoop ⊢
  cases hL : loopPow2 (waitRetryStep raw pid) depth () w with
  | mk lres w₁ =>
    rw [hL] at hLoop
    try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hLoop ⊢
    cases lres with
    | inr out =>
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
      exact ⟨hLoop.1, hLoop.2 out rfl⟩
    | inl u =>
      cases u
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
      exact ⟨hLoop.1, (fun _ hOk => nomatch hOk), (fun _ hErr => by
        cases hErr; exact mkSysErr_valid 4 _ ⟨by decide, by decide⟩ rfl)⟩

/-- Soundness of `raw.closeFd`: preserves `HostInv` and bounds any error code in `1..4095`. -/
theorem closeFd_inv {W : Type} {proj : W → HostStepState} {raw : RawHostOpsM (StateM W)}
    (hRaw : Core.ObeysStep proj rawStepWf (execRawStep raw) allowedRawStep)
    (h : Nat) (w : W) (hwf : rawStepWf (proj w) = true) :
    let r := (raw.closeFd h).run w
    HostInv proj w r.2 ∧ (∀ e, r.1 = .error e → validHostErrnoProp e) := by
  have hStep := hRaw w (.closeFd h) hwf
  try dsimp only [allowedRawStep, execRawStep, Functor.map, StateT.map,
    Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
  cases hCall : raw.closeFd h w with
  | mk res w₁ =>
    rw [hCall] at hStep
    try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
    rcases hStep with ⟨_, hwf₁, hLe₁, hPay⟩
    cases res with
    | ok _ => exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hE => nomatch hE)⟩
    | error e =>
      try dsimp only at hPay
      exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hE => by cases hE; exact hPay)⟩

/-- Best-effort `closeListQuiet` preserves `HostInv`. -/
theorem closeListQuiet_inv {W : Type} {proj : W → HostStepState} {raw : RawHostOpsM (StateM W)}
    (hRaw : Core.ObeysStep proj rawStepWf (execRawStep raw) allowedRawStep) (hs : List Nat) :
    ∀ (w : W), rawStepWf (proj w) = true → HostInv proj w ((closeListQuiet raw hs).run w).2 := by
  induction hs with
  | nil => intro w hwf; exact hostInv_refl hwf
  | cons h tl ih =>
    intro w hwf
    have h₁ := (closeFd_inv hRaw h w hwf).1
    try dsimp only [closeListQuiet, Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at h₁ ⊢
    cases hCall : raw.closeFd h w with
    | mk _ w₁ =>
      rw [hCall] at h₁
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at h₁ ⊢
      exact hostInv_trans h₁ (ih w₁ h₁.1)

/-- Soundness of `probeRef`: preserves `HostInv` and yields `validSysErrProp` on errors. -/
theorem probeRef_sound {W : Type} {proj : W → HostStepState} {raw : RawHostOpsM (StateM W)}
    (hRaw : Core.ObeysStep proj rawStepWf (execRawStep raw) allowedRawStep)
    (ref : FdRef Nat) (w : W) (hwf : rawStepWf (proj w) = true) :
    let r := (probeRef raw ref).run w
    HostInv proj w r.2 ∧ (∀ err, r.1 = .error err → validSysErrProp err) := by
  cases ref with
  | raw n =>
    have hStep := hRaw w (.probeFdOpen n) hwf
    try dsimp only [allowedRawStep, execRawStep, Functor.map, StateT.map,
      probeRef, Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
    cases hCall : raw.probeFdOpen n w with
    | mk res w₁ =>
      rw [hCall] at hStep
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
      rcases hStep with ⟨_, hwf₁, hLe₁, hPay⟩
      cases res with
      | ok u =>
        cases u
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hE => nomatch hE)⟩
      | error e =>
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPay ⊢
        refine ⟨⟨hwf₁, hLe₁⟩, fun _ hE => ?_⟩
        cases hE
        have hNe : !(s!"caller fd {n} is not open").isEmpty = true := by simp [String.isEmpty, toString]
        exact mkSysErr_valid e _ hPay hNe
  | handle h =>
    have hStep := hRaw w (.probeHandleOpen h) hwf
    try dsimp only [allowedRawStep, execRawStep, Functor.map, StateT.map,
      probeRef, Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
    cases hCall : raw.probeHandleOpen h w with
    | mk res w₁ =>
      rw [hCall] at hStep
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
      rcases hStep with ⟨_, hwf₁, hLe₁, hPay⟩
      cases res with
      | ok u =>
        cases u
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hE => nomatch hE)⟩
      | error e =>
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPay ⊢
        exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hE => by cases hE; exact mkSysErr_valid e _ hPay rfl)⟩

/-- Soundness of `probeRefList`: preserves `HostInv` and yields `validSysErrProp` on errors. -/
theorem probeRefList_sound {W : Type} {proj : W → HostStepState} {raw : RawHostOpsM (StateM W)}
    (hRaw : Core.ObeysStep proj rawStepWf (execRawStep raw) allowedRawStep) (rs : List (FdRef Nat)) :
    ∀ (w : W), rawStepWf (proj w) = true →
      let r := (probeRefList raw rs).run w; HostInv proj w r.2 ∧ (∀ err, r.1 = .error err → validSysErrProp err) := by
  induction rs with
  | nil => intro w hwf; exact ⟨hostInv_refl hwf, (fun _ hE => nomatch hE)⟩
  | cons hd tl ih =>
    intro w hwf
    have h₁ := probeRef_sound hRaw hd w hwf
    try dsimp only [probeRefList, Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at h₁ ⊢
    cases hCall : probeRef raw hd w with
    | mk res₁ w₁ =>
      rw [hCall] at h₁
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at h₁ ⊢
      cases res₁ with
      | error err =>
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        exact ⟨h₁.1, fun _ hE => h₁.2 _ hE⟩
      | ok u =>
        cases u
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        have h₂ := ih w₁ h₁.1.1
        try dsimp only [StateT.run] at h₂
        exact ⟨hostInv_trans h₁.1 h₂.1, h₂.2⟩

/-- Soundness of `probeStdioPlan`: preserves `HostInv` and yields `validSysErrProp` on errors. -/
theorem probeStdioPlan_sound {W : Type} {proj : W → HostStepState} {raw : RawHostOpsM (StateM W)}
    (hRaw : Core.ObeysStep proj rawStepWf (execRawStep raw) allowedRawStep)
    (plan : StdioPlan Nat) (w : W) (hwf : rawStepWf (proj w) = true) :
    let r := (probeStdioPlan raw plan).run w
    HostInv proj w r.2 ∧ (∀ err, r.1 = .error err → validSysErrProp err) := by
  cases plan with
  | inherit => exact ⟨hostInv_refl hwf, (fun _ hE => nomatch hE)⟩
  | redirect sIn sOut sErr _ => exact probeRefList_sound hRaw [sIn, sOut, sErr] w hwf

/-- `filterOpenCloseList` preserves `HostInv`. -/
theorem filterOpenCloseList_inv {W : Type} {proj : W → HostStepState} {raw : RawHostOpsM (StateM W)}
    (hRaw : Core.ObeysStep proj rawStepWf (execRawStep raw) allowedRawStep) (rs : List (FdRef Nat)) :
    ∀ (acc : Array (FdRef Nat)) (w : W), rawStepWf (proj w) = true →
      HostInv proj w ((filterOpenCloseList raw rs acc).run w).2 := by
  induction rs with
  | nil => intro _ w hwf; exact hostInv_refl hwf
  | cons r tl ih =>
    intro acc w hwf
    cases r with
    | handle h => exact ih (acc.push (.handle h)) w hwf
    | raw n =>
      have hStep := hRaw w (.probeFdOpen n) hwf
      try dsimp only [allowedRawStep, execRawStep, Functor.map, StateT.map,
        filterOpenCloseList, Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
      cases hCall : raw.probeFdOpen n w with
      | mk res w₁ =>
        rw [hCall] at hStep
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
        rcases hStep with ⟨_, hwf₁, hLe₁, _⟩
        cases res with
        | ok u =>
          cases u
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          exact hostInv_trans ⟨hwf₁, hLe₁⟩ (ih (acc.push (.raw n)) w₁ hwf₁)
        | error _ =>
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          exact hostInv_trans ⟨hwf₁, hLe₁⟩ (ih acc w₁ hwf₁)

/-- Every `ChildFailure` decoded by `decodeChildFailure` carries an `errno` in `1..4095`. -/
theorem decodeChildFailure_errno_valid {bs : ByteArray} {cf : ChildFailure}
    (h : decodeChildFailure bs = some cf) :
    validHostErrnoProp cf.errno := by
  unfold decodeChildFailure at h
  by_cases h0 : (bs.size == 0) = true
  · simp [h0] at h
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
    by_cases h8 : (bs.size != 8) = true
    · simp only [h8, ↓reduceIte, Option.some.injEq] at h; subst h; exact ⟨by decide, by decide⟩
    · simp only [h8, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · injection h with hEq; subst hEq; exact ⟨by decide, by decide⟩
      · cases hStg : FailureStage.ofTag? (bs.get! 2) <;> rw [hStg] at h
        · injection h with hEq; subst hEq; exact ⟨by decide, by decide⟩
        · try dsimp only at h
          split at h
          · rename_i hRange
            injection h with hEq; subst hEq
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hRange
            let rawU := (bs.get! 4).toNat + 256 * (bs.get! 5).toNat +
              65536 * (bs.get! 6).toNat + 16777216 * (bs.get! 7).toNat
            have hToNat : (UInt32.ofNat rawU).toNat = rawU := by simp [UInt32.ofNat, UInt32.toNat]; omega
            exact ⟨by change 1 ≤ (UInt32.ofNat rawU).toNat; rw [hToNat]; exact hRange.1,
              by change (UInt32.ofNat rawU).toNat ≤ 4095; rw [hToNat]; exact hRange.2⟩
          · injection h with hEq; subst hEq; exact ⟨by decide, by decide⟩

/-- Soundness of `awaitExecOrFailure`: preserves `HostInv` and validates `SpawnedChild` or `validRuntimeErrProp`. -/
theorem awaitExecOrFailure_sound {W : Type} {proj : W → HostStepState} {raw : RawHostOpsM (StateM W)}
    (hRaw : Core.ObeysStep proj rawStepWf (execRawStep raw) allowedRawStep)
    (pid : Pid) (pgid? : Option Pid) (errRead fuel : Nat) (barrierBroken : Bool) (w : W)
    (hwf : rawStepWf (proj w) = true) :
    let r := (awaitExecOrFailure raw pid pgid? errRead fuel barrierBroken).run w
    HostInv proj w r.2 ∧ (∀ ch, r.1 = .ok ch → ch.pid = pid ∧ ch.pgid = pgid?) ∧
      (∀ err, r.1 = .error err → validRuntimeErrProp err) := by
  have hRead := readAllRetryEintr_sound hRaw errRead 16 ByteArray.empty fuel w hwf
  try dsimp only [awaitExecOrFailure, Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hRead ⊢
  cases hR : readAllRetryEintr raw errRead 16 ByteArray.empty fuel w with
  | mk repRes w₁ =>
    rw [hR] at hRead
    try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hRead ⊢
    have hCl := (closeFd_inv hRaw errRead w₁ hRead.1.1).1
    try dsimp only [StateT.run] at hCl
    cases hC : raw.closeFd errRead w₁ with
    | mk _ w₂ =>
      rw [hC] at hCl
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCl ⊢
      have hInv₂ := hostInv_trans hRead.1 hCl
      cases repRes with
      | error err =>
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        exact ⟨hInv₂, (fun _ hOk => nomatch hOk),
          (fun _ hE => by cases hE; exact Or.inl (hRead.2 err rfl))⟩
      | ok repBytes =>
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        have hWaitBranch : ∀ (cf : ChildFailure), validHostErrnoProp cf.errno →
            let r := (StateT.bind (waitRetryEintr raw pid fuel) fun __do_lift =>
              match __do_lift with
              | Except.error err => StateT.pure (Except.error err)
              | Except.ok wst =>
                StateT.pure (Except.error
                  (mkChildFailedErr { cf with waitStatus := some wst }
                    "child setup or execve failed"))) w₂
            HostInv proj w r.2 ∧
              (∀ (ch : SpawnedChild), r.1 = .ok ch → ch.pid = pid ∧ ch.pgid = pgid?) ∧
              (∀ err, r.1 = .error err → validRuntimeErrProp err) := by
          intro cf hCfErr
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          have hWait := waitRetryEintr_sound hRaw pid fuel w₂ hInv₂.1
          try dsimp only [StateT.run] at hWait
          cases hW : waitRetryEintr raw pid fuel w₂ with
          | mk wRes w₃ =>
            rw [hW] at hWait
            try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hWait ⊢
            have hInv₃ := hostInv_trans hInv₂ hWait.1
            cases wRes with
            | error err =>
              try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
              exact ⟨hInv₃, (fun _ hOk => nomatch hOk),
                (fun _ hE => by cases hE; exact Or.inl (hWait.2.2 err rfl))⟩
            | ok wst =>
              try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
              refine ⟨hInv₃, (fun _ hOk => nomatch hOk), fun _ hE => ?_⟩
              cases hE
              exact Or.inr ⟨rfl, rfl, { cf with waitStatus := some wst }, wst,
                rfl, rfl, rfl, hWait.2.1 wst rfl, hCfErr⟩
        cases hDec : decodeChildFailure repBytes with
        | some cf =>
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          exact hWaitBranch cf (decodeChildFailure_errno_valid hDec)
        | none =>
          cases barrierBroken with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
            exact ⟨hInv₂, (fun _ hOk => by cases hOk; exact ⟨rfl, rfl⟩), (fun _ hE => nomatch hE)⟩
          | true =>
            simp only [↓reduceIte]
            try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
            exact hWaitBranch { stage := .wireTruncated, errno := Errno.EIO } ⟨by decide, by decide⟩

/-- Soundness of `performFork`: preserves `HostInv`, bounds `pid` in `1..maxLinuxPid`, and validates `.error`. -/
theorem performFork_sound {W : Type} {proj : W → HostStepState} {raw : RawHostOpsM (StateM W)}
    (hRaw : Core.ObeysStep proj rawStepWf (execRawStep raw) allowedRawStep)
    (spec : ChildSpecM Nat) (syncRead? : Option Nat) (errWrite : Nat)
    (openCloseFds extraClose : Array (FdRef Nat)) (withBarrier : Bool) (w : W)
    (hwf : rawStepWf (proj w) = true) :
    let r := (performFork raw spec syncRead? errWrite openCloseFds extraClose withBarrier).run w
    HostInv proj w r.2 ∧ (∀ pid, r.1 = .ok pid → 1 ≤ pid ∧ pid ≤ maxLinuxPid) ∧
      (∀ err, r.1 = .error err → validSysErrProp err) := by
  have hStep := hRaw w (.forkRun (flagsOfSpec spec withBarrier) spec.forkMode syncRead? errWrite
    (stdioRefsArray spec.stdio) (openCloseFds ++ extraClose) (FdPolicy.keepFds spec.fdPolicy)
    spec.cwd spec.path spec.argv (formatEnvEntriesBytes spec.rawEnv spec.env)) hwf
  try dsimp only [allowedRawStep, execRawStep, Functor.map, StateT.map,
    performFork, Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
  cases hCall : raw.forkRun (flagsOfSpec spec withBarrier) spec.forkMode syncRead? errWrite
      (stdioRefsArray spec.stdio) (openCloseFds ++ extraClose) (FdPolicy.keepFds spec.fdPolicy)
      spec.cwd spec.path spec.argv (formatEnvEntriesBytes spec.rawEnv spec.env) w with
  | mk res w₁ =>
    rw [hCall] at hStep
    try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
    rcases hStep with ⟨_, hwf₁, hLe₁, hPay⟩
    cases res with
    | error e =>
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPay ⊢
      exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hOk => nomatch hOk),
        (fun _ hE => by cases hE; exact mkSysErr_valid e _ hPay rfl)⟩
    | ok pid =>
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPay ⊢
      cases spec.processGroup with
      | inherit =>
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        exact ⟨⟨hwf₁, hLe₁⟩, (fun _ hOk => by cases hOk; exact ⟨hPay.1, hPay.2.1⟩),
          (fun _ hE => nomatch hE)⟩
      | newGroup =>
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        have hPgid := hRaw w₁ (.setpgidOnce pid pid) hwf₁
        try dsimp only [allowedRawStep, execRawStep, Functor.map, StateT.map,
          Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPgid
        cases hSet : raw.setpgidOnce pid pid w₁ with
        | mk _ w₂ =>
          rw [hSet] at hPgid
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPgid ⊢
          rcases hPgid with ⟨_, hwf₂, hLe₂, _⟩
          exact ⟨hostInv_trans ⟨hwf₁, hLe₁⟩ ⟨hwf₂, hLe₂⟩,
            (fun _ hOk => by cases hOk; exact ⟨hPay.1, hPay.2.1⟩),
            (fun _ hE => nomatch hE)⟩

end LeanSwe.PostFork.Proofs
