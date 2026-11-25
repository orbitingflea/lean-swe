namespace Core

/-- Equality on `Except E α` up to diagnostic message text: `.ok` payloads match exactly,
    while `.error` results agree on `kindOf` with a non-empty implementation `msgOf`. -/
def EqUpToErrMsg {E K α : Type} (kindOf : E → K) (msgOf : E → String)
    (actual expected : Except E α) : Prop :=
  match actual, expected with
  | .ok a, .ok b => a = b
  | .error e₁, .error e₂ => kindOf e₁ = kindOf e₂ ∧ !(msgOf e₁).isEmpty
  | _, _ => False

/-- Pure 1-argument refinement predicate stating that `allowed x (impl x)` holds for all `x`. -/
def ObeysPure {In Out : Type} (impl : In → Out) (allowed : In → Out → Prop) : Prop :=
  ∀ x : In, allowed x (impl x)

/-- Pure 2-argument refinement predicate stating that `allowed a b (impl a b)` holds for all `a, b`. -/
def ObeysPure2 {A B Out : Type} (impl : A → B → Out) (allowed : A → B → Out → Prop) : Prop :=
  ∀ (a : A) (b : B), allowed a b (impl a b)

/-- Pure 3-argument refinement predicate stating that `allowed a b c (impl a b c)` holds for all `a, b, c`. -/
def ObeysPure3 {A B C Out : Type} (impl : A → B → C → Out)
    (allowed : A → B → C → Out → Prop) : Prop :=
  ∀ (a : A) (b : B) (c : C), allowed a b c (impl a b c)

/-- Pure 4-argument refinement predicate stating that `allowed a b c d (impl a b c d)` holds for all `a, b, c, d`. -/
def ObeysPure4 {A B C D Out : Type} (impl : A → B → C → D → Out)
    (allowed : A → B → C → D → Out → Prop) : Prop :=
  ∀ (a : A) (b : B) (c : C) (d : D), allowed a b c d (impl a b c d)

/-- Pure 1-argument deterministic refinement predicate stating that `impl x = model x` for all `x`. -/
def ObeysPureEq {In Out : Type} (impl model : In → Out) : Prop :=
  ObeysPure impl (fun x y => y = model x)

/-- Pure 2-argument deterministic refinement predicate stating that `impl a b = model a b` for all `a, b`. -/
def ObeysPureEq2 {A B Out : Type} (impl model : A → B → Out) : Prop :=
  ObeysPure2 impl (fun a b y => y = model a b)

/-- Pure 3-argument deterministic refinement predicate stating that `impl a b c = model a b c` for all `a, b, c`. -/
def ObeysPureEq3 {A B C Out : Type} (impl model : A → B → C → Out) : Prop :=
  ObeysPure3 impl (fun a b c y => y = model a b c)

/-- Pure 4-argument deterministic refinement predicate stating that `impl a b c d = model a b c d` for all `a, b, c, d`. -/
def ObeysPureEq4 {A B C D Out : Type} (impl model : A → B → C → D → Out) : Prop :=
  ObeysPure4 impl (fun a b c d y => y = model a b c d)

/-- Pure 1-argument fallible refinement predicate stating exact `.ok` equality and `.error`
    structural equality (`kindOf`) with non-empty implementation diagnostics (`msgOf`). -/
def ObeysPureEqUpToErrMsg {In E K α : Type} (kindOf : E → K) (msgOf : E → String)
    (impl model : In → Except E α) : Prop :=
  ∀ x : In, EqUpToErrMsg kindOf msgOf (impl x) (model x)

/-- Pure 2-argument fallible refinement up to diagnostic message text. -/
def ObeysPureEqUpToErrMsg2 {A B E K α : Type} (kindOf : E → K) (msgOf : E → String)
    (impl model : A → B → Except E α) : Prop :=
  ∀ (a : A) (b : B), EqUpToErrMsg kindOf msgOf (impl a b) (model a b)

/-- Pure 3-argument fallible refinement up to diagnostic message text. -/
def ObeysPureEqUpToErrMsg3 {A B C E K α : Type} (kindOf : E → K) (msgOf : E → String)
    (impl model : A → B → C → Except E α) : Prop :=
  ∀ (a : A) (b : B) (c : C), EqUpToErrMsg kindOf msgOf (impl a b c) (model a b c)

/-- Pure 4-argument fallible refinement up to diagnostic message text. -/
def ObeysPureEqUpToErrMsg4 {A B C D E K α : Type} (kindOf : E → K) (msgOf : E → String)
    (impl model : A → B → C → D → Except E α) : Prop :=
  ∀ (a : A) (b : B) (c : C) (d : D), EqUpToErrMsg kindOf msgOf (impl a b c d) (model a b c d)

/-- Injectivity of a nondeterministic renderer `render : Obj → Tape → Option Raw` up to `equiv`. -/
def RenderInjectiveModulo {Obj Tape Raw : Type}
    (render : Obj → Tape → Option Raw) (equiv : Obj → Obj → Prop) : Prop :=
  ∀ a b t₁ t₂ raw, render a t₁ = some raw → render b t₂ = some raw → equiv a b

/-- Strict inverse-renderer relational spec for parsers returning `Except Err Obj`:
    `.ok out` requires `wf out`, a witness tape rendering `out` to `raw`, and uniqueness up to
    `equiv`; `.error e` requires non-empty `msgOf e` and that no `(a, t)` renders to `raw`. -/
def InverseRenderSpec {Obj Tape Raw Err : Type}
    (render : Obj → Tape → Option Raw) (wf : Obj → Prop) (equiv : Obj → Obj → Prop)
    (msgOf : Err → String) (raw : Raw) (res : Except Err Obj) : Prop :=
  match res with
  | .ok out =>
    wf out ∧ (∃ tape, render out tape = some raw) ∧ ∀ a t, render a t = some raw → equiv a out
  | .error e =>
    !(msgOf e).isEmpty ∧ ∀ a t, render a t ≠ some raw

/-- Pure parser refinement stating that `parse` obeys `InverseRenderSpec` on every input `raw`. -/
def ObeysInverseRender {Obj Tape Raw Err : Type}
    (parse : Raw → Except Err Obj) (render : Obj → Tape → Option Raw)
    (wf : Obj → Prop) (equiv : Obj → Obj → Prop) (msgOf : Err → String) : Prop :=
  ObeysPure parse (InverseRenderSpec render wf equiv msgOf)

/-- Resource-bounded inverse-renderer relational spec for parsers returning `Except Err Obj`:
    `.ok out` requires `wf out`, a pure-grammar witness tape rendering `out` to `raw`, and
    uniqueness up to `equiv` across all tapes; `.error e` requires non-empty `msgOf e` and that
    any `(a, t)` rendering to `raw` exceeds `withinLimits t`. -/
def InverseRenderWithinSpec {Obj Tape Raw Err : Type}
    (render : Obj → Tape → Option Raw) (withinLimits : Tape → Prop)
    (wf : Obj → Prop) (equiv : Obj → Obj → Prop)
    (msgOf : Err → String) (raw : Raw) (res : Except Err Obj) : Prop :=
  match res with
  | .ok out =>
    wf out ∧ (∃ tape, render out tape = some raw) ∧ ∀ a t, render a t = some raw → equiv a out
  | .error e =>
    !(msgOf e).isEmpty ∧ ∀ a t, render a t = some raw → ¬ withinLimits t

/-- Pure parser refinement stating that `parse` obeys `InverseRenderWithinSpec` on every input `raw`. -/
def ObeysInverseRenderWithin {Obj Tape Raw Err : Type}
    (parse : Raw → Except Err Obj) (render : Obj → Tape → Option Raw)
    (withinLimits : Tape → Prop) (wf : Obj → Prop) (equiv : Obj → Obj → Prop)
    (msgOf : Err → String) : Prop :=
  ObeysPure parse (InverseRenderWithinSpec render withinLimits wf equiv msgOf)

/-- Single-step stateful refinement relating `StateM W Out` transitions under `proj` and `wf` to `allowedStep`. -/
def ObeysStep {W S Req Out : Type} (proj : W → S) (wf : S → Bool)
    (step : Req → StateM W Out) (allowedStep : S → Req → Out → S → Prop) : Prop :=
  ∀ (w : W) (req : Req), wf (proj w) = true →
    let r := (step req).run w
    allowedStep (proj w) req r.1 (proj r.2)

/-- Single-step stateful refinement when concrete state equals abstract state (`proj = id`). -/
abbrev ObeysStepId {S Req Out : Type} := @ObeysStep S S Req Out id

/-- Compositional single-step refinement lifting a verified `RawOps` step contract to a `mkApi`-built `PkgApi`. -/
def ObeysStepFrom
    {RawS PkgS : Type} {RawOps PkgApi : (Type → Type) → Type} {RawReq RawOut PkgReq PkgOut : Type}
    (mapS : RawS → PkgS) (rawWf : RawS → Bool)
    (execRaw : {W : Type} → RawOps (StateM W) → RawReq → StateM W RawOut)
    (rawAllowed : RawS → RawReq → RawOut → RawS → Prop) (pkgWf : PkgS → Bool)
    (mkApi : {m : Type → Type} → [Monad m] → RawOps m → PkgApi m)
    (execPkg : {W : Type} → PkgApi (StateM W) → PkgReq → StateM W PkgOut)
    (pkgAllowed : PkgS → PkgReq → PkgOut → PkgS → Prop) : Prop :=
  ∀ {W : Type} (proj : W → RawS) (raw : RawOps (StateM W)),
    ObeysStep proj rawWf (execRaw raw) rawAllowed →
    ObeysStep (mapS ∘ proj) pkgWf (execPkg (mkApi raw)) pkgAllowed

/-- Compositional single-step refinement lifting a verified `RawOps` step contract to a
    `[MonadFinally m]`-polymorphic `mkApi`-built `PkgApi`. Quantifies over `m := StateM W`
    (returning control flow only; exception-path `IO` cleanup must be verified separately). -/
def ObeysStepFromFinally.{u₁, u₂}
    {RawS PkgS : Type} {RawOps : (Type → Type) → Type u₁} {PkgApi : (Type → Type) → Type u₂}
    {RawReq RawOut PkgReq PkgOut : Type} (mapS : RawS → PkgS) (rawWf : RawS → Bool)
    (execRaw : {W : Type} → RawOps (StateM W) → RawReq → StateM W RawOut)
    (rawAllowed : RawS → RawReq → RawOut → RawS → Prop) (pkgWf : PkgS → Bool)
    (mkApi : {m : Type → Type} → [Monad m] → [MonadFinally m] → RawOps m → PkgApi m)
    (execPkg : {W : Type} → PkgApi (StateM W) → PkgReq → StateM W PkgOut)
    (pkgAllowed : PkgS → PkgReq → PkgOut → PkgS → Prop) : Prop :=
  ∀ {W : Type} (proj : W → RawS) (raw : RawOps (StateM W)),
    ObeysStep proj rawWf (execRaw raw) rawAllowed →
    ObeysStep (mapS ∘ proj) pkgWf (execPkg (mkApi raw)) pkgAllowed

/-- Single-step stateful and `IO.Error`-exceptional refinement relating
    `ExceptT IO.Error (StateM W) Out` transitions under `proj` and `wf` to `allowedStep`. -/
def ObeysStepExcept {W S Req Out : Type} (proj : W → S) (wf : S → Bool)
    (step : Req → ExceptT IO.Error (StateM W) Out)
    (allowedStep : S → Req → Except IO.Error Out → S → Prop) : Prop :=
  ∀ (w : W) (req : Req), wf (proj w) = true →
    let r := (step req).run.run w
    allowedStep (proj w) req r.1 (proj r.2)

/-- Compositional single-step refinement lifting a verified `RawOps` step contract over
    `ExceptT IO.Error (StateM W)` to a `[Monad m] → [MonadFinally m] → [MonadExceptOf IO.Error m]`
    `mkApi`-built `PkgApi`, faithfully tracking `throwThe IO.Error`, `tryCatch`, and `tryFinally'`. -/
def ObeysStepFromExcept.{u₁, u₂}
    {RawS PkgS : Type} {RawOps : (Type → Type) → Type u₁} {PkgApi : (Type → Type) → Type u₂}
    {RawReq RawOut PkgReq PkgOut : Type} (mapS : RawS → PkgS) (rawWf : RawS → Bool)
    (execRaw : {W : Type} → RawOps (ExceptT IO.Error (StateM W)) → RawReq → ExceptT IO.Error (StateM W) RawOut)
    (rawAllowed : RawS → RawReq → Except IO.Error RawOut → RawS → Prop) (pkgWf : PkgS → Bool)
    (mkApi : {m : Type → Type} → [Monad m] → [MonadFinally m] → [MonadExceptOf IO.Error m] → RawOps m → PkgApi m)
    (execPkg : {W : Type} → PkgApi (ExceptT IO.Error (StateM W)) → PkgReq → ExceptT IO.Error (StateM W) PkgOut)
    (pkgAllowed : PkgS → PkgReq → Except IO.Error PkgOut → PkgS → Prop) : Prop :=
  ∀ {W : Type} (proj : W → RawS) (raw : RawOps (ExceptT IO.Error (StateM W))),
    ObeysStepExcept proj rawWf (execRaw raw) rawAllowed →
    ObeysStepExcept (mapS ∘ proj) pkgWf (execPkg (mkApi raw)) pkgAllowed

/-- Compositional single-step refinement lifting two verified capability contracts to a `mkApi`-built `PkgApi`. -/
def ObeysStepFrom2.{u₁, u₂, u₃}
    {RawS PkgS : Type} {RawOps1 : (Type → Type) → Type u₁} {RawOps2 : (Type → Type) → Type u₂}
    {PkgApi : (Type → Type) → Type u₃} {RawReq1 RawOut1 RawReq2 RawOut2 PkgReq PkgOut : Type}
    (mapS : RawS → PkgS) (rawWf : RawS → Bool)
    (execRaw1 : {W : Type} → RawOps1 (StateM W) → RawReq1 → StateM W RawOut1)
    (rawAllowed1 : RawS → RawReq1 → RawOut1 → RawS → Prop)
    (execRaw2 : {W : Type} → RawOps2 (StateM W) → RawReq2 → StateM W RawOut2)
    (rawAllowed2 : RawS → RawReq2 → RawOut2 → RawS → Prop) (pkgWf : PkgS → Bool)
    (mkApi : {m : Type → Type} → [Monad m] → RawOps1 m → RawOps2 m → PkgApi m)
    (execPkg : {W : Type} → PkgApi (StateM W) → PkgReq → StateM W PkgOut)
    (pkgAllowed : PkgS → PkgReq → PkgOut → PkgS → Prop) : Prop :=
  ∀ {W : Type} (proj : W → RawS) (raw1 : RawOps1 (StateM W)) (raw2 : RawOps2 (StateM W)),
    ObeysStep proj rawWf (execRaw1 raw1) rawAllowed1 →
    ObeysStep proj rawWf (execRaw2 raw2) rawAllowed2 →
    ObeysStep (mapS ∘ proj) pkgWf (execPkg (mkApi raw1 raw2)) pkgAllowed

/-- Construct `EqUpToErrMsg` on `.ok` values from payload equality. -/
theorem EqUpToErrMsg.ok {E K α : Type} {kindOf : E → K} {msgOf : E → String}
    {a b : α} (h : a = b) : EqUpToErrMsg kindOf msgOf (.ok a) (.ok b) :=
  h

/-- Construct `EqUpToErrMsg` on `.error` values from matching metadata and a non-empty message. -/
theorem EqUpToErrMsg.error {E K α : Type} {kindOf : E → K} {msgOf : E → String}
    {e₁ e₂ : E} (hKind : kindOf e₁ = kindOf e₂) (hMsg : !(msgOf e₁).isEmpty) :
    @EqUpToErrMsg E K α kindOf msgOf (.error e₁) (.error e₂) :=
  ⟨hKind, hMsg⟩

/-- Exact equality implies `EqUpToErrMsg` whenever errors carry a non-empty message. -/
theorem EqUpToErrMsg.of_eq {E K α : Type} {kindOf : E → K} {msgOf : E → String}
    {actual expected : Except E α} (hEq : actual = expected)
    (hMsg : ∀ e, expected = .error e → !(msgOf e).isEmpty) :
    EqUpToErrMsg kindOf msgOf actual expected := by
  subst hEq
  cases actual with
  | ok _ => rfl
  | error e => exact ⟨rfl, hMsg e rfl⟩

/-- Transitivity of `EqUpToErrMsg`. -/
theorem EqUpToErrMsg.trans {E K α : Type} {kindOf : E → K} {msgOf : E → String}
    {x y z : Except E α} (hxy : EqUpToErrMsg kindOf msgOf x y)
    (hyz : EqUpToErrMsg kindOf msgOf y z) : EqUpToErrMsg kindOf msgOf x z := by
  cases x <;> cases y <;> cases z <;> simp [EqUpToErrMsg] at hxy hyz ⊢
  · exact ⟨hxy.1.trans hyz.1, hxy.2⟩
  · exact hxy.trans hyz

/-- Derive `ObeysInverseRender` from renderer injectivity plus `.ok` witness and `.error` completeness. -/
theorem ObeysInverseRender.of_injective {Obj Tape Raw Err : Type}
    {parse : Raw → Except Err Obj} {render : Obj → Tape → Option Raw}
    {wf : Obj → Prop} {equiv : Obj → Obj → Prop} {msgOf : Err → String}
    (hInj : RenderInjectiveModulo render equiv)
    (hOk : ∀ raw out, parse raw = .ok out → wf out ∧ ∃ tape, render out tape = some raw)
    (hErr : ∀ raw e, parse raw = .error e → !(msgOf e).isEmpty ∧ ∀ a t, render a t ≠ some raw) :
    ObeysInverseRender parse render wf equiv msgOf := by
  intro raw
  cases hp : parse raw with
  | ok out =>
    rcases hOk raw out hp with ⟨hwf, tape, hRend⟩
    exact ⟨hwf, ⟨tape, hRend⟩, fun a t hA => hInj a out t tape raw hA hRend⟩
  | error e => exact hErr raw e hp

/-- Any rendered wire value round-trips through an `ObeysInverseRender` parser up to `equiv`. -/
theorem ObeysInverseRender.render_roundtrip {Obj Tape Raw Err : Type}
    {parse : Raw → Except Err Obj} {render : Obj → Tape → Option Raw}
    {wf : Obj → Prop} {equiv : Obj → Obj → Prop} {msgOf : Err → String}
    (hParse : ObeysInverseRender parse render wf equiv msgOf)
    {obj : Obj} {tape : Tape} {raw : Raw} (hRend : render obj tape = some raw) :
    ∃ out, parse raw = .ok out ∧ wf out ∧ equiv obj out := by
  have h := hParse raw
  cases hp : parse raw with
  | error e =>
    have hE : !(msgOf e).isEmpty ∧ ∀ a t, render a t ≠ some raw := by
      simpa [InverseRenderSpec, hp] using h
    exact False.elim (hE.2 obj tape hRend)
  | ok out =>
    have hO : wf out ∧ (∃ t, render out t = some raw) ∧ ∀ a t, render a t = some raw → equiv a out := by
      simpa [InverseRenderSpec, hp] using h
    exact ⟨out, rfl, hO.1, hO.2.2 obj tape hRend⟩

/-- Derive `ObeysInverseRenderWithin` from renderer injectivity plus `.ok` witness and resource-bounded `.error` completeness. -/
theorem ObeysInverseRenderWithin.of_injective {Obj Tape Raw Err : Type}
    {parse : Raw → Except Err Obj} {render : Obj → Tape → Option Raw}
    {withinLimits : Tape → Prop} {wf : Obj → Prop} {equiv : Obj → Obj → Prop}
    {msgOf : Err → String} (hInj : RenderInjectiveModulo render equiv)
    (hOk : ∀ raw out, parse raw = .ok out → wf out ∧ ∃ tape, render out tape = some raw)
    (hErr : ∀ raw e, parse raw = .error e → !(msgOf e).isEmpty ∧ ∀ a t, render a t = some raw → ¬ withinLimits t) :
    ObeysInverseRenderWithin parse render withinLimits wf equiv msgOf := by
  intro raw
  cases hp : parse raw with
  | ok out =>
    rcases hOk raw out hp with ⟨hwf, tape, hRend⟩
    exact ⟨hwf, ⟨tape, hRend⟩, fun a t hA => hInj a out t tape raw hA hRend⟩
  | error e => exact hErr raw e hp

/-- Any resource-bounded rendered wire value round-trips through an `ObeysInverseRenderWithin` parser up to `equiv`. -/
theorem ObeysInverseRenderWithin.render_roundtrip {Obj Tape Raw Err : Type}
    {parse : Raw → Except Err Obj} {render : Obj → Tape → Option Raw}
    {withinLimits : Tape → Prop} {wf : Obj → Prop} {equiv : Obj → Obj → Prop}
    {msgOf : Err → String}
    (hParse : ObeysInverseRenderWithin parse render withinLimits wf equiv msgOf)
    {obj : Obj} {tape : Tape} {raw : Raw}
    (hLim : withinLimits tape) (hRend : render obj tape = some raw) :
    ∃ out, parse raw = .ok out ∧ wf out ∧ equiv obj out := by
  have h := hParse raw
  cases hp : parse raw with
  | error e =>
    have hE : !(msgOf e).isEmpty ∧ ∀ a t, render a t = some raw → ¬ withinLimits t := by
      simpa [InverseRenderWithinSpec, hp] using h
    exact False.elim (hE.2 obj tape hRend hLim)
  | ok out =>
    have hO : wf out ∧ (∃ t, render out t = some raw) ∧ ∀ a t, render a t = some raw → equiv a out := by
      simpa [InverseRenderWithinSpec, hp] using h
    exact ⟨out, rfl, hO.1, hO.2.2 obj tape hRend⟩

/-- Weaken the relational postcondition of an `ObeysPure` contract. -/
theorem ObeysPure.weaken {In Out : Type} {impl : In → Out} {r₁ r₂ : In → Out → Prop}
    (h : ObeysPure impl r₁) (hImp : ∀ x y, r₁ x y → r₂ x y) : ObeysPure impl r₂ :=
  fun x => hImp x (impl x) (h x)

/-- Transitivity of deterministic `ObeysPureEq` contracts. -/
theorem ObeysPureEq.trans {In Out : Type} {f g h : In → Out}
    (hfg : ObeysPureEq f g) (hgh : ObeysPureEq g h) : ObeysPureEq f h :=
  fun x => (hfg x).trans (hgh x)

/-- Upgrade an exact `ObeysPureEq` contract on fallible outputs to `ObeysPureEqUpToErrMsg`. -/
theorem ObeysPureEq.toObeysPureEqUpToErrMsg {In E K α : Type}
    {kindOf : E → K} {msgOf : E → String} {impl model : In → Except E α}
    (hEq : ObeysPureEq impl model) (hMsg : ∀ x e, model x = .error e → !(msgOf e).isEmpty) :
    ObeysPureEqUpToErrMsg kindOf msgOf impl model :=
  fun x => EqUpToErrMsg.of_eq (hEq x) (hMsg x)

/-- Transitivity of `ObeysPureEqUpToErrMsg`. -/
theorem ObeysPureEqUpToErrMsg.trans {In E K α : Type} {kindOf : E → K} {msgOf : E → String}
    {f g h : In → Except E α} (hfg : ObeysPureEqUpToErrMsg kindOf msgOf f g)
    (hgh : ObeysPureEqUpToErrMsg kindOf msgOf g h) : ObeysPureEqUpToErrMsg kindOf msgOf f h :=
  fun x => (hfg x).trans (hgh x)

/-- Strengthen the guard or weaken the transition relation of an `ObeysStep` contract. -/
theorem ObeysStep.weaken {W S Req Out : Type} {proj : W → S} {wf₁ wf₂ : S → Bool}
    {step : Req → StateM W Out} {a₁ a₂ : S → Req → Out → S → Prop}
    (h : ObeysStep proj wf₁ step a₁) (hWf : ∀ s, wf₂ s = true → wf₁ s = true)
    (hImp : ∀ s req out s', a₁ s req out s' → a₂ s req out s') : ObeysStep proj wf₂ step a₂ :=
  fun w req hw => hImp _ _ _ _ (h w req (hWf _ hw))

/-- Re-project an `ObeysStep` contract along an abstraction map `f : S₁ → S₂`. -/
theorem ObeysStep.mapProj {W S₁ S₂ Req Out : Type} {proj : W → S₁} {f : S₁ → S₂}
    {wf₁ : S₁ → Bool} {wf₂ : S₂ → Bool} {step : Req → StateM W Out}
    {a₁ : S₁ → Req → Out → S₁ → Prop} {a₂ : S₂ → Req → Out → S₂ → Prop}
    (h : ObeysStep proj wf₁ step a₁) (hWf : ∀ s, wf₂ (f s) = true → wf₁ s = true)
    (hRel : ∀ s req out s', a₁ s req out s' → a₂ (f s) req out (f s')) :
    ObeysStep (f ∘ proj) wf₂ step a₂ :=
  fun w req hw => hRel _ _ _ _ (h w req (hWf _ hw))

/-- Transport an `ObeysStep` contract across pointwise-equal step functions. -/
theorem ObeysStep.of_eq {W S Req Out : Type} {proj : W → S} {wf : S → Bool}
    {step₁ step₂ : Req → StateM W Out} {allowedStep : S → Req → Out → S → Prop}
    (h : ObeysStep proj wf step₁ allowedStep) (hEq : ∀ req w, (step₂ req).run w = (step₁ req).run w) :
    ObeysStep proj wf step₂ allowedStep := by
  intro w req hw
  simpa [hEq req w] using h w req hw

/-- Compose two `ObeysStepFrom` layers vertically across three abstraction tiers. -/
theorem ObeysStepFrom.comp
    {RawS MidS PkgS : Type} {RawOps MidApi PkgApi : (Type → Type) → Type}
    {RawReq RawOut MidReq MidOut PkgReq PkgOut : Type} {map1 : RawS → MidS} {map2 : MidS → PkgS}
    {rawWf : RawS → Bool} {midWf : MidS → Bool} {pkgWf : PkgS → Bool}
    {execRaw : {W : Type} → RawOps (StateM W) → RawReq → StateM W RawOut}
    {rawAllowed : RawS → RawReq → RawOut → RawS → Prop}
    {mkMid : {m : Type → Type} → [Monad m] → RawOps m → MidApi m}
    {execMid : {W : Type} → MidApi (StateM W) → MidReq → StateM W MidOut}
    {midAllowed : MidS → MidReq → MidOut → MidS → Prop}
    {mkPkg : {m : Type → Type} → [Monad m] → MidApi m → PkgApi m}
    {execPkg : {W : Type} → PkgApi (StateM W) → PkgReq → StateM W PkgOut}
    {pkgAllowed : PkgS → PkgReq → PkgOut → PkgS → Prop}
    (h1 : ObeysStepFrom map1 rawWf execRaw rawAllowed midWf mkMid execMid midAllowed)
    (h2 : ObeysStepFrom map2 midWf execMid midAllowed pkgWf mkPkg execPkg pkgAllowed) :
    ObeysStepFrom (map2 ∘ map1) rawWf execRaw rawAllowed pkgWf
      (fun raw => mkPkg (mkMid raw)) execPkg pkgAllowed :=
  fun proj raw hRaw => h2 (map1 ∘ proj) (mkMid raw) (h1 proj raw hRaw)

end Core
