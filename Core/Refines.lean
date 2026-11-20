namespace Core

/-- Pure 1-argument refinement predicate stating that `allowed x (impl x)` holds for all `x`. -/
def RefinesPure {In Out : Type} (impl : In → Out) (allowed : In → Out → Prop) : Prop :=
  ∀ x : In, allowed x (impl x)

/-- Pure 2-argument refinement predicate stating that `allowed a b (impl a b)` holds for all `a, b`. -/
def RefinesPure2 {A B Out : Type} (impl : A → B → Out) (allowed : A → B → Out → Prop) : Prop :=
  ∀ (a : A) (b : B), allowed a b (impl a b)

/-- Pure 3-argument refinement predicate stating that `allowed a b c (impl a b c)` holds for all `a, b, c`. -/
def RefinesPure3 {A B C Out : Type} (impl : A → B → C → Out)
    (allowed : A → B → C → Out → Prop) : Prop :=
  ∀ (a : A) (b : B) (c : C), allowed a b c (impl a b c)

/-- Pure 4-argument refinement predicate stating that `allowed a b c d (impl a b c d)` holds for all `a, b, c, d`. -/
def RefinesPure4 {A B C D Out : Type} (impl : A → B → C → D → Out)
    (allowed : A → B → C → D → Out → Prop) : Prop :=
  ∀ (a : A) (b : B) (c : C) (d : D), allowed a b c d (impl a b c d)

/-- Pure 1-argument deterministic refinement predicate stating that `impl x = model x` for all `x`. -/
def RefinesPureEq {In Out : Type} (impl model : In → Out) : Prop :=
  RefinesPure impl (fun x y => y = model x)

/-- Pure 2-argument deterministic refinement predicate stating that `impl a b = model a b` for all `a, b`. -/
def RefinesPureEq2 {A B Out : Type} (impl model : A → B → Out) : Prop :=
  RefinesPure2 impl (fun a b y => y = model a b)

/-- Pure 3-argument deterministic refinement predicate stating that `impl a b c = model a b c` for all `a, b, c`. -/
def RefinesPureEq3 {A B C Out : Type} (impl model : A → B → C → Out) : Prop :=
  RefinesPure3 impl (fun a b c y => y = model a b c)

/-- Pure 4-argument deterministic refinement predicate stating that `impl a b c d = model a b c d` for all `a, b, c, d`. -/
def RefinesPureEq4 {A B C D Out : Type} (impl model : A → B → C → D → Out) : Prop :=
  RefinesPure4 impl (fun a b c d y => y = model a b c d)

/-- Single-step stateful refinement predicate relating concrete `StateM W Out` transitions under projection `proj` and well-formedness guard `wf` to `allowedStep`. -/
def RefinesStep {W S Req Out : Type} (proj : W → S) (wf : S → Bool)
    (step : Req → StateM W Out) (allowedStep : S → Req → Out → S → Prop) : Prop :=
  ∀ (w : W) (req : Req), wf (proj w) = true →
    let r := (step req).run w
    allowedStep (proj w) req r.1 (proj r.2)

/-- Single-step stateful refinement predicate when concrete state `S` equals abstract state `S` (`proj = id`). -/
abbrev RefinesStepId {S Req Out : Type} := @RefinesStep S S Req Out id

/-- Compositional single-step refinement lifting a verified `RawOps` step contract to a `mkApi`-built `PkgApi` step contract. -/
def RefinesStepFrom
    {RawS PkgS : Type}
    {RawOps PkgApi : (Type → Type) → Type}
    {RawReq RawOut PkgReq PkgOut : Type}
    (mapS : RawS → PkgS)
    (rawWf : RawS → Bool)
    (execRaw : {W : Type} → RawOps (StateM W) → RawReq → StateM W RawOut)
    (rawAllowed : RawS → RawReq → RawOut → RawS → Prop)
    (pkgWf : PkgS → Bool)
    (mkApi : {m : Type → Type} → [Monad m] → RawOps m → PkgApi m)
    (execPkg : {W : Type} → PkgApi (StateM W) → PkgReq → StateM W PkgOut)
    (pkgAllowed : PkgS → PkgReq → PkgOut → PkgS → Prop) : Prop :=
  ∀ {W : Type} (proj : W → RawS) (raw : RawOps (StateM W)),
    RefinesStep proj rawWf (execRaw raw) rawAllowed →
    RefinesStep (mapS ∘ proj) pkgWf (execPkg (mkApi raw)) pkgAllowed

/-- Compositional single-step refinement lifting two verified capability contracts (`RawOps1`, `RawOps2`) to a `mkApi`-built `PkgApi` step contract. -/
def RefinesStepFrom2.{u₁, u₂, u₃}
    {RawS PkgS : Type}
    {RawOps1 : (Type → Type) → Type u₁}
    {RawOps2 : (Type → Type) → Type u₂}
    {PkgApi : (Type → Type) → Type u₃}
    {RawReq1 RawOut1 RawReq2 RawOut2 PkgReq PkgOut : Type}
    (mapS : RawS → PkgS)
    (rawWf : RawS → Bool)
    (execRaw1 : {W : Type} → RawOps1 (StateM W) → RawReq1 → StateM W RawOut1)
    (rawAllowed1 : RawS → RawReq1 → RawOut1 → RawS → Prop)
    (execRaw2 : {W : Type} → RawOps2 (StateM W) → RawReq2 → StateM W RawOut2)
    (rawAllowed2 : RawS → RawReq2 → RawOut2 → RawS → Prop)
    (pkgWf : PkgS → Bool)
    (mkApi : {m : Type → Type} → [Monad m] → RawOps1 m → RawOps2 m → PkgApi m)
    (execPkg : {W : Type} → PkgApi (StateM W) → PkgReq → StateM W PkgOut)
    (pkgAllowed : PkgS → PkgReq → PkgOut → PkgS → Prop) : Prop :=
  ∀ {W : Type} (proj : W → RawS) (raw1 : RawOps1 (StateM W)) (raw2 : RawOps2 (StateM W)),
    RefinesStep proj rawWf (execRaw1 raw1) rawAllowed1 →
    RefinesStep proj rawWf (execRaw2 raw2) rawAllowed2 →
    RefinesStep (mapS ∘ proj) pkgWf (execPkg (mkApi raw1 raw2)) pkgAllowed

end Core
