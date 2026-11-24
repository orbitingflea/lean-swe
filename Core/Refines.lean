import Core.Obeys

namespace Core

/-- Backward-compatible alias for `Core.ObeysPure`. -/
abbrev RefinesPure {In Out : Type} (impl : In → Out) (allowed : In → Out → Prop) : Prop :=
  ObeysPure impl allowed

/-- Backward-compatible alias for `Core.ObeysPure2`. -/
abbrev RefinesPure2 {A B Out : Type} (impl : A → B → Out) (allowed : A → B → Out → Prop) : Prop :=
  ObeysPure2 impl allowed

/-- Backward-compatible alias for `Core.ObeysPure3`. -/
abbrev RefinesPure3 {A B C Out : Type} (impl : A → B → C → Out)
    (allowed : A → B → C → Out → Prop) : Prop :=
  ObeysPure3 impl allowed

/-- Backward-compatible alias for `Core.ObeysPure4`. -/
abbrev RefinesPure4 {A B C D Out : Type} (impl : A → B → C → D → Out)
    (allowed : A → B → C → D → Out → Prop) : Prop :=
  ObeysPure4 impl allowed

/-- Backward-compatible alias for `Core.ObeysPureEq`. -/
abbrev RefinesPureEq {In Out : Type} (impl model : In → Out) : Prop :=
  ObeysPureEq impl model

/-- Backward-compatible alias for `Core.ObeysPureEq2`. -/
abbrev RefinesPureEq2 {A B Out : Type} (impl model : A → B → Out) : Prop :=
  ObeysPureEq2 impl model

/-- Backward-compatible alias for `Core.ObeysPureEq3`. -/
abbrev RefinesPureEq3 {A B C Out : Type} (impl model : A → B → C → Out) : Prop :=
  ObeysPureEq3 impl model

/-- Backward-compatible alias for `Core.ObeysPureEq4`. -/
abbrev RefinesPureEq4 {A B C D Out : Type} (impl model : A → B → C → D → Out) : Prop :=
  ObeysPureEq4 impl model

/-- Backward-compatible alias for `Core.ObeysStep`. -/
abbrev RefinesStep {W S Req Out : Type} (proj : W → S) (wf : S → Bool)
    (step : Req → StateM W Out) (allowedStep : S → Req → Out → S → Prop) : Prop :=
  ObeysStep proj wf step allowedStep

/-- Backward-compatible alias for `Core.ObeysStepId`. -/
abbrev RefinesStepId {S Req Out : Type} := @ObeysStep S S Req Out id

/-- Backward-compatible alias for `Core.ObeysStepFrom`. -/
abbrev RefinesStepFrom
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
  ObeysStepFrom mapS rawWf execRaw rawAllowed pkgWf mkApi execPkg pkgAllowed

/-- Backward-compatible alias for `Core.ObeysStepFromFinally`. -/
abbrev RefinesStepFromFinally.{u₁, u₂}
    {RawS PkgS : Type}
    {RawOps : (Type → Type) → Type u₁}
    {PkgApi : (Type → Type) → Type u₂}
    {RawReq RawOut PkgReq PkgOut : Type}
    (mapS : RawS → PkgS)
    (rawWf : RawS → Bool)
    (execRaw : {W : Type} → RawOps (StateM W) → RawReq → StateM W RawOut)
    (rawAllowed : RawS → RawReq → RawOut → RawS → Prop)
    (pkgWf : PkgS → Bool)
    (mkApi : {m : Type → Type} → [Monad m] → [MonadFinally m] → RawOps m → PkgApi m)
    (execPkg : {W : Type} → PkgApi (StateM W) → PkgReq → StateM W PkgOut)
    (pkgAllowed : PkgS → PkgReq → PkgOut → PkgS → Prop) : Prop :=
  ObeysStepFromFinally mapS rawWf execRaw rawAllowed pkgWf mkApi execPkg pkgAllowed

/-- Backward-compatible alias for `Core.ObeysStepFrom2`. -/
abbrev RefinesStepFrom2.{u₁, u₂, u₃}
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
  ObeysStepFrom2 mapS rawWf execRaw1 rawAllowed1 execRaw2 rawAllowed2 pkgWf mkApi execPkg pkgAllowed

end Core
