import Core.Obeys

namespace Core

/-- General `Init`-only concurrency capability bundle parameterized over monad `m`, exposing
    mutable reference cells (`Ref`), asynchronous task handles (`TaskHandle`), and error-capturing
    execution so concurrent packages can be verified compositionally without `IO` middle hooks. -/
structure ConcOpsM (m : Type → Type) : Type 1 where
  /-- Opaque mutable reference cell type in `m` (e.g., `IO.Ref` on `IO`). -/
  Ref : Type → Type
  /-- Opaque asynchronous task handle type in `m` (e.g., `Task (Except IO.Error ·)` on `IO`). -/
  TaskHandle : Type → Type
  /-- Allocate a mutable cell initialized to `init`. -/
  mkRef : {α : Type} → α → m (Ref α)
  /-- Read the current value stored in `r`. -/
  readRef : {α : Type} → Ref α → m α
  /-- Replace the value stored in `r` with `v`. -/
  writeRef : {α : Type} → Ref α → α → m Unit
  /-- Atomically update `r` via `f`, returning `(result, nextVal)`. -/
  modifyGetRef : {α β : Type} → Ref α → (α → β × α) → m β
  /-- Spawn a dedicated asynchronous task executing `act`. -/
  spawnTask : {α : Type} → m α → m (TaskHandle α)
  /-- Non-blocking check returning `true` iff `t` has completed. -/
  hasFinished : {α : Type} → TaskHandle α → m Bool
  /-- Non-blocking poll returning `some res` once `t` completes, or `none` if still pending. -/
  pollTask : {α : Type} → TaskHandle α → m (Option (Except String α))
  /-- Wait until `t` completes, returning `.ok val` or `.error reason`. -/
  waitTask : {α : Type} → TaskHandle α → m (Except String α)
  /-- Execute `act`, converting any monadic runtime error into `.error reason`. -/
  tryCatchMsg : {α : Type} → m α → m (Except String α)

/-- Atomically update `r` in place via `f` using `ConcOpsM.modifyGetRef`. -/
def ConcOpsM.modifyRef {m : Type → Type} {α : Type}
    (conc : ConcOpsM m) (r : conc.Ref α) (f : α → α) : m Unit :=
  conc.modifyGetRef r (fun a => ((), f a))

/-- Canonical `IO` concurrency capability bundle backed solely by `Init` (`IO.Ref`,
    `IO.asTask (prio := .dedicated)`, `IO.hasFinished`, `IO.wait`, and `try/catch`). -/
def ioConcOps : ConcOpsM IO where
  Ref := IO.Ref
  TaskHandle := fun α => Task (Except IO.Error α)
  mkRef := fun init => IO.mkRef init
  readRef := fun r => r.get
  writeRef := fun r v => r.set v
  modifyGetRef := fun r f => r.modifyGet f
  spawnTask := fun act => IO.asTask (prio := .dedicated) act
  hasFinished := fun t => (IO.hasFinished t : IO Bool)
  pollTask := fun t => do
    if ← IO.hasFinished t then
      match ← IO.wait t with
      | .ok v => return some (.ok v)
      | .error err => return some (.error (toString err))
    else
      return none
  waitTask := fun t => do
    match ← IO.wait t with
    | .ok v => return .ok v
    | .error err => return .error (toString err)
  tryCatchMsg := fun act => do
    try
      return .ok (← act)
    catch err =>
      return .error (toString err)

/-- Nondeterministic relational concurrency contract on `conc : ConcOpsM (StateM W)` with respect
    to a world invariant `inv : W → Prop`. Existentially tracks per-task postconditions `TaskPost`
    so `spawnTask`, `hasFinished`, `pollTask` (pending `none` or completed `some`), `waitTask`,
    and concurrent `Ref` operations preserve `inv` across every reachable interleaving. -/
def ObeysConc {W : Type} (inv : W → Prop) (conc : ConcOpsM (StateM W)) : Prop :=
  ∃ (TaskPost : {α : Type} → conc.TaskHandle α → (α → Prop) → Prop),
    (∀ {α : Type} (x : α) (w : W), inv w → inv ((conc.mkRef x).run w).2) ∧
    (∀ {α : Type} (r : conc.Ref α) (w : W), inv w → inv ((conc.readRef r).run w).2) ∧
    (∀ {α : Type} (r : conc.Ref α) (v : α) (w : W), inv w → inv ((conc.writeRef r v).run w).2) ∧
    (∀ {α β : Type} (r : conc.Ref α) (f : α → β × α) (w : W), inv w →
      let (b, w') := (conc.modifyGetRef r f).run w
      inv w' ∧ ∃ a : α, (f a).1 = b) ∧
    (∀ {α : Type} (act : StateM W α) (P : α → Prop),
      (∀ w, inv w → let (a, w') := act.run w; inv w' ∧ P a) →
      ∀ w, inv w →
        let (t, w') := (conc.spawnTask act).run w
        inv w' ∧ TaskPost t P) ∧
    (∀ {α : Type} (t : conc.TaskHandle α) (w : W), inv w → inv ((conc.hasFinished t).run w).2) ∧
    (∀ {α : Type} (t : conc.TaskHandle α) (P : α → Prop),
      TaskPost t P →
      ∀ w, inv w →
        let (res, w') := (conc.pollTask t).run w
        inv w' ∧ match res with
          | none => True
          | some (.ok a) => P a
          | some (.error msg) => msg ≠ "") ∧
    (∀ {α : Type} (t : conc.TaskHandle α) (P : α → Prop),
      TaskPost t P →
      ∀ w, inv w →
        let (res, w') := (conc.waitTask t).run w
        inv w' ∧ match res with
          | .ok a => P a
          | .error msg => msg ≠ "") ∧
    (∀ {α : Type} (act : StateM W α) (P : α → Prop),
      (∀ w, inv w → let (a, w') := act.run w; inv w' ∧ P a) →
      ∀ w, inv w →
        let (res, w') := (conc.tryCatchMsg act).run w
        inv w' ∧ match res with
          | .ok a => P a
          | .error msg => msg ≠ "")

/-- Compositional single-step refinement lifting a verified `RawOps` step contract and the
    nondeterministic `ObeysConc` concurrency contract to a `[MonadFinally m]`- and
    `ConcOpsM m`-polymorphic `mkApi`-built `PkgApi`. Quantifies universally over all `W`, `raw`,
    and `conc` satisfying `ObeysStep` and `ObeysConc`. -/
def ObeysStepFromConc.{u₁, u₂}
    {RawS PkgS : Type} {RawOps : (Type → Type) → Type u₁} {PkgApi : (Type → Type) → Type u₂}
    {RawReq RawOut PkgReq PkgOut : Type} (mapS : RawS → PkgS) (rawWf : RawS → Bool)
    (execRaw : {W : Type} → RawOps (StateM W) → RawReq → StateM W RawOut)
    (rawAllowed : RawS → RawReq → RawOut → RawS → Prop) (pkgWf : PkgS → Bool)
    (mkApi : {m : Type → Type} → [Monad m] → [MonadFinally m] → RawOps m → ConcOpsM m → PkgApi m)
    (execPkg : {W : Type} → PkgApi (StateM W) → PkgReq → StateM W PkgOut)
    (pkgAllowed : PkgS → PkgReq → PkgOut → PkgS → Prop) : Prop :=
  ∀ {W : Type} (proj : W → RawS) (raw : RawOps (StateM W)) (conc : ConcOpsM (StateM W)),
    ObeysStep proj rawWf (execRaw raw) rawAllowed →
    ObeysConc (fun w => rawWf (proj w) = true) conc →
    ObeysStep (mapS ∘ proj) pkgWf (execPkg (mkApi raw conc)) pkgAllowed

end Core
