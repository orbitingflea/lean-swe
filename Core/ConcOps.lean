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
  tryCatchMsg := fun act =>
    tryCatch (act >>= fun a => pure (.ok a)) (fun err => pure (.error (toString err)))

/-- Persistent mutable state-cell capability parameterized over monad `m` and state `S`,
    allowing handle-table packages to share pure slot state across top-level calls without
    same-package `IO` middle hooks. -/
structure StateCellM (m : Type → Type) (S : Type) : Type 1 where
  /-- Read the current value stored in the cell. -/
  get : m S
  /-- Atomically update the cell via `f`, returning `(result, nextVal)`. -/
  modifyGet : {α : Type} → (S → α × S) → m α

/-- Atomically update `cell` in place via `f` using `StateCellM.modifyGet`. -/
def StateCellM.modify {m : Type → Type} {S : Type}
    (cell : StateCellM m S) (f : S → S) : m Unit :=
  cell.modifyGet (fun s => ((), f s))

/-- Canonical `IO` state-cell capability backed directly by an `Init` `IO.Ref S`. -/
def ioStateCell {S : Type} (r : IO.Ref S) : StateCellM IO S where
  get := (r.get : BaseIO S)
  modifyGet := fun f => (r.modifyGet f : BaseIO _)

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

/-- Lens and OS-frame disjointness contract for `cell : StateCellM (StateM W) CellT` relative to
    `projRaw : W → RawS` and `projCell : W → CellT`: `cell.get` and `cell.modifyGet` read and
    update `projCell` deterministically while leaving `projRaw` unchanged. -/
def ObeysStateCell {W RawS CellT : Type} (projRaw : W → RawS) (projCell : W → CellT)
    (cell : StateCellM (StateM W) CellT) : Prop :=
  (∀ w : W,
    let (s, w') := cell.get.run w
    s = projCell w ∧ projCell w' = projCell w ∧ projRaw w' = projRaw w) ∧
  (∀ {α : Type} (f : CellT → α × CellT) (w : W),
    let (a, w') := (cell.modifyGet f).run w
    a = (f (projCell w)).1 ∧ projCell w' = (f (projCell w)).2 ∧ projRaw w' = projRaw w)

/-- Frame-preserving concurrency contract on `conc : ConcOpsM (StateM W)` with respect to world
    invariant `inv : W → Prop` and binary frame relation `frame : W → W → Prop`. Preserves `inv`
    and `frame` across `Ref` operations, task lifecycle operations (including cross-call handles
    stored in a `StateCellM`), and relational `tryCatchMsg` execution. -/
def ObeysConcFrame {W : Type} (inv : W → Prop) (frame : W → W → Prop)
    (conc : ConcOpsM (StateM W)) : Prop :=
  ∃ (TaskPost : {α : Type} → conc.TaskHandle α → (α → Prop) → Prop),
    (∀ {α : Type} (x : α) (w : W), inv w →
      let (_, w') := (conc.mkRef x).run w
      inv w' ∧ frame w w') ∧
    (∀ {α : Type} (r : conc.Ref α) (w : W), inv w →
      let (_, w') := (conc.readRef r).run w
      inv w' ∧ frame w w') ∧
    (∀ {α : Type} (r : conc.Ref α) (v : α) (w : W), inv w →
      let (_, w') := (conc.writeRef r v).run w
      inv w' ∧ frame w w') ∧
    (∀ {α β : Type} (r : conc.Ref α) (f : α → β × α) (w : W), inv w →
      let (b, w') := (conc.modifyGetRef r f).run w
      inv w' ∧ frame w w' ∧ ∃ a : α, (f a).1 = b) ∧
    (∀ {α : Type} (act : StateM W α) (P : α → Prop),
      (∀ w, inv w → let (a, w') := act.run w; inv w' ∧ frame w w' ∧ P a) →
      ∀ w, inv w →
        let (t, w') := (conc.spawnTask act).run w
        inv w' ∧ frame w w' ∧ TaskPost t P) ∧
    (∀ {α : Type} (t : conc.TaskHandle α) (w : W), inv w →
      let (_, w') := (conc.hasFinished t).run w
      inv w' ∧ frame w w') ∧
    (∀ {α : Type} (t : conc.TaskHandle α) (w : W), inv w →
      let (res, w') := (conc.pollTask t).run w
      inv w' ∧ frame w w' ∧ match res with
        | some (.error msg) => msg ≠ ""
        | _ => True) ∧
    (∀ {α : Type} (t : conc.TaskHandle α) (w : W), inv w →
      let (res, w') := (conc.waitTask t).run w
      inv w' ∧ frame w w' ∧ match res with
        | .error msg => msg ≠ ""
        | .ok _ => True) ∧
    (∀ {α : Type} (t : conc.TaskHandle α) (P : α → Prop),
      TaskPost t P →
      ∀ w, inv w →
        let (res, w') := (conc.pollTask t).run w
        inv w' ∧ frame w w' ∧ match res with
          | none => True
          | some (.ok a) => P a
          | some (.error msg) => msg ≠ "") ∧
    (∀ {α : Type} (t : conc.TaskHandle α) (P : α → Prop),
      TaskPost t P →
      ∀ w, inv w →
        let (res, w') := (conc.waitTask t).run w
        inv w' ∧ frame w w' ∧ match res with
          | .ok a => P a
          | .error msg => msg ≠ "") ∧
    (∀ {α : Type} (act : StateM W α) (QOk : W → α → W → Prop) (QErr : W → W → Prop),
      (∀ w, inv w → QErr w w) →
      (∀ w, inv w → let (a, w') := act.run w; inv w' ∧ QOk w a w' ∧ QErr w w') →
      ∀ w, inv w →
        let (res, w') := (conc.tryCatchMsg act).run w
        inv w' ∧ match res with
          | .ok a => QOk w a w'
          | .error msg => msg ≠ "" ∧ QErr w w')

/-- Compositional single-step refinement lifting a verified `RawOps` step contract,
    frame-preserving `ObeysConcFrame`, and persistent `ObeysStateCell` contract to a
    `[MonadFinally m]`-, `ConcOpsM m`-, and `StateCellM m`-polymorphic `mkApi`-built `PkgApi`. -/
def ObeysStepFromConcCell.{u₁, u₂}
    {RawS CellModelS PkgS : Type}
    {RawOps : (Type → Type) → Type u₁}
    {CellS : (Type → Type) → (Type → Type) → Type}
    {PkgApi : (Type → Type) → Type u₂}
    {RawReq RawOut PkgReq PkgOut : Type}
    (mapS : RawS → CellModelS → PkgS)
    (cellToModel : {Ref TaskH : Type → Type} → CellS Ref TaskH → CellModelS)
    (rawWf : RawS → Bool)
    (execRaw : {W : Type} → RawOps (StateM W) → RawReq → StateM W RawOut)
    (rawAllowed : RawS → RawReq → RawOut → RawS → Prop)
    (pkgWf : PkgS → Bool)
    (mkApi : {m : Type → Type} → [Monad m] → [MonadFinally m] →
      RawOps m → (conc : ConcOpsM m) → StateCellM m (CellS conc.Ref conc.TaskHandle) → PkgApi m)
    (execPkg : {W : Type} → PkgApi (StateM W) → PkgReq → StateM W PkgOut)
    (pkgAllowed : PkgS → PkgReq → PkgOut → PkgS → Prop) : Prop :=
  ∀ {W : Type} (projRaw : W → RawS) (raw : RawOps (StateM W)) (conc : ConcOpsM (StateM W))
      (projCell : W → CellS conc.Ref conc.TaskHandle)
      (cell : StateCellM (StateM W) (CellS conc.Ref conc.TaskHandle)),
    ObeysStep projRaw rawWf (execRaw raw) rawAllowed →
    (∀ w req, rawWf (projRaw w) = true → projCell ((execRaw raw req).run w).2 = projCell w) →
    ObeysConcFrame (fun w => rawWf (projRaw w) = true) (fun w₁ w₂ => projCell w₂ = projCell w₁) conc →
    ObeysStateCell projRaw projCell cell →
    ObeysStep (fun w => mapS (projRaw w) (cellToModel (projCell w))) pkgWf
      (execPkg (mkApi raw conc cell)) pkgAllowed

end Core
