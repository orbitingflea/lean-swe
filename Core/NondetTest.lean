namespace Core

/-- Test-runner capability supporting `do`-notation alongside `nondet`, `assume`, and `assert`. -/
class NondetTest (runner : Type → Type) extends Monad runner where
  /-- Universally/existentially branch over values of type `α`. -/
  nondet (α : Type) : runner α
  /-- Restrict subsequent checks to paths where `P` holds. -/
  assume : Prop → runner Unit
  /-- Require `P` to hold at this point along surviving paths. -/
  assert : Prop → runner Unit

/-- Runner interpretation that universally checks every valid path satisfies every `assert`. -/
def AllPassRun (α : Type) : Type := (α → Prop) → Prop

instance : NondetTest AllPassRun where
  pure a := fun post => post a
  bind x f := fun post => x (fun a => f a post)
  nondet α := fun post => ∀ a : α, post a
  assume P := fun post => P → post ()
  assert P := fun post => P ∧ post ()

/-- Prop stating that every path satisfying all `assume` guards passes every `assert`. -/
def AllPass (prog : AllPassRun Unit) : Prop := prog (fun _ => True)

/-- Runner interpretation checking that at least one concrete run satisfies every `assume` and `assert`. -/
def CanReachRun (α : Type) : Type := (α → Prop) → Prop

instance : NondetTest CanReachRun where
  pure a := fun post => post a
  bind x f := fun post => x (fun a => f a post)
  nondet α := fun post => ∃ a : α, post a
  assume P := fun post => P ∧ post ()
  assert P := fun post => P ∧ post ()

/-- Prop stating that at least one concrete witness passes every `assume` and `assert`. -/
def CanReach (prog : CanReachRun Unit) : Prop := prog (fun _ => True)

end Core
