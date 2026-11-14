# lean-swe

Monorepo of everyday software engineering packages in Lean 4, combining plain Lean implementations, external C++ and Python wrappers, and machine-checked `NondetTest` specifications.

## Module Layout

Each package lives in its own folder under a uniform five-part layout:

- `Interface.lean`: public data types, typed error enums, and the exported module interface.
- `Impl.lean` (or `Impl/`): plain executable Lean code implementing the interface.
- `SpecTests.lean` (or `SpecTests/`): human-audited `NondetTest` contracts (`AllPass` and `CanReach`).
- `Proofs.lean` (or `Proofs/`): machine-checked proofs discharging `SpecTests` over `EmpiricalAssumptions`.
- `RuntimeTests.lean` (or `RuntimeTests/`): concrete and differential runtime tests grounding external wrappers.

## Build

```bash
lake build
```
