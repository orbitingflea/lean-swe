# lean-swe

Monorepo of everyday software engineering packages in Lean 4, combining plain Lean implementations, external C++ and Python wrappers, and machine-checked `NondetTest` specifications.

## Module Layout

Each package lives under `LeanSwe/<Package>/` in a six-part layout:

- `Types.lean`: public data types, typed error enums, and API records with zero upstream imports.
- `Interface.lean`: public entry point importing `Types` and `Impl` and exporting clean top-level functions.
- `Impl.lean` (or `Impl/`): plain executable Lean code inside `Internal` implementing the package against dependencies.
- `SpecTests.lean` (or `SpecTests/`): human-audited `NondetTest` contracts (`AllPass` and `CanReach`) importing only `Core` and `Types`.
- `Proofs.lean` (or `Proofs/`): machine-checked proofs discharging `SpecTests`.
- `RuntimeTests.lean` (or `RuntimeTests/`): concrete and differential runtime tests grounding wrappers.

## Build

```bash
lake build
lake test
```
