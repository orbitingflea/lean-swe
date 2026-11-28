# Layer 1 Review Guide (`LeanSwe/`)

`LeanSwe/` contains pure, runnable production library code only (`Types`, `Interface`, `Impl`, `SysBridge`, and thin C shims in `c/`).

## Must-Check Rules
- **Zero proofs in Layer 1:**
  - `Types*.lean`, `Interface*.lean`, and all other non-`Impl`/`SysBridge` Layer 1 modules (including `LeanSwe.lean` and package umbrellas): forbid all user-written `theorem`/`lemma` declarations (public or `private`). Put bridge and contract theorems in `proofs/LeanSweProofs/<Pkg>/Proofs.lean` or `Properties.lean`.
  - `Impl*.lean` and `SysBridge*.lean`: forbid all public `theorem`/`lemma` declarations. `private` proof helpers are allowed **only** when referenced (directly or transitively via same-file `private` theorems) by a non-`Prop` runtime `def` in the same module (e.g., `termination_by`/`decreasing_by` or subtype validity witnesses).
- **No spec helpers disguised as `def`:** do not place proof-only predicates, ghost state, or verification helpers in `LeanSwe/` as `def`s.
- **Zero mocks or test-only helpers:** reject `FakeClock`, `.mock` handles, `Mock*State`, or test hooks in production modules. Test doubles and test utilities belong strictly under `harness/`.
- **Zero external Lean dependencies:** allowed import roots are `Init`, `Std`, `Lean`, `Core`, and `LeanSwe`. Never import `LeanSweProofs` or Layer 2 roles (`Model`, `Proofs`, `Properties`, `SpecTests`, `SpecMutants`).
- **Thin FFI boundary:** `@[extern]` declarations are permitted only when `external_boundary = true` in `scripts/package_manifest.json`, must be `private opaque` in `<Pkg>.Interface` with `leanswe_*` C symbols, and must keep C shims `CheckForeignThinness`-compliant.
- **Executable LOC check:** manually compare executable LOC against the upfront estimate in the PR/task (no CI line-cap rules).
