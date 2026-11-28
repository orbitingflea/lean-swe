# Core Contract Review Guide (`Core/`)

`Core/` provides shared Layer 1 contract combinators and runtime capability primitives used across all packages.

## Must-Check Rules
- **Stay `O(1)` and package-independent:** reject any package name, per-package special case, or domain-specific type/logic in `Core/`.
- **Reusable combinators only:** restrict additions to small, generic contract or capability primitives (`Core.Obeys*`, `Core.NeverErrorKind*`, `Core.NondetTest`, `Core.ConcOpsM`, `Core.StateCellM`).
- **Trusted-root hygiene:** zero custom `axiom`s, zero external imports, zero `@[extern]`/`@[export]`/`@[implemented_by]`/`@[csimp]`, and no new `initialize` blocks outside the audited `Core.Assumptions` log refs.
- **Locked spec boundary:** pure appended declaration additions to an existing `Core/*.lean` file require `spec-add` (also satisfied by `spec-change`); new `Core/*.lean` files and any other edits, removals, or reorderings require `spec-change` (`scripts/check_spec_change.py`).
