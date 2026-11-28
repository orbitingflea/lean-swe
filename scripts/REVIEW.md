# Audit & Tooling Review Guide (`scripts/`)

`scripts/` enforces repository-wide import hygiene, promise/contract audits, FFI thinness, and spec-lock gates.

## Must-Check Rules
- **Stay `O(1)` and package-independent:** never hardcode package names, special-case branches, or per-package allowlists inside checker logic.
- **Data-driven metadata only:** keep per-package declarations strictly in data files (`scripts/package_manifest.json`, `scripts/external_assumptions.json`, `harness/Fuzz/suites.json`).
- **Fail closed everywhere:** reject empty allowlists, silent skips, fallback exemptions, or ratchet loopholes. Parse errors, malformed headers, missing `.olean`/`.ilean` files, and unknown manifest entries must exit non-zero.
- **Regression self-tests required:** every new or tightened check must include both positive and negative synthetic regression tests (`CheckImports.lean --self-test`, `CheckPromisesTest.lean` / `CheckPromisesDagTest.lean`, `CheckAssumptionsTest.lean`, `scripts/test_*.py`).
- **Clean execution:** Lean scripts must run cleanly under `lean -DwarningAsError=true --run`, remove temporary `/tmp/*` directories in `finally` blocks, and avoid committing `scripts/__pycache__/`.
