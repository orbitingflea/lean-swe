# CI Workflows Review Guide (`.github/`)

`.github/` defines the fast PR gate (`audit.yml`), daily deep gate (`audit-daily.yml`), and pinned Lean installer action.

## Must-Check Rules
- **Stay `O(1)` and package-independent:** drive suite discovery and checks from `leanswe-fuzz --list-suites`, `harness/Fuzz/suites.json`, and `scripts/package_manifest.json`. Reject per-package hardcoded sprawl unless an OS runner privilege setup strictly demands it (e.g., overlayfs/namespace/strace setup for kernel suites).
- **Zero external toolchain steps:** reject Rust, Cargo, Charon, Aeneas, or external Lean dependency steps; keep CI pure Lean 4 + local C shims.
- **Preserve fail-closed security and audit gates:** keep ELF `BIND_NOW` enforcement on `leanswe-fuzz`, the `libleanswe_postfork.a` symbol export diff, `scripts/check_spec_change.py`, `CheckImports.lean` (`--self-test` + repo check), and all parallel post-build audit lanes (`CheckAssumptionsTest`, `CheckPromises --with-self-test`, `CheckAssumptions`, `CheckForeignThinness`).
- **Minimal privileges and pinned actions:** pin third-party actions to full commit SHAs and keep workflow `permissions` minimal (`contents: read` on PR gates).
