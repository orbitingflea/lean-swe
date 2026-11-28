# Layer 2 Review Guide (`proofs/`)

`proofs/LeanSweProofs/` holds specifications (`Model`, `Properties`, `SpecTests`, `SpecMutants`) and machine-checked proofs (`Proofs`).

## Must-Check Rules
- **Plain-English summary first:** require a brief plain-English summary of abstract state and transition rules at the top of `Model.lean` (or the PR description) before Lean code.
- **Keep stateful OS contracts small and relational:** follow the canonical stateful contract shape in `Uuid/Model.lean` (~40 L stateful contract section) and `Time/Model.lean` (~60 L `TimeOps` clock contract section) — concise abstract state, `pkgWf`, request/output sums, `execPkgStep`, and relational `allowedPkgStep` fuzz-tested against the real OS.
- **Never duplicate pure Lean implementations inside `Model.lean`:** do not mirror pure formatting, parsing, or helper code in `Model.lean`. Verify pure functions directly with `Properties.lean` theorems and `harness/UnitTests/` I/O tests (rely on human/AI review alone for pure UI/text layout such as `renderHelp`).
- **No toy simulators or optimizations in `Model.lean`:** reject toy SQL/Git/VFS engines, caching, or performance tricks inside `Model`. Models specify observable contracts only.
- **Drop fatal/impossible OS error branches:** omit unrecoverable OS failures rather than modeling them.
- **Never pin exact English error strings:** assert error `kind` and non-empty message (`!err.message.isEmpty`), never literal English phrasing.
- **Strict cross-package proof reuse:** a `Proofs` module may import only a declared **direct** dependency's top-level `LeanSweProofs.<Dep>.Proofs` or `LeanSweProofs.<Dep>.Properties` to reuse public `theorem`s. Reject cross-package `Impl`/`SysBridge`/`.Internal.` reach-ins, non-proof helper `def` reuse, transitive/undeclared deps, or proof constants in `obeys_model`/`AllPass`/`CanReach` signatures.
- **Model LOC check:** manually compare `Model` LOC against the upfront estimate in the PR/task (no CI line-cap rules).
