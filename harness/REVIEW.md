# Layer 3 Review Guide (`harness/`)

`harness/` holds real-OS differential fuzzers (`Fuzz/`), ordinary unit tests (`UnitTests/`), and broken-implementation mutants (`ModelMutants/`).

## Must-Check Rules
- **Real OS/library fuzzing only:** reject any **new** mocked error probes in `harness/Fuzz/`. Fuzzers must exercise real OS syscalls and real library behavior against the package's `Model`.
- **Retire legacy mocked error probes:** when a package drops fatal/impossible OS error branches, delete its corresponding legacy mocked error probes rather than keeping dead scaffolding.
- **Ordinary unit tests for pure logic:** put deterministic input-output tests for pure functions, codecs, and concrete edge cases in `harness/UnitTests/`.
- **Trivial, effective `ModelMutants`:** each mutant in `harness/ModelMutants/` should be a small, obviously broken variant that actually fails the model or properties.
- **Keep test helpers inside `harness/`:** test-only C and Lean helpers must stay strictly inside `harness/` (never leak into `LeanSwe/`), use zero `@[export]` attributes, and satisfy `CheckForeignThinness` limits.
- **Layer 3 import discipline:** never import the `LeanSweProofs` umbrella or `SpecTests`/`SpecMutants`/`Proofs`/`Verified`/`SysBridge`. `UnitTests` and `ModelMutants` must never import `Impl`; a `Fuzz/<Suite>` module may import only its own matching package's top-level `<Pkg>.Impl`.
