# lean-swe

Monorepo of everyday software engineering packages in Lean 4, combining plain Lean implementations, external C++ and Python wrappers, and machine-checked `NondetTest` specifications.

## Module Layout

Each package lives under `LeanSwe/<Package>/` in a five-part layout:

- `Types.lean`: public data types, typed error enums, and API records with zero upstream imports.
- `Interface.lean`: public entry point importing `Types` and `Impl` and exporting clean top-level functions.
- `Impl.lean` (or `Impl/`): plain executable Lean code inside `Internal` implementing the package against dependencies.
- `SpecTests.lean` (or `SpecTests/`): `NondetTest` contracts (`AllPass` and `CanReach`) importing only `Core` and `Types`.
- `Proofs.lean` (or `Proofs/`): machine-checked proofs discharging `SpecTests`.

## Build

```bash
lake build
lake -d harness build
harness/.lake/build/bin/leanswe-fuzz --smoke
```

## License

`lean-swe` is released under the Apache License 2.0. See [LICENSE](LICENSE) for the full license text. The bundled SQLite amalgamation in `LeanSwe/Sqlite/Raw/c/sqlite3.c` and `LeanSwe/Sqlite/Raw/c/sqlite3.h` is in the public domain, and both files disclaim copyright.
