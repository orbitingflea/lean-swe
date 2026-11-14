import Lake
open Lake DSL

package «lean-swe» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩,
    ⟨`weak.linter.missingDocs, true⟩,
    ⟨`weak.linter.unusedVariables, true⟩
  ]

require Regex from git "https://github.com/pandaman64/lean-regex.git" @ "v4.27.0" / "regex"

lean_lib Core where
  globs := #[.submodules `Core]

@[default_target]
lean_lib LeanSwe where
  globs := #[.andSubmodules `LeanSwe]

extern_lib «leanswe_fs» pkg := do
  let oFile := pkg.buildDir / "c" / "fs_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "Fs" / "Raw" / "c" / "fs_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_fs"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_process» pkg := do
  let oFile := pkg.buildDir / "c" / "process_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "Process" / "Raw" / "c" / "process_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_process"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_env» pkg := do
  let oFile := pkg.buildDir / "c" / "env_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "Env" / "Raw" / "c" / "env_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_env"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_uuid» pkg := do
  let oFile := pkg.buildDir / "c" / "uuid_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "Uuid" / "Raw" / "c" / "uuid_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_uuid"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

@[default_target, test_driver]
lean_exe «lean-swe-test» where
  root := `Tests.Main
