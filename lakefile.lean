import Lake
open Lake DSL

package «lean-swe» where
  moreLinkArgs := #["-lcrypto"]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩,
    ⟨`weak.linter.missingDocs, true⟩,
    ⟨`weak.linter.unusedVariables, true⟩
  ]

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

extern_lib «leanswe_envvars» pkg := do
  let oFile := pkg.buildDir / "c" / "envvars_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "EnvVars" / "Raw" / "c" / "envvars_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_envvars"
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

extern_lib «leanswe_sqlite» pkg := do
  let lean ← getLeanInstall
  let cDir := pkg.dir / "LeanSwe" / "Sqlite" / "Raw" / "c"
  let sqliteO := pkg.buildDir / "c" / "sqlite3.o"
  let sqliteSrc ← inputTextFile (cDir / "sqlite3.c")
  let sqliteOJob ← buildO sqliteO sqliteSrc
    #["-I", cDir.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra", "-Werror", "-DSQLITE_THREADSAFE=1", "-DSQLITE_OMIT_LOAD_EXTENSION=1", "-DSQLITE_DISABLE_LFS"]
  let shimO := pkg.buildDir / "c" / "sqlite_shim.o"
  let shimSrc ← inputTextFile (cDir / "sqlite_shim.c")
  let shimOJob ← buildO shimO shimSrc
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_sqlite"
  buildStaticLib (pkg.staticLibDir / name) #[sqliteOJob, shimOJob]

extern_lib «leanswe_cryptohash» pkg := do
  let oFile := pkg.buildDir / "c" / "cryptohash_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "CryptoHash" / "Raw" / "c" / "cryptohash_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_cryptohash"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

@[default_target, test_driver]
lean_exe «lean-swe-test» where
  root := `Tests.Main
