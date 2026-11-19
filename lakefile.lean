import Lake
open Lake DSL

#eval (if System.Platform.isWindows || System.Platform.isOSX then
    Lean.throwError "LeanSwe requires Linux (x86_64 or aarch64)"
  else pure () : Lean.Elab.Command.CommandElabM Unit)

package «lean-swe» where
  moreLinkArgs := #["-lcrypto", "-lpthread"]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩,
    ⟨`weak.linter.missingDocs, true⟩,
    ⟨`weak.linter.unusedVariables, true⟩
  ]

@[default_target]
lean_lib Core where
  globs := #[.submodules `Core]

@[default_target]
lean_lib LeanSwe where
  globs := #[.andSubmodules `LeanSwe]

@[default_target]
lean_lib Fuzz where
  globs := #[.submodules `Fuzz]

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

extern_lib «leanswe_psandbox» pkg := do
  let lean ← getLeanInstall
  let cDir := pkg.dir / "LeanSwe" / "ProcessSandbox" / "Raw" / "c"
  let outDir := pkg.buildDir / "c"
  let initSrcJob ← inputTextFile (cDir / "psandbox_init.c")
  let initBin := outDir / "leanswe-psandbox-init"
  let initBinJob ← buildFileAfterDep initBin initSrcJob fun srcFile => do
    createParentDirs initBin
    proc {
      cmd := "cc"
      args := #["-O2", "-Wall", "-Wextra", "-Werror", srcFile.toString, "-o", initBin.toString]
    }
  let embedH := outDir / "psandbox_init_embed.h"
  let embedHJob ← buildFileAfterDep embedH initBinJob fun binFile => do
    let bytes ← IO.FS.readBinFile binFile
    createParentDirs embedH
    let h ← IO.FS.Handle.mk embedH .write
    h.putStr "static const unsigned char g_psandbox_init_elf[] = {\n"
    let mut i : Nat := 0
    while i < bytes.size do
      if i % 16 == 0 then
        h.putStr "  "
      h.putStr s!"{bytes[i]!.toNat},"
      if i % 16 == 15 || i + 1 == bytes.size then
        h.putStr "\n"
      else
        h.putStr " "
      i := i + 1
    h.putStr "};\n"
    h.putStr s!"static const size_t g_psandbox_init_elf_len = {bytes.size}u;\n"
    h.flush
  let shimSrcJob ← inputTextFile (cDir / "psandbox_shim.c")
  let shimDeps := Job.collectArray #[shimSrcJob, embedHJob]
  let shimO := outDir / "psandbox_shim.o"
  let shimOJob ← buildO shimO (shimDeps.map fun _ => cDir / "psandbox_shim.c")
    #["-I", lean.includeDir.toString, "-I", outDir.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_psandbox"
  buildStaticLib (pkg.staticLibDir / name) #[shimOJob]

extern_lib «leanswe_connectproxy» pkg := do
  let oFile := pkg.buildDir / "c" / "cproxy_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "ConnectProxy" / "Raw" / "c" / "cproxy_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_connectproxy"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_linux_sandbox» pkg := do
  let cDir := pkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (cDir / "sandbox_shim.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / "linux_sandbox_shim.o"
  let oJob ← buildO oFile (deps.map fun _ => cDir / "sandbox_shim.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let name := nameToStaticLib "leanswe_linux_sandbox"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_sandbox_fuzz_env» pkg := do
  let cDir := pkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (cDir / "sandbox_fuzz_env.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / "linux_sandbox_fuzz_env.o"
  let oJob ← buildO oFile (deps.map fun _ => cDir / "sandbox_fuzz_env.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let name := nameToStaticLib "leanswe_sandbox_fuzz_env"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_linux_timerand» pkg := do
  let oFile := pkg.buildDir / "c" / "timerand_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "LinuxSyscall" / "c" / "timerand_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_linux_timerand"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_linux_timerand_fuzz» pkg := do
  let oFile := pkg.buildDir / "c" / "timerand_fuzz_sig.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "LinuxSyscall" / "c" / "timerand_fuzz_sig.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let name := nameToStaticLib "leanswe_linux_timerand_fuzz"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_float_fuzz_oracle» pkg := do
  let oFile := pkg.buildDir / "c" / "float_fuzz_oracle.o"
  let srcJob ← inputTextFile (pkg.dir / "Fuzz" / "Float" / "c" / "float_oracle.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra", "-Werror", "-fno-fast-math", "-ffp-contract=off", "-fno-builtin-snprintf", "-DNDEBUG"]
  let name := nameToStaticLib "leanswe_float_fuzz_oracle"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_cmdline_fuzz» pkg := do
  let oFile := pkg.buildDir / "c" / "cmdline_fuzz_env.o"
  let srcJob ← inputTextFile (pkg.dir / "Fuzz" / "CmdLine" / "c" / "cmdline_fuzz_env.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_cmdline_fuzz"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

@[default_target, test_driver]
lean_exe «lean-swe-test» where
  root := `Tests.Main

lean_exe «lean-swe-mut-test» where
  root := `Tests.MutateDriver

lean_exe «leanswe-world-fuzz» where
  root := `Tests.WorldFuzzMain

@[default_target]
lean_exe «leanswe-fuzz» where
  root := `Fuzz.Main
