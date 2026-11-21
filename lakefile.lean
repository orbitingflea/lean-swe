import Lake
open Lake DSL

#eval (if System.Platform.isWindows || System.Platform.isOSX then
    Lean.throwError "LeanSwe requires Linux (x86_64 or aarch64)"
  else pure () : Lean.Elab.Command.CommandElabM Unit)

package «lean-swe» where
  moreLinkArgs := #["-Wl,-z,now", "-lcrypto", "-Wl,--exclude-libs,libcrypto.a", "-lpthread"]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩,
    ⟨`weak.linter.missingDocs, true⟩,
    ⟨`weak.linter.unusedVariables, true⟩
  ]

require «aeneas» from git
  "https://github.com/AeneasVerif/aeneas.git" @ "0d21a9ec7bbbb110110cacc14464a47fd71c8705" / "backends/lean"

@[default_target]
lean_lib Core where
  globs := #[.submodules `Core]

@[default_target]
lean_lib LeanSwe where
  globs := #[
    .one `LeanSwe,
    .submodules `LeanSwe.Base64,
    .submodules `LeanSwe.CmdLine,
    .submodules `LeanSwe.Compress,
    .submodules `LeanSwe.ConnectProxy,
    .submodules `LeanSwe.CryptoHash,
    .submodules `LeanSwe.EnvVars,
    .submodules `LeanSwe.Fs,
    .submodules `LeanSwe.Git,
    .submodules `LeanSwe.Glob,
    .submodules `LeanSwe.Json,
    .submodules `LeanSwe.LinuxSyscall,
    .submodules `LeanSwe.NumParse,
    .one `LeanSwe.PostFork.Types,
    .one `LeanSwe.PostFork.Model,
    .one `LeanSwe.PostFork.Interface,
    .one `LeanSwe.PostFork.Impl,
    .one `LeanSwe.PostFork.SpecTests,
    .one `LeanSwe.PostFork.SpecMutants,
    .one `LeanSwe.PostFork.RuntimeTests,
    .andSubmodules `LeanSwe.PostFork.Proofs,
    .one `LeanSwe.PostFork.Verified,
    .one `LeanSwe.PostFork.Aeneas.Model,
    .one `LeanSwe.PostFork.Aeneas.Api,
    .one `LeanSwe.PostFork.Aeneas.Bridge,
    .submodules `LeanSwe.Process,
    .submodules `LeanSwe.ProcessSandbox,
    .submodules `LeanSwe.RegExp,
    .submodules `LeanSwe.SlotPool,
    .submodules `LeanSwe.Sqlite,
    .submodules `LeanSwe.Tar,
    .submodules `LeanSwe.TempDir,
    .submodules `LeanSwe.Time,
    .submodules `LeanSwe.Toml,
    .submodules `LeanSwe.Uuid
  ]

@[default_target]
lean_lib «LeanSwe.PostFork.AeneasGen» where
  roots := #[
    `LeanSwe.PostFork.Aeneas.TypesExternal,
    `LeanSwe.PostFork.Aeneas.Types,
    `LeanSwe.PostFork.Aeneas.FunsExternal,
    `LeanSwe.PostFork.Aeneas.Funs
  ]
  globs := #[
    .one `LeanSwe.PostFork.Aeneas.TypesExternal,
    .one `LeanSwe.PostFork.Aeneas.Types,
    .one `LeanSwe.PostFork.Aeneas.FunsExternal,
    .one `LeanSwe.PostFork.Aeneas.Funs
  ]
  leanOptions := #[⟨`weak.linter.missingDocs, false⟩]

@[default_target]
lean_lib Fuzz where
  globs := #[.submodules `Fuzz]

private def buildFdBoxObj (pkg : NPackage __name__) (tag : String) : FetchM (Job System.FilePath) := do
  let cDir := pkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (cDir / "fd_box.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / s!"linux_fd_box_{tag}.o"
  buildO oFile (deps.map fun _ => cDir / "fd_box.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]

extern_lib «leanswe_fs» pkg := do
  let oFile := pkg.buildDir / "c" / "fs_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "Fs" / "Raw" / "c" / "fs_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_fs"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_process» pkg := do
  let oFile := pkg.buildDir / "c" / "process_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "Process" / "Raw" / "c" / "process_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_process"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_envvars» pkg := do
  let oFile := pkg.buildDir / "c" / "envvars_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "EnvVars" / "Raw" / "c" / "envvars_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_envvars"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_envvars_fuzz» pkg := do
  let oFile := pkg.buildDir / "c" / "envvars_fuzz_env.o"
  let srcJob ← inputTextFile (pkg.dir / "Fuzz" / "EnvVars" / "c" / "envvars_fuzz_env.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_envvars_fuzz"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_sqlite» pkg := do
  let lean ← getLeanInstall
  let cDir := pkg.dir / "LeanSwe" / "Sqlite" / "Raw" / "c"
  let sqliteO := pkg.buildDir / "c" / "sqlite3.o"
  let sqliteSrc ← inputTextFile (cDir / "sqlite3.c")
  let sqliteOJob ← buildO sqliteO sqliteSrc
    #["-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-DSQLITE_THREADSAFE=1", "-DSQLITE_OMIT_LOAD_EXTENSION=1", "-DSQLITE_DISABLE_LFS"]
  let shimO := pkg.buildDir / "c" / "sqlite_shim.o"
  let shimSrc ← inputTextFile (cDir / "sqlite_shim.c")
  let shimOJob ← buildO shimO shimSrc
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_sqlite"
  buildStaticLib (pkg.staticLibDir / name) #[sqliteOJob, shimOJob]

extern_lib «leanswe_cryptohash» pkg := do
  let oFile := pkg.buildDir / "c" / "cryptohash_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "CryptoHash" / "Raw" / "c" / "cryptohash_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-pthread", "-Wall", "-Wextra", "-Werror"]
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
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_psandbox"
  buildStaticLib (pkg.staticLibDir / name) #[shimOJob]

extern_lib «leanswe_connectproxy» pkg := do
  let oFile := pkg.buildDir / "c" / "cproxy_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "ConnectProxy" / "Raw" / "c" / "cproxy_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_connectproxy"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_linux_process_fuzz_env» pkg := do
  let cDir := pkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let fDir := pkg.dir / "Fuzz" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (fDir / "process_fuzz_env.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / "linux_process_fuzz_env.o"
  let oJob ← buildO oFile (deps.map fun _ => fDir / "process_fuzz_env.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let fdBoxJob ← buildFdBoxObj pkg "proc_fuzz"
  let name := nameToStaticLib "leanswe_linux_process_fuzz_env"
  buildStaticLib (pkg.staticLibDir / name) #[oJob, fdBoxJob]

extern_lib «leanswe_linux_process» pkg := do
  let cDir := pkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (cDir / "process_shim.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / "linux_process_shim.o"
  let oJob ← buildO oFile (deps.map fun _ => cDir / "process_shim.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let fdBoxJob ← buildFdBoxObj pkg "proc"
  let name := nameToStaticLib "leanswe_linux_process"
  buildStaticLib (pkg.staticLibDir / name) #[oJob, fdBoxJob]

extern_lib «leanswe_sandbox_fuzz_env» pkg := do
  let cDir := pkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let fDir := pkg.dir / "Fuzz" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (fDir / "sandbox_fuzz_env.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / "linux_sandbox_fuzz_env.o"
  let oJob ← buildO oFile (deps.map fun _ => fDir / "sandbox_fuzz_env.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let fdBoxJob ← buildFdBoxObj pkg "sbx_fuzz"
  let name := nameToStaticLib "leanswe_sandbox_fuzz_env"
  buildStaticLib (pkg.staticLibDir / name) #[oJob, fdBoxJob]

extern_lib «leanswe_linux_files» pkg := do
  let cDir := pkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (cDir / "files_shim.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / "linux_files_shim.o"
  let oJob ← buildO oFile (deps.map fun _ => cDir / "files_shim.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let fdBoxJob ← buildFdBoxObj pkg "files"
  let name := nameToStaticLib "leanswe_linux_files"
  buildStaticLib (pkg.staticLibDir / name) #[oJob, fdBoxJob]

extern_lib «leanswe_fuzz_env» pkg := do
  let cDir := pkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let fDir := pkg.dir / "Fuzz" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (fDir / "fuzz_env.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / "linux_fuzz_env.o"
  let oJob ← buildO oFile (deps.map fun _ => fDir / "fuzz_env.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let name := nameToStaticLib "leanswe_fuzz_env"
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
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let fdBoxJob ← buildFdBoxObj pkg "sbx"
  let name := nameToStaticLib "leanswe_linux_sandbox"
  buildStaticLib (pkg.staticLibDir / name) #[oJob, fdBoxJob]

extern_lib «leanswe_linux_timerand» pkg := do
  let oFile := pkg.buildDir / "c" / "timerand_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "LinuxSyscall" / "c" / "timerand_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_linux_timerand"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_linux_dns» pkg := do
  let oFile := pkg.buildDir / "c" / "dns_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "LinuxSyscall" / "c" / "dns_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_linux_dns"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_linux_timerand_fuzz» pkg := do
  let oFile := pkg.buildDir / "c" / "timerand_fuzz_sig.o"
  let srcJob ← inputTextFile (pkg.dir / "Fuzz" / "LinuxSyscall" / "c" / "timerand_fuzz_sig.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let name := nameToStaticLib "leanswe_linux_timerand_fuzz"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_linux_passwd» pkg := do
  let oFile := pkg.buildDir / "c" / "passwd_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "LinuxSyscall" / "c" / "passwd_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-isystem", lean.includeDir.toString]
    #["-O2", "-fPIC", "-DNDEBUG", "-DLEAN_EXPORTING", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-Wshadow", "-Wconversion"]
  let name := nameToStaticLib "leanswe_linux_passwd"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_float_fuzz_oracle» pkg := do
  let oFile := pkg.buildDir / "c" / "float_fuzz_oracle.o"
  let srcJob ← inputTextFile (pkg.dir / "Fuzz" / "Float" / "c" / "float_oracle.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-fno-fast-math", "-ffp-contract=off", "-fno-builtin-snprintf"]
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

extern_lib «leanswe_linux_poll» pkg := do
  let cDir := pkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (cDir / "poll_shim.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / "linux_poll_shim.o"
  let oJob ← buildO oFile (deps.map fun _ => cDir / "poll_shim.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let fdBoxJob ← buildFdBoxObj pkg "poll"
  let name := nameToStaticLib "leanswe_linux_poll"
  buildStaticLib (pkg.staticLibDir / name) #[oJob, fdBoxJob]

extern_lib «leanswe_poll_fuzz_env» pkg := do
  let cDir := pkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let fDir := pkg.dir / "Fuzz" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (fDir / "poll_fuzz_env.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / "linux_poll_fuzz_env.o"
  let oJob ← buildO oFile (deps.map fun _ => fDir / "poll_fuzz_env.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let fdBoxJob ← buildFdBoxObj pkg "poll_fuzz"
  let name := nameToStaticLib "leanswe_poll_fuzz_env"
  buildStaticLib (pkg.staticLibDir / name) #[oJob, fdBoxJob]

extern_lib «leanswe_linux_net» pkg := do
  let cDir := pkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (cDir / "net_shim.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / "linux_net_shim.o"
  let oJob ← buildO oFile (deps.map fun _ => cDir / "net_shim.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let fdBoxJob ← buildFdBoxObj pkg "net"
  let name := nameToStaticLib "leanswe_linux_net"
  buildStaticLib (pkg.staticLibDir / name) #[oJob, fdBoxJob]

extern_lib «leanswe_net_fuzz_env» pkg := do
  let cDir := pkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let fDir := pkg.dir / "Fuzz" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (fDir / "net_fuzz_env.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / "linux_net_fuzz_env.o"
  let oJob ← buildO oFile (deps.map fun _ => fDir / "net_fuzz_env.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let fdBoxJob ← buildFdBoxObj pkg "net_fuzz"
  let name := nameToStaticLib "leanswe_net_fuzz_env"
  buildStaticLib (pkg.staticLibDir / name) #[oJob, fdBoxJob]

extern_lib «leanswe_linux_fd_box» pkg := do
  let cDir := pkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (cDir / "fd_box.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / "linux_fd_box.o"
  let oJob ← buildO oFile (deps.map fun _ => cDir / "fd_box.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let name := nameToStaticLib "leanswe_linux_fd_box"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

/-- Build `#![no_std]` `libleanswe_postfork_rust.a` with localized internal symbols. -/
target «postfork_rust_archive» pkg : System.FilePath := do
  let rustDir := pkg.dir / "LeanSwe" / "PostFork" / "rust"
  let targetDir := pkg.buildDir / "postfork-rust"
  let outLib := pkg.staticLibDir / nameToStaticLib "leanswe_postfork_rust"
  let manifestJob ← inputTextFile (rustDir / "Cargo.toml")
  let lockJob ← inputTextFile (rustDir / "Cargo.lock")
  let toolchainJob ← inputTextFile (rustDir / "rust-toolchain.toml")
  let srcLib ← inputTextFile (rustDir / "src" / "lib.rs")
  let srcSys ← inputTextFile (rustDir / "src" / "sys.rs")
  let srcFd ← inputTextFile (rustDir / "src" / "fd_ops.rs")
  let srcChild ← inputTextFile (rustDir / "src" / "child.rs")
  let srcFfi ← inputTextFile (rustDir / "src" / "ffi.rs")
  let depsJob := Job.collectArray #[manifestJob, lockJob, toolchainJob, srcLib, srcSys, srcFd, srcChild, srcFfi]
  buildFileAfterDep outLib depsJob fun _ => do
    createParentDirs outLib
    IO.FS.createDirAll targetDir
    let absRustDir ← IO.FS.realPath rustDir
    let absTargetDir ← IO.FS.realPath targetDir
    let homeDir := (← IO.getEnv "HOME").getD ""
    let aeneasToolchain := s!"{homeDir}/.local/share/aeneas-toolchain"
    let fallbackCargo : System.FilePath := s!"{aeneasToolchain}/cargo/bin/cargo"
    let findCargoOnPath : IO (Option String) := do
      let pathEnv := (← IO.getEnv "PATH").getD ""
      for dir in pathEnv.splitOn ":" do
        if !dir.isEmpty then
          let cand : System.FilePath := System.FilePath.mk dir / "cargo"
          if ← cand.pathExists then
            return some cand.toString
      return none
    let cargoBin ← do
      match (← IO.getEnv "CARGO").filter (!·.isEmpty) with
      | some c => pure c
      | none =>
        match (← findCargoOnPath) with
        | some c => pure c
        | none =>
          if !homeDir.isEmpty && (← fallbackCargo.pathExists) then
            pure fallbackCargo.toString
          else
            pure "cargo"
    let aeneasPath : System.FilePath := aeneasToolchain
    let absAeneas? ←
      if !homeDir.isEmpty && (← aeneasPath.pathExists) then
        pure (some (← IO.FS.realPath aeneasPath))
      else
        pure none
    let cargoPath : System.FilePath := cargoBin
    let absCargo? ←
      if (← cargoPath.pathExists) then
        pure (some (← IO.FS.realPath cargoPath))
      else
        pure none
    let useAeneas := match absAeneas?, absCargo? with
      | some ad, some cb => cb.toString.startsWith (ad.toString ++ "/")
      | _, _ => false
    let baseEnv : Array (String × Option String) := #[
      ("RUSTUP_TOOLCHAIN", none),
      ("CARGO_BUILD_TARGET", none),
      ("RUSTFLAGS", some "-C opt-level=3")
    ]
    let extraEnv := match useAeneas, absAeneas? with
      | true, some ad => baseEnv ++ #[("CARGO_HOME", some s!"{ad}/cargo"), ("RUSTUP_HOME", some s!"{ad}/rustup")]
      | _, _ => baseEnv
    proc {
      cmd := cargoBin
      args := #["build", "--locked", "--target-dir", absTargetDir.toString, "--release", "--features", "standalone"]
      cwd := some absRustDir
      env := extraEnv
    }
    let builtRlib := absTargetDir / "release" / "libpostfork.rlib"
    let objDir := absTargetDir / "obj-extract"
    proc {
      cmd := "sh"
      args := #[
        "-eu", "-c",
        "rm -rf \"$1\" \"$2\"; mkdir -p \"$1\"; (cd \"$1\" && ar x \"$3\"); for o in \"$1\"/*.rcgu.o; do \"${OBJCOPY:-objcopy}\" --keep-global-symbol=leanswe_postfork_run_child --keep-global-symbol=leanswe_postfork_close_fds_above2_except \"$o\"; done; ar rcs \"$2\" \"$1\"/*.rcgu.o",
        "_", objDir.toString, outLib.toString, builtRlib.toString
      ]
    }

/-- Emit a relocatable Rust object with weak `leanswe_postfork_*` definitions so standalone `extern_lib` `.so`s resolve under `LD_BIND_NOW=1` while `gcc -fuse-ld=bfd` static archive linking avoids duplicate symbols. -/
target «postfork_rust_weak_o» pkg : System.FilePath := do
  let archiveJob ← postfork_rust_archive.fetch
  let weakObj := pkg.buildDir / "c" / "postfork_rust_weak.o"
  let weakDir := pkg.buildDir / "postfork-rust" / "obj-weak"
  buildFileAfterDep weakObj archiveJob fun archivePath => do
    createParentDirs weakObj
    proc {
      cmd := "sh"
      args := #[
        "-eu", "-c",
        "wdir=\"$1\"; out=\"$2\"; arc=\"$3\"; rm -rf \"$wdir\" \"$out\"; mkdir -p \"$wdir\"; (cd \"$wdir\" && ar x \"$arc\"); set -- \"$wdir\"/*.rcgu.o; if [ \"$#\" -eq 1 ]; then cp \"$1\" \"$out\"; else \"${LD:-ld}\" -r -o \"$out\" \"$@\"; fi; \"${OBJCOPY:-objcopy}\" --weaken-symbol=leanswe_postfork_run_child --weaken-symbol=leanswe_postfork_close_fds_above2_except \"$out\"",
        "_", weakDir.toString, weakObj.toString, archivePath.toString
      ]
    }

extern_lib «leanswe_postfork» pkg := do
  let oFile := pkg.buildDir / "c" / "postfork_shim.o"
  let cDir := pkg.dir / "LeanSwe" / "PostFork" / "c"
  let srcJob ← inputTextFile (cDir / "postfork_shim.c")
  let hdrJob ← inputTextFile (cDir / "postfork.h")
  let fdBoxHdrJob ← inputTextFile (pkg.dir / "LeanSwe" / "LinuxSyscall" / "c" / "fd_box.h")
  let depsJob := Job.collectArray #[srcJob, hdrJob, fdBoxHdrJob]
  let lean ← getLeanInstall
  let oJob ← buildO oFile (depsJob.map fun _ => cDir / "postfork_shim.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let weakRustJob ← postfork_rust_weak_o.fetch
  let fdBoxJob ← buildFdBoxObj pkg "postfork"
  let name := nameToStaticLib "leanswe_postfork"
  buildStaticLib (pkg.staticLibDir / name) #[oJob, weakRustJob, fdBoxJob]

extern_lib «leanswe_postfork_fuzz» pkg := do
  let oFile := pkg.buildDir / "c" / "postfork_fuzz.o"
  let fuzzCDir := pkg.dir / "Fuzz" / "PostFork" / "c"
  let postforkCDir := pkg.dir / "LeanSwe" / "PostFork" / "c"
  let srcJob ← inputTextFile (fuzzCDir / "postfork_fuzz.c")
  let hdrJob ← inputTextFile (postforkCDir / "postfork.h")
  let fdBoxHdrJob ← inputTextFile (pkg.dir / "LeanSwe" / "LinuxSyscall" / "c" / "fd_box.h")
  let probeSrc := fuzzCDir / "postfork_probe.c"
  let probeSrcJob ← inputTextFile probeSrc
  let probeExe := pkg.binDir / "leanswe-postfork-probe"
  let probeJob ← buildFileAfterDep probeExe probeSrcJob fun src => do
    createParentDirs probeExe
    let cc := ((← IO.getEnv "CC").filter (!·.isEmpty)).getD "cc"
    proc {
      cmd := cc
      args := #["-static", "-O2", "-Wall", "-Wextra", "-Werror", "-o", probeExe.toString, src.toString]
    }
  let depsJob := Job.collectArray #[srcJob, hdrJob, fdBoxHdrJob, probeJob]
  let lean ← getLeanInstall
  let oJob ← buildO oFile (depsJob.map fun _ => fuzzCDir / "postfork_fuzz.c")
    #["-I", lean.includeDir.toString, "-I", postforkCDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let weakRustJob ← postfork_rust_weak_o.fetch
  let fdBoxJob ← buildFdBoxObj pkg "postfork_fuzz"
  let name := nameToStaticLib "leanswe_postfork_fuzz"
  buildStaticLib (pkg.staticLibDir / name) #[oJob, weakRustJob, fdBoxJob]

extern_lib «leanswe_postfork_rust» := do
  postfork_rust_archive.fetch

@[default_target, test_driver]
lean_exe «lean-swe-test» where
  root := `Tests.Main

lean_exe «lean-swe-mut-test» where
  root := `Tests.MutateDriver

@[default_target]
lean_exe «leanswe-fuzz» where
  root := `Fuzz.Main
