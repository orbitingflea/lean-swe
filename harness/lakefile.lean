import Lake
open Lake DSL

#eval (if System.Platform.isWindows || System.Platform.isOSX then
    Lean.throwError "LeanSwe harness requires Linux (x86_64 or aarch64)"
  else pure () : Lean.Elab.Command.CommandElabM Unit)

package «lean-swe-harness» where
  packagesDir := "../.lake/packages"
  moreLinkArgs := #["-Wl,-z,now", "-lcrypto", "-Wl,--exclude-libs,libcrypto.a", "-lpthread"]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩,
    ⟨`weak.linter.missingDocs, true⟩,
    ⟨`weak.linter.unusedVariables, true⟩
  ]

require «lean-swe-proofs» from "../proofs"
require «lean-swe» from ".."

@[default_target]
lean_lib Fuzz where
  globs := #[.submodules `Fuzz]

@[default_target]
lean_lib ModelMutants where
  globs := #[.submodules `ModelMutants]

@[default_target]
lean_lib UnitTests where
  globs := #[.one `UnitTests, .submodules `UnitTests]

private def rootLeanSwePkg : FetchM Package := do
  let some pkg ← findPackageByName? `«lean-swe»
    | error "required package 'lean-swe' not found in workspace"
  return pkg

private def buildFdBoxObj (pkg : NPackage __name__) (rootDir : System.FilePath) (tag : String) :
    FetchM (Job System.FilePath) := do
  let cDir := rootDir / "LeanSwe" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (cDir / "fd_box.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / s!"linux_fd_box_{tag}.o"
  buildO oFile (deps.map fun _ => cDir / "fd_box.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]

extern_lib «leanswe_envvars_fuzz» pkg := do
  let oFile := pkg.buildDir / "c" / "envvars_fuzz_env.o"
  let srcJob ← inputTextFile (pkg.dir / "Fuzz" / "EnvVars" / "c" / "envvars_fuzz_env.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_envvars_fuzz"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

extern_lib «leanswe_linux_process_fuzz_env» pkg := do
  let rootPkg ← rootLeanSwePkg
  let cDir := rootPkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let fDir := pkg.dir / "Fuzz" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (fDir / "process_fuzz_env.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / "linux_process_fuzz_env.o"
  let oJob ← buildO oFile (deps.map fun _ => fDir / "process_fuzz_env.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let fdBoxJob ← buildFdBoxObj pkg rootPkg.dir "proc_fuzz"
  let name := nameToStaticLib "leanswe_linux_process_fuzz_env"
  buildStaticLib (pkg.staticLibDir / name) #[oJob, fdBoxJob]

extern_lib «leanswe_sandbox_fuzz_env» pkg := do
  let rootPkg ← rootLeanSwePkg
  let cDir := rootPkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let fDir := pkg.dir / "Fuzz" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (fDir / "sandbox_fuzz_env.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / "linux_sandbox_fuzz_env.o"
  let oJob ← buildO oFile (deps.map fun _ => fDir / "sandbox_fuzz_env.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let fdBoxJob ← buildFdBoxObj pkg rootPkg.dir "sbx_fuzz"
  let name := nameToStaticLib "leanswe_sandbox_fuzz_env"
  buildStaticLib (pkg.staticLibDir / name) #[oJob, fdBoxJob]

extern_lib «leanswe_fuzz_env» pkg := do
  let rootPkg ← rootLeanSwePkg
  let cDir := rootPkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
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

extern_lib «leanswe_linux_timerand_fuzz» pkg := do
  let oFile := pkg.buildDir / "c" / "timerand_fuzz_sig.o"
  let srcJob ← inputTextFile (pkg.dir / "Fuzz" / "LinuxSyscall" / "c" / "timerand_fuzz_sig.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let name := nameToStaticLib "leanswe_linux_timerand_fuzz"
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

extern_lib «leanswe_poll_fuzz_env» pkg := do
  let rootPkg ← rootLeanSwePkg
  let cDir := rootPkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let fDir := pkg.dir / "Fuzz" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (fDir / "poll_fuzz_env.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / "linux_poll_fuzz_env.o"
  let oJob ← buildO oFile (deps.map fun _ => fDir / "poll_fuzz_env.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let fdBoxJob ← buildFdBoxObj pkg rootPkg.dir "poll_fuzz"
  let name := nameToStaticLib "leanswe_poll_fuzz_env"
  buildStaticLib (pkg.staticLibDir / name) #[oJob, fdBoxJob]

extern_lib «leanswe_net_fuzz_env» pkg := do
  let rootPkg ← rootLeanSwePkg
  let cDir := rootPkg.dir / "LeanSwe" / "LinuxSyscall" / "c"
  let fDir := pkg.dir / "Fuzz" / "LinuxSyscall" / "c"
  let hdrJob ← inputTextFile (cDir / "fd_box.h")
  let srcJob ← inputTextFile (fDir / "net_fuzz_env.c")
  let deps := Job.collectArray #[hdrJob, srcJob]
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "c" / "linux_net_fuzz_env.o"
  let oJob ← buildO oFile (deps.map fun _ => fDir / "net_fuzz_env.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let fdBoxJob ← buildFdBoxObj pkg rootPkg.dir "net_fuzz"
  let name := nameToStaticLib "leanswe_net_fuzz_env"
  buildStaticLib (pkg.staticLibDir / name) #[oJob, fdBoxJob]

@[default_target]
lean_exe «leanswe-fuzz» where
  root := `Fuzz.Main
