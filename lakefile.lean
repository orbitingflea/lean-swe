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

@[default_target]
lean_lib Core where
  globs := #[.submodules `Core]

@[default_target]
lean_lib LeanSwe where
  globs := #[.one `LeanSwe, .submodules `LeanSwe]

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

extern_lib «leanswe_envvars» pkg := do
  let oFile := pkg.buildDir / "c" / "envvars_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "EnvVars" / "c" / "envvars_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_envvars"
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
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "CryptoHash" / "c" / "cryptohash_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-pthread", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_cryptohash"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

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

extern_lib «leanswe_linux_timerand» pkg := do
  let oFile := pkg.buildDir / "c" / "timerand_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "LinuxSyscall" / "c" / "timerand_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_linux_timerand"
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

extern_lib «leanswe_postfork» pkg := do
  let oFile := pkg.buildDir / "c" / "postfork_shim.o"
  let cDir := pkg.dir / "LeanSwe" / "PostFork" / "c"
  let srcJob ← inputTextFile (cDir / "postfork_shim.c")
  let fdBoxHdrJob ← inputTextFile (pkg.dir / "LeanSwe" / "LinuxSyscall" / "c" / "fd_box.h")
  let depsJob := Job.collectArray #[srcJob, fdBoxHdrJob]
  let lean ← getLeanInstall
  let oJob ← buildO oFile (depsJob.map fun _ => cDir / "postfork_shim.c")
    #["-I", lean.includeDir.toString, "-I", cDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let fdBoxJob ← buildFdBoxObj pkg "postfork"
  let name := nameToStaticLib "leanswe_postfork"
  buildStaticLib (pkg.staticLibDir / name) #[oJob, fdBoxJob]
