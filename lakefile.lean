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
  extraDepTargets := #[`«leanswe-psandbox-init-data»]
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
    .submodules `LeanSwe.NetRelay,
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
    .one `LeanSwe.ProcessSandbox.Types,
    .one `LeanSwe.ProcessSandbox.Model,
    .one `LeanSwe.ProcessSandbox.SpecTests,
    .one `LeanSwe.ProcessSandbox.SpecMutants,
    .one `LeanSwe.ProcessSandbox.Impl,
    .one `LeanSwe.ProcessSandbox.Interface,
    .andSubmodules `LeanSwe.ProcessSandbox.Proofs,
    .one `LeanSwe.ProcessSandbox.RuntimeTests,
    .submodules `LeanSwe.ProcessSandbox.Seccomp,
    .submodules `LeanSwe.ProcessSandbox.Raw,
    .submodules `LeanSwe.ProcessSandbox.Host,
    .andSubmodules `LeanSwe.ProcessSandbox.Init.Proofs,
    .one `LeanSwe.ProcessSandbox.Init.Verified,
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
lean_lib LeanSweProcessSandboxInitData where
  srcDir := ".lake/build/gen"
  roots := #[`LeanSwe.ProcessSandbox.InitData]
  globs := #[.one `LeanSwe.ProcessSandbox.InitData]
  extraDepTargets := #[`«leanswe-psandbox-init-data»]

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
lean_lib «LeanSwe.ProcessSandbox.Init.AeneasGen» where
  roots := #[
    `LeanSwe.ProcessSandbox.Init.Aeneas.TypesExternal,
    `LeanSwe.ProcessSandbox.Init.Aeneas.Types,
    `LeanSwe.ProcessSandbox.Init.Aeneas.FunsExternal,
    `LeanSwe.ProcessSandbox.Init.Aeneas.Funs
  ]
  globs := #[
    .one `LeanSwe.ProcessSandbox.Init.Aeneas.TypesExternal,
    .one `LeanSwe.ProcessSandbox.Init.Aeneas.Types,
    .one `LeanSwe.ProcessSandbox.Init.Aeneas.FunsExternal,
    .one `LeanSwe.ProcessSandbox.Init.Aeneas.Funs
  ]
  leanOptions := #[⟨`weak.linter.missingDocs, false⟩]

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
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "EnvVars" / "Raw" / "c" / "envvars_shim.c")
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
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "CryptoHash" / "Raw" / "c" / "cryptohash_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-I", lean.includeDir.toString]
    #["-O2", "-DNDEBUG", "-DLEAN_EXPORTING", "-fPIC", "-fvisibility=hidden", "-pthread", "-Wall", "-Wextra", "-Werror"]
  let name := nameToStaticLib "leanswe_cryptohash"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

private def base64Table : ByteArray :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toUTF8

private def encodeBase64Lake (bs : ByteArray) : String := Id.run do
  let n := bs.size
  let mut out := ByteArray.emptyWithCapacity (((n + 2) / 3) * 4)
  let mut i := 0
  while i + 2 < n do
    let b0 := bs[i]!.toNat
    let b1 := bs[i + 1]!.toNat
    let b2 := bs[i + 2]!.toNat
    out := out.push base64Table[b0 >>> 2]!
    out := out.push base64Table[((b0 &&& 3) <<< 4) ||| (b1 >>> 4)]!
    out := out.push base64Table[((b1 &&& 15) <<< 2) ||| (b2 >>> 6)]!
    out := out.push base64Table[b2 &&& 63]!
    i := i + 3
  let rem := n - i
  if rem == 1 then
    let b0 := bs[i]!.toNat
    out := out.push base64Table[b0 >>> 2]!
    out := out.push base64Table[(b0 &&& 3) <<< 4]!
    out := out.push '='.toNat.toUInt8
    out := out.push '='.toNat.toUInt8
  else if rem == 2 then
    let b0 := bs[i]!.toNat
    let b1 := bs[i + 1]!.toNat
    out := out.push base64Table[b0 >>> 2]!
    out := out.push base64Table[((b0 &&& 3) <<< 4) ||| (b1 >>> 4)]!
    out := out.push base64Table[(b1 &&& 15) <<< 2]!
    out := out.push '='.toNat.toUInt8
  return String.fromUTF8! out

private def resolveCargoAndEnv (rustFlags? : Option String) :
    IO (String × Array (String × Option String)) := do
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
    ("RUSTFLAGS", rustFlags?)
  ]
  let extraEnv := match useAeneas, absAeneas? with
    | true, some ad => baseEnv ++ #[("CARGO_HOME", some s!"{ad}/cargo"), ("RUSTUP_HOME", some s!"{ad}/rustup")]
    | _, _ => baseEnv
  return (cargoBin, extraEnv)

/-- Compile `#![no_std]` `psandbox-init` and generate `.lake/build/gen/LeanSwe/ProcessSandbox/InitData.lean`. -/
target «leanswe-psandbox-init-data» pkg : System.FilePath := do
  let rustDir := pkg.dir / "LeanSwe" / "ProcessSandbox" / "Init" / "rust"
  let targetDir := pkg.buildDir / "psandbox-init-rust"
  let genFile := pkg.buildDir / "gen" / "LeanSwe" / "ProcessSandbox" / "InitData.lean"
  let manifestJob ← inputTextFile (rustDir / "Cargo.toml")
  let lockJob ← inputTextFile (rustDir / "Cargo.lock")
  let toolchainJob ← inputTextFile (rustDir / "rust-toolchain.toml")
  let srcLib ← inputTextFile (rustDir / "src" / "lib.rs")
  let srcMain ← inputTextFile (rustDir / "src" / "main.rs")
  let srcSys ← inputTextFile (rustDir / "src" / "init_sys.rs")
  let srcCli ← inputTextFile (rustDir / "src" / "cli.rs")
  let srcPlan ← inputTextFile (rustDir / "src" / "plan.rs")
  let srcOps ← inputTextFile (rustDir / "src" / "ops.rs")
  let depsJob := Job.collectArray #[manifestJob, lockJob, toolchainJob, srcLib, srcMain, srcSys, srcCli, srcPlan, srcOps]
  buildFileAfterDep genFile depsJob fun _ => do
    IO.FS.createDirAll targetDir
    let absRustDir ← IO.FS.realPath rustDir
    let absTargetDir ← IO.FS.realPath targetDir
    let (cargoBin, extraEnv) ← resolveCargoAndEnv none
    proc {
      cmd := cargoBin
      args := #["build", "--locked", "--target-dir", absTargetDir.toString, "--release", "--bin", "psandbox-init", "--features", "standalone"]
      cwd := some absRustDir
      env := extraEnv
    }
    let initBin := absTargetDir / "release" / "psandbox-init"
    let bytes ← IO.FS.readBinFile initBin
    let b64 := encodeBase64Lake bytes
    createParentDirs genFile
    let content :=
      "namespace LeanSwe.ProcessSandbox.InitData\n\n" ++
      "/-- Base64-encoded ELF bytes of the compiled `leanswe-psandbox-init` helper binary. -/\n" ++
      "def initBinaryBase64 : String :=\n" ++
      "  \"" ++ b64 ++ "\"\n\n" ++
      "end LeanSwe.ProcessSandbox.InitData\n"
    IO.FS.writeFile genFile content

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

extern_lib «leanswe_linux_passwd» pkg := do
  let oFile := pkg.buildDir / "c" / "passwd_shim.o"
  let srcJob ← inputTextFile (pkg.dir / "LeanSwe" / "LinuxSyscall" / "c" / "passwd_shim.c")
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcJob
    #["-isystem", lean.includeDir.toString]
    #["-O2", "-fPIC", "-DNDEBUG", "-DLEAN_EXPORTING", "-fvisibility=hidden", "-Wall", "-Wextra", "-Werror", "-Wshadow", "-Wconversion"]
  let name := nameToStaticLib "leanswe_linux_passwd"
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
    let (cargoBin, extraEnv) ← resolveCargoAndEnv (some "-C opt-level=3")
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

extern_lib «leanswe_postfork_rust» := do
  postfork_rust_archive.fetch
