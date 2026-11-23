import Lean

/-!
Promise coverage audit for `lean-swe` compiled `.olean` artifacts.

Checks:
1. Every `LeanSwe/**/SpecTests.lean` and `LeanSwe/**/SpecMutants.lean` file on disk is
   transitively imported by `LeanSwe`.
2. Zero custom `axiom` declarations exist in `Core` or `LeanSwe`.
3. Every `SpecTests` module has a companion `SpecMutants` module containing at least one
   `Core.AllPass` mutant theorem/example, and no `SpecTests` module contains any theorem,
   `example`, or `Core.AllPass` reference.
4. Every public `test_*` (and non-legacy `empirical_*`) declaration in a `SpecTests` module has
   a public, non-projection theorem outside `SpecTests`, `SpecMutants`, and `RuntimeTests` whose
   conclusion is `Core.AllPass` applied to that promise, plus one with `Core.CanReach` when the
   promise uses `Core.NondetTest.assume`.
5. Qualifying theorems have no hypothesis (`Prop` binder) and all qualifying theorems plus all
   `SpecMutants` declarations/examples use only standard axioms
   (`propext`, `Classical.choice`, `Quot.sound`) with zero `sorry`/`admit`/`native_decide`.
6. One-way transitive `.olean` import-DAG ratchet and no-proof-content audit covering `LeanSwe`,
   `LeanSwe.PostFork.Verified`, `LeanSwe.ProcessSandbox.Init.Verified`, and any extra unimported
   modules:
   - Within-package transitive checks (`Types`/`Model`/`SpecTests`/`Properties` cannot import
     same-package `Impl`/`SysBridge`/`Interface`/`Proofs`/`SpecMutants`/`RuntimeTests`/
     `TestSupport`, or any unclassified `.other` helper module whose name matches no role;
     `Impl`/`SysBridge`/`Interface` cannot import same-package
     `Proofs`/`SpecTests`/`Properties`/`SpecMutants`/`RuntimeTests`).
   - Cross-package checks: direct imports target only another package's `Types`, `Model`, or
     `Interface` (no `Impl`/`SysBridge`/`Proofs`/`SpecTests`/`Properties`/`SpecMutants`/
     `RuntimeTests`/`TestSupport`/`.other`), plus cross-package transitive leak checks and
     constant-level indirect reach-in and `.Internal.` reach-in checks on non-proof modules.
   - `namespace <Pkg>.Model` inside `*.Proofs*` ban over `.olean` constant tables (excluding
     strictly verified lazy compiler-generated aux lemmas for existing non-proof `Model` decls).
   - No `*.Proofs*` constants in `SpecTests`/`Properties` (`type` or `value`), in exported
     `refines_model` / `obeys_model` theorem signatures, or in qualifying `AllPass` / `CanReach`
     theorem signatures, enforced with a strict shrinking ratchet allowlist (fails on both new
     violations and stale allowlist entries).
-/

open Lean Meta

private def allowedAxioms : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity 4 |>.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound

private def legacyEmpiricalModules : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity 0

private def timeRandAuditModules : Array Name := #[
  `LeanSwe.LinuxSyscall.TimeRand.Types,
  `LeanSwe.LinuxSyscall.TimeRand.Model,
  `LeanSwe.LinuxSyscall.TimeRand.Impl,
  `LeanSwe.LinuxSyscall.TimeRand.Interface,
  `LeanSwe.LinuxSyscall.TimeRand.SpecTests,
  `LeanSwe.LinuxSyscall.TimeRand.Proofs
]

private def filesAuditModules : Array Name := #[
  `LeanSwe.LinuxSyscall.Files.Types,
  `LeanSwe.LinuxSyscall.Files.Model,
  `LeanSwe.LinuxSyscall.Files.Seed,
  `LeanSwe.LinuxSyscall.Files.Impl,
  `LeanSwe.LinuxSyscall.Files.Interface,
  `LeanSwe.LinuxSyscall.Files.SpecTests,
  `LeanSwe.LinuxSyscall.Files.Proofs
]

private def passwdAuditModules : Array Name := #[
  `LeanSwe.LinuxSyscall.Passwd.Types,
  `LeanSwe.LinuxSyscall.Passwd.Model,
  `LeanSwe.LinuxSyscall.Passwd.Impl,
  `LeanSwe.LinuxSyscall.Passwd.Interface,
  `LeanSwe.LinuxSyscall.Passwd.SpecTests,
  `LeanSwe.LinuxSyscall.Passwd.Proofs
]

private def dnsAuditModules : Array Name := #[
  `LeanSwe.LinuxSyscall.Dns.Types,
  `LeanSwe.LinuxSyscall.Dns.Model,
  `LeanSwe.LinuxSyscall.Dns.Impl,
  `LeanSwe.LinuxSyscall.Dns.Interface,
  `LeanSwe.LinuxSyscall.Dns.SpecTests,
  `LeanSwe.LinuxSyscall.Dns.Proofs
]

private def pollAuditModules : Array Name := #[
  `LeanSwe.LinuxSyscall.Poll.Types,
  `LeanSwe.LinuxSyscall.Poll.Model,
  `LeanSwe.LinuxSyscall.Poll.Impl,
  `LeanSwe.LinuxSyscall.Poll.Interface,
  `LeanSwe.LinuxSyscall.Poll.SpecTests,
  `LeanSwe.LinuxSyscall.Poll.Proofs
]

private def netAuditModules : Array Name := #[
  `LeanSwe.LinuxSyscall.Net.Types,
  `LeanSwe.LinuxSyscall.Net.Model,
  `LeanSwe.LinuxSyscall.Net.Impl,
  `LeanSwe.LinuxSyscall.Net.Interface,
  `LeanSwe.LinuxSyscall.Net.SpecTests,
  `LeanSwe.LinuxSyscall.Net.Proofs
]

private def processAuditModules : Array Name := #[
  `LeanSwe.LinuxSyscall.Process.Types,
  `LeanSwe.LinuxSyscall.Process.Model,
  `LeanSwe.LinuxSyscall.Process.Impl,
  `LeanSwe.LinuxSyscall.Process.Interface,
  `LeanSwe.LinuxSyscall.Process.SpecTests,
  `LeanSwe.LinuxSyscall.Process.Proofs
]

private def envVarsAuditModules : Array Name := #[
  `LeanSwe.EnvVars.Raw.Types,
  `LeanSwe.EnvVars.Raw.Model,
  `LeanSwe.EnvVars.Raw.Impl,
  `LeanSwe.EnvVars.Raw.Interface,
  `LeanSwe.EnvVars.Raw.SpecTests,
  `LeanSwe.EnvVars.Raw.Proofs,
  `LeanSwe.EnvVars.Types,
  `LeanSwe.EnvVars.Model,
  `LeanSwe.EnvVars.Impl,
  `LeanSwe.EnvVars.Interface,
  `LeanSwe.EnvVars.SpecTests,
  `LeanSwe.EnvVars.Proofs
]

private def cryptoHashAuditModules : Array Name := #[
  `LeanSwe.CryptoHash.Raw.Types,
  `LeanSwe.CryptoHash.Raw.Model,
  `LeanSwe.CryptoHash.Raw.Impl,
  `LeanSwe.CryptoHash.Raw.Interface,
  `LeanSwe.CryptoHash.Raw.SpecTests,
  `LeanSwe.CryptoHash.Raw.Proofs,
  `LeanSwe.CryptoHash.Types,
  `LeanSwe.CryptoHash.Model,
  `LeanSwe.CryptoHash.Impl,
  `LeanSwe.CryptoHash.Interface,
  `LeanSwe.CryptoHash.SpecTests,
  `LeanSwe.CryptoHash.Proofs
]

private def postForkAuditModules : Array Name := #[`LeanSwe.PostFork.Types, `LeanSwe.PostFork.Model, `LeanSwe.PostFork.Impl, `LeanSwe.PostFork.Interface]
private def cryptoHashVectorModules : Array Name := #[
  `LeanSwe.CryptoHash.Raw.Proofs.HmacEmptyInner,
  `LeanSwe.CryptoHash.Raw.Proofs.HmacTc1,
  `LeanSwe.CryptoHash.Raw.Proofs.HmacTc1Inner,
  `LeanSwe.CryptoHash.Raw.Proofs.HmacTc2,
  `LeanSwe.CryptoHash.Raw.Proofs.HmacTc2Inner,
  `LeanSwe.CryptoHash.Raw.Proofs.HmacTc2Outer,
  `LeanSwe.CryptoHash.Raw.Proofs.HmacTc6,
  `LeanSwe.CryptoHash.Raw.Proofs.HmacTc6Inner,
  `LeanSwe.CryptoHash.Raw.Proofs.HmacVectors,
  `LeanSwe.CryptoHash.Raw.Proofs.Sha256Vec131,
  `LeanSwe.CryptoHash.Raw.Proofs.Sha256Vectors,
  `LeanSwe.CryptoHash.Raw.Proofs.Sha512Vectors
]

private def sqliteAuditModules : Array Name := #[
  `LeanSwe.Sqlite.Types, `LeanSwe.Sqlite.Model, `LeanSwe.Sqlite.Impl, `LeanSwe.Sqlite.Interface,
  `LeanSwe.Sqlite.SpecTests, `LeanSwe.Sqlite.Proofs, `LeanSwe.Sqlite.Proofs.ModelTrace,
  `LeanSwe.Sqlite.Raw.Types, `LeanSwe.Sqlite.Raw.Model, `LeanSwe.Sqlite.Raw.Impl, `LeanSwe.Sqlite.Raw.Interface,
  `LeanSwe.Sqlite.Raw.SpecTests, `LeanSwe.Sqlite.Raw.Proofs,
  `LeanSwe.Sqlite.Raw.Proofs.ErrorAndFlagsProofs,
  `LeanSwe.Sqlite.Raw.Proofs.Helpers,
  `LeanSwe.Sqlite.Raw.Proofs.StmtProofs,
  `LeanSwe.Sqlite.Raw.Proofs.UriHasWalProofs,
  `LeanSwe.Sqlite.Raw.Proofs.UriNoWalProofs,
  `LeanSwe.Sqlite.Raw.Proofs.UriProofs,
  `LeanSwe.Sqlite.Raw.Proofs.WalProofs
]

private def isProjectModule (m : Name) : Bool :=
  let r := m.getRoot
  r == `Core || r == `LeanSwe

private def forbiddenStdSubtrees : Array Name :=
  #[`Time, `Net, `Http, `Sync, `Async, `Internal]

private def isAllowedClosureStdlibModule (allowInternalForIn : Bool := false) (m : Name) : Bool :=
  let r := m.getRoot
  if r == `Init then true
  else if allowInternalForIn && m == `Std.Internal.ForIn.Basic then true
  else if r == `Std then
    m.components.take 3 == [`Std, `Internal, `ForIn] ||
      match m.components.drop 1 with
      | sub :: _ => !forbiddenStdSubtrees.contains sub
      | [] => true
  else false

private def nameLastStr (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => ""

private def discoverPackageModules (env : Environment) (extraMods : Array Name) (pkgPrefix : Name) (baseMods : Array Name) : Array Name := Id.run do
  let mut mods := baseMods
  let prefStr := pkgPrefix.toString
  for m in env.header.moduleNames ++ extraMods do
    let s := m.toString
    if s == prefStr || s.startsWith (prefStr ++ ".") then
      let last := nameLastStr m
      if last != "RuntimeTests" && last != "SpecMutants" && !mods.contains m then
        mods := mods.push m
  return mods

private def isAllowedTimeRandClosureModule (m : Name) : Bool :=
  m.getRoot == `Core ||
    m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Common] ||
    timeRandAuditModules.contains m

private def isAllowedFilesClosureModule (m : Name) : Bool :=
  m.getRoot == `Core ||
    m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Common] ||
    (m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Files] &&
      nameLastStr m != "RuntimeTests" && nameLastStr m != "SpecMutants")

private def isAllowedPasswdClosureModule (m : Name) : Bool :=
  m.getRoot == `Core ||
    m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Common] ||
    passwdAuditModules.contains m

private def isAllowedDnsClosureModule (m : Name) : Bool :=
  m.getRoot == `Core ||
    m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Common] ||
    dnsAuditModules.contains m

private def isAllowedPollClosureModule (m : Name) : Bool :=
  m.getRoot == `Core ||
    m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Common] ||
    (m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Poll] &&
      nameLastStr m != "RuntimeTests" && nameLastStr m != "SpecMutants")

private def isAllowedNetClosureModule (m : Name) : Bool :=
  m.getRoot == `Core ||
    m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Common] ||
    (m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Net] &&
      nameLastStr m != "RuntimeTests" && nameLastStr m != "SpecMutants")

private def isAllowedProcessClosureModule (m : Name) : Bool :=
  m.getRoot == `Core ||
    m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Common] ||
    (m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Process] &&
      let last := nameLastStr m
      last != "RuntimeTests" && last != "SpecMutants")

private def isAllowedEnvVarsClosureModule (m : Name) : Bool :=
  m.getRoot == `Core || envVarsAuditModules.contains m

private def isAllowedPostForkClosureModule (m : Name) : Bool :=
  m.getRoot == `Core || m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Common] || postForkAuditModules.contains m

private def isInitVerifiedMod (m : Name) : Bool :=
  m.components.take 3 == [`LeanSwe, `ProcessSandbox, `Init]

private def isPostForkVerifiedMod (m : Name) : Bool :=
  m == `LeanSwe.PostFork.Verified || m == `LeanSwe.PostFork.SpecTests || m == `LeanSwe.PostFork.SpecMutants ||
    m.components.take 3 == [`LeanSwe, `PostFork, `Aeneas] || m.components.take 3 == [`LeanSwe, `PostFork, `Proofs] ||
    isInitVerifiedMod m

private def isAllowedCryptoHashClosureModule (m : Name) : Bool :=
  m.getRoot == `Core ||
    cryptoHashAuditModules.contains m ||
    cryptoHashVectorModules.contains m

private def isAllowedSqliteClosureModule (m : Name) : Bool :=
  m.getRoot == `Core || sqliteAuditModules.contains m

private def allowedTimeRandExternSyms : Std.HashMap Name String :=
  Std.HashMap.emptyWithCapacity 4
    |>.insert `LeanSwe.LinuxSyscall.TimeRand.rawClockGettime "leanswe_sys_clock_gettime"
    |>.insert `LeanSwe.LinuxSyscall.TimeRand.rawClockNanosleep "leanswe_sys_clock_nanosleep"
    |>.insert `LeanSwe.LinuxSyscall.TimeRand.rawGetrandom "leanswe_sys_getrandom"

private def allowedFilesExternSyms : Std.HashMap Name String :=
  Std.HashMap.emptyWithCapacity 32
    |>.insert `LeanSwe.LinuxSyscall.Files.rawOpenat "leanswe_sys_openat"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawOpenat2 "leanswe_sys_openat2"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawClose "leanswe_sys_close"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawRead "leanswe_sys_read"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawWrite "leanswe_sys_write"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawFstat "leanswe_sys_fstat"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawFstatat "leanswe_sys_fstatat"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawFaccessat "leanswe_sys_faccessat"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawMkdirat "leanswe_sys_mkdirat"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawUnlinkat "leanswe_sys_unlinkat"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawRenameat2 "leanswe_sys_renameat2"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawSymlinkat "leanswe_sys_symlinkat"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawReadlinkat "leanswe_sys_readlinkat"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawGetdents64 "leanswe_sys_getdents64"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawFchmodat "leanswe_sys_fchmodat"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawFchmod "leanswe_sys_fchmod"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawFlock "leanswe_sys_flock"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawFcntl "leanswe_sys_fcntl"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawFsync "leanswe_sys_fsync"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawGetcwd "leanswe_sys_getcwd"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawLseek "leanswe_sys_lseek"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawReopenReadOnly "leanswe_sys_reopen_readonly"
    |>.insert `LeanSwe.LinuxSyscall.Files.rawDupStdio "leanswe_sys_dup_stdio"

private def allowedPasswdExternSyms : Std.HashMap Name String :=
  Std.HashMap.emptyWithCapacity 4
    |>.insert `LeanSwe.LinuxSyscall.Passwd.rawGetpwuidOnce "leanswe_sys_getpwuid_once"
    |>.insert `LeanSwe.LinuxSyscall.Passwd.rawGetpwnamOnce "leanswe_sys_getpwnam_once"

private def allowedDnsExternSyms : Std.HashMap Name String :=
  Std.HashMap.emptyWithCapacity 2
    |>.insert `LeanSwe.LinuxSyscall.Dns.rawGetaddrinfo "leanswe_sys_getaddrinfo"

private def allowedPollExternSyms : Std.HashMap Name String :=
  Std.HashMap.emptyWithCapacity 4
    |>.insert `LeanSwe.LinuxSyscall.Poll.rawPpoll "leanswe_sys_ppoll"
    |>.insert `LeanSwe.LinuxSyscall.Poll.rawEventfd2 "leanswe_sys_eventfd2"

private def allowedNetExternSyms : Std.HashMap Name String :=
  Std.HashMap.emptyWithCapacity 20
    |>.insert `LeanSwe.LinuxSyscall.Net.rawSocket "leanswe_sys_socket"
    |>.insert `LeanSwe.LinuxSyscall.Net.rawSocketpair "leanswe_sys_socketpair"
    |>.insert `LeanSwe.LinuxSyscall.Net.rawBind "leanswe_sys_bind"
    |>.insert `LeanSwe.LinuxSyscall.Net.rawListen "leanswe_sys_listen"
    |>.insert `LeanSwe.LinuxSyscall.Net.rawAccept4 "leanswe_sys_accept4"
    |>.insert `LeanSwe.LinuxSyscall.Net.rawConnect "leanswe_sys_connect"
    |>.insert `LeanSwe.LinuxSyscall.Net.rawGetsockopt "leanswe_sys_getsockopt"
    |>.insert `LeanSwe.LinuxSyscall.Net.rawSetsockopt "leanswe_sys_setsockopt"
    |>.insert `LeanSwe.LinuxSyscall.Net.rawGetsockname "leanswe_sys_getsockname"
    |>.insert `LeanSwe.LinuxSyscall.Net.rawRecvfrom "leanswe_sys_recvfrom"
    |>.insert `LeanSwe.LinuxSyscall.Net.rawSendto "leanswe_sys_sendto"
    |>.insert `LeanSwe.LinuxSyscall.Net.rawShutdown "leanswe_sys_shutdown"
    |>.insert `LeanSwe.LinuxSyscall.Net.rawSendmsg "leanswe_sys_sendmsg_scm"
    |>.insert `LeanSwe.LinuxSyscall.Net.rawRecvmsg "leanswe_sys_recvmsg_scm"
    |>.insert `LeanSwe.LinuxSyscall.Net.rawNetIoctl "leanswe_sys_net_ioctl"

private def allowedProcessExternSyms : Std.HashMap Name String :=
  Std.HashMap.emptyWithCapacity 8
    |>.insert `LeanSwe.LinuxSyscall.Process.rawPipe2 "leanswe_sys_pipe2"
    |>.insert `LeanSwe.LinuxSyscall.Process.rawWaitpid "leanswe_sys_waitpid"
    |>.insert `LeanSwe.LinuxSyscall.Process.rawKill "leanswe_sys_kill"
    |>.insert `LeanSwe.LinuxSyscall.Process.rawPidfdOpen "leanswe_sys_pidfd_open"
    |>.insert `LeanSwe.LinuxSyscall.Process.rawPidfdSendSignal "leanswe_sys_pidfd_send_signal"
    |>.insert `LeanSwe.LinuxSyscall.Process.rawGetpid "leanswe_sys_getpid"
    |>.insert `LeanSwe.LinuxSyscall.Process.rawGetuid "leanswe_sys_getuid"

private def allowedEnvVarsExternSyms : Std.HashMap Name String :=
  Std.HashMap.emptyWithCapacity 4
    |>.insert `LeanSwe.EnvVars.Raw.rawGetEnvBytes "leanswe_envvars_getenv"
    |>.insert `LeanSwe.EnvVars.Raw.rawListEnvironBytes "leanswe_envvars_environ"

private def postForkExternSpecs : Array (Name × String × Nat × Array Bool) := #[
  (`LeanSwe.PostFork.rawProbeFdOpen, "leanswe_postfork_host_probe_fd", 1, #[false]), (`LeanSwe.PostFork.rawProbeHandleOpen, "leanswe_postfork_host_probe_handle", 1, #[true]),
  (`LeanSwe.PostFork.rawMkPipeCloexec, "leanswe_postfork_host_pipe_cloexec", 0, #[]), (`LeanSwe.PostFork.rawCloseFd, "leanswe_postfork_host_close_fd", 1, #[true]),
  (`LeanSwe.PostFork.rawSetpgid, "leanswe_postfork_host_setpgid", 2, #[false, false]), (`LeanSwe.PostFork.rawWriteOnce, "leanswe_postfork_host_write_once", 4, #[true, true, false, false]),
  (`LeanSwe.PostFork.rawReadOnce, "leanswe_postfork_host_read_once", 2, #[true, false]), (`LeanSwe.PostFork.rawWaitOnce, "leanswe_postfork_host_wait_once", 1, #[false]),
  (`LeanSwe.PostFork.rawForkRun, "leanswe_postfork_host_fork_run", 12, #[false, false, true, true, true, true, true, true, true, true, true, true])]
private def allowedPostForkExternSyms : Std.HashMap Name String := postForkExternSpecs.foldl (fun m (n, s, _, _) => m.insert n s) {}
private def allowedCryptoHashExternSyms : Std.HashMap Name String :=
  Std.HashMap.emptyWithCapacity 4
    |>.insert `LeanSwe.CryptoHash.Raw.rawDigest "leanswe_cryptohash_digest"
    |>.insert `LeanSwe.CryptoHash.Raw.rawHmacSha256 "leanswe_cryptohash_hmac_sha256"
    |>.insert `LeanSwe.CryptoHash.Raw.rawCtEqual "leanswe_cryptohash_ct_equal"

private def allowedSqliteExternSyms : Std.HashMap Name String :=
  Std.HashMap.ofList [
    (`LeanSwe.Sqlite.Raw.rawOpenV2, "leanswe_sqlite_open_v2"), (`LeanSwe.Sqlite.Raw.rawClose, "leanswe_sqlite_close"),
    (`LeanSwe.Sqlite.Raw.rawExtendedResultCodes, "leanswe_sqlite_extended_result_codes"),
    (`LeanSwe.Sqlite.Raw.rawBusyTimeout, "leanswe_sqlite_busy_timeout"), (`LeanSwe.Sqlite.Raw.rawPrepareV2, "leanswe_sqlite_prepare_v2"),
    (`LeanSwe.Sqlite.Raw.rawStep, "leanswe_sqlite_step"), (`LeanSwe.Sqlite.Raw.rawReset, "leanswe_sqlite_reset"),
    (`LeanSwe.Sqlite.Raw.rawClearBindings, "leanswe_sqlite_clear_bindings"), (`LeanSwe.Sqlite.Raw.rawFinalize, "leanswe_sqlite_finalize"),
    (`LeanSwe.Sqlite.Raw.rawBindParamCount, "leanswe_sqlite_bind_param_count"), (`LeanSwe.Sqlite.Raw.rawBindNull, "leanswe_sqlite_bind_null"),
    (`LeanSwe.Sqlite.Raw.rawBindInt64, "leanswe_sqlite_bind_int64"), (`LeanSwe.Sqlite.Raw.rawBindDouble, "leanswe_sqlite_bind_double"),
    (`LeanSwe.Sqlite.Raw.rawBindText, "leanswe_sqlite_bind_text"), (`LeanSwe.Sqlite.Raw.rawBindBlob, "leanswe_sqlite_bind_blob"),
    (`LeanSwe.Sqlite.Raw.rawColumnCount, "leanswe_sqlite_column_count"), (`LeanSwe.Sqlite.Raw.rawColumnType, "leanswe_sqlite_column_type"),
    (`LeanSwe.Sqlite.Raw.rawColumnInt64, "leanswe_sqlite_column_int64"), (`LeanSwe.Sqlite.Raw.rawColumnDouble, "leanswe_sqlite_column_double"),
    (`LeanSwe.Sqlite.Raw.rawColumnTextBytes, "leanswe_sqlite_column_text_bytes"), (`LeanSwe.Sqlite.Raw.rawColumnBlob, "leanswe_sqlite_column_blob")
  ]

private def isAllowedSqliteStdMutexOrRef (cName : Name) (extData : ExternAttrData) : Bool :=
  let expectedSym? : Option String :=
    if cName == `ST.Prim.mkRef then some "lean_st_mk_ref"
    else if cName == `ST.Prim.Ref.get then some "lean_st_ref_get"
    else if cName == `ST.Prim.Ref.put then some "lean_st_ref_put"
    else if cName == `ST.Prim.Ref.take then some "lean_st_ref_take"
    else if cName == `ST.Prim.Ref.swap then some "lean_st_ref_swap"
    else if cName == `Std.BaseMutex.new then some "lean_io_basemutex_new"
    else if cName == `Std.BaseMutex.lock then some "lean_io_basemutex_lock"
    else if cName == `Std.BaseMutex.tryLock then some "lean_io_basemutex_try_lock"
    else if cName == `Std.BaseMutex.unlock then some "lean_io_basemutex_unlock"
    else none
  match expectedSym? with
  | some sym => extData.entries == [.standard `all sym]
  | none => false

private def forbiddenHostCSymPrefixes : Array String :=
  #["lean_io_", "lean_uv_", "lean_dbg_", "lean_st_", "lean_process_",
    "lean_get_current_time", "lean_get_windows_", "lean_windows_",
    "lean_task_", "lean_runtime_", "lean_dynlib_", "lean_load_",
    "lean_get_std", "lean_get_set_std", "lean_option_get_or_block",
    "lean_internal_get_"]

private def typeMentionsIOEffect (ty : Expr) : Bool :=
  ty.getUsedConstants.any fun u =>
    u == ``IO.RealWorld || u == ``BaseIO || u == ``EIO || u == ``EST

private def isForbiddenHostExtern (cName : Name) (cinfo : ConstantInfo) (extData : ExternAttrData) : Bool :=
  cName.getRoot == `IO || cName.components.contains `IO ||
    cName == `dbgTrace || cName == `dbgTraceVal ||
    cName.toString.startsWith "Lean.IO." ||
    cName.toString.startsWith "Std.Internal.UV." ||
    cName.toString.startsWith "ST.Prim." ||
    cName.toString.startsWith "BaseIO." ||
    typeMentionsIOEffect cinfo.type ||
    extData.entries.any fun e =>
      match e with
      | .adhoc _ => true
      | .inline _ s => forbiddenHostCSymPrefixes.any fun p => s.startsWith p
      | .standard _ s => forbiddenHostCSymPrefixes.any fun p => s.startsWith p
      | .opaque => false

private def isCompilerGeneratedCtorIdx (env : Environment) (cName impl : Name) (cinfo : ConstantInfo) : IO Bool := do
  let .str indName "ctorIdx" := cName | return false
  if indName == .anonymous || impl != cName.str "_impl" then
    return false
  let .defnInfo cDef := cinfo | return false
  if cDef.name != cName || cDef.safety != .safe then
    return false
  if (Lean.declRangeExt.find? env cName).isSome || (Lean.declRangeExt.find? env impl).isSome then
    return false
  if env.getModuleIdxFor? indName != env.getModuleIdxFor? cName ||
      env.getModuleIdxFor? impl != env.getModuleIdxFor? cName then
    return false
  let some (.inductInfo iv) := env.find? indName | return false
  let some (.defnInfo implInfo) := env.find? impl | return false
  if iv.isUnsafe || iv.ctors.length <= 1 then
    return false
  if !(implInfo.value.getUsedConstants.contains `getObjTagNat) then
    return false
  if !(implInfo.value.getUsedConstants.all fun u =>
      u == `getObjTagNat || u == indName || cinfo.type.getUsedConstants.contains u) then
    return false
  let ctx : Core.Context := { fileName := "<ctorIdx>", fileMap := default, maxHeartbeats := 0 }
  let state : Core.State := { env }
  let (ok, _) ← (Meta.MetaM.run' <| Meta.withTransparency .all do
    let isPropInd ← Meta.forallTelescopeReducing iv.type fun _ body => do
      let b ← Meta.whnf body
      return b == .sort .zero
    if isPropInd then
      return false
    Meta.forallTelescopeReducing cinfo.type fun xs ret => do
      if xs.size != iv.numParams + iv.numIndices + 1 then
        return false
      let retWhnf ← Meta.whnf ret
      if retWhnf != mkConst ``Nat then
        return false
      let lastTy ← Meta.inferType xs.back!
      let lastTyWhnf ← Meta.whnf lastTy
      return lastTyWhnf.getAppFn.constName? == some iv.name
  ).toIO ctx state
  return ok

private partial def hasAttrNameInStx (names : Array String) (stx : Syntax) : Bool :=
  if stx.getKind == ``Lean.Parser.Attr.extern then names.contains "extern"
  else if stx.getKind == ``Lean.Parser.Attr.export then names.contains "export"
  else if stx.getKind == ``Lean.Parser.Term.attrInstance then
    let rec hasId : Syntax → Bool
      | .ident _ _ val _ =>
        let s := val.toString
        let last := match val with | .str _ ls => ls | _ => s
        names.contains s || names.contains last
      | .atom _ val => names.contains val
      | .node _ _ args => args.any hasId
      | .missing => false
    hasId stx
  else match stx with
  | .node _ _ args => args.any (hasAttrNameInStx names)
  | _ => false

private partial def hasSyntaxKindInClosure (k : Name) (stx : Syntax) : Bool :=
  if stx.getKind == k then true
  else match stx with
  | .node _ _ args => args.any (hasSyntaxKindInClosure k)
  | _ => false

private def isAllowedProjectDirectImport (m imp : Name) : Bool :=
  let r := imp.getRoot
  r == `Init || r == `Std || r == `Core || r == `LeanSwe ||
    imp.components.take 2 == [`Lean, `Data] ||
    (imp == `Aeneas &&
      (m.components.take 3 == [`LeanSwe, `PostFork, `Aeneas] ||
        m.components.take 4 == [`LeanSwe, `ProcessSandbox, `Init, `Aeneas]))

private def closureForbiddenMetaSyntaxKinds : Array Name :=
  #[``Lean.Parser.Command.macro, ``Lean.Parser.Command.macro_rules,
    ``Lean.Parser.Command.elab, ``Lean.Parser.Command.elab_rules,
    ``Lean.Parser.Command.syntax, ``Lean.Parser.Command.syntaxAbbrev,
    ``Lean.Parser.Command.syntaxCat, ``Lean.Parser.Command.binderPredicate,
    ``Lean.Parser.Command.notation, ``Lean.Parser.Command.mixfix,
    `Lean.runCmd, `Lean.runElab, `Lean.runMeta, `Lean.testExternCmd,
    ``Lean.Parser.Command.eval, ``Lean.Parser.Command.evalBang,
    `Lean.reduceCmd, ``Lean.Parser.Command.check, ``Lean.Parser.Command.check_failure,
    `Lean.Parser.checkTactic, `Lean.Parser.checkTacticFailure,
    ``Lean.Parser.Command.synth, ``Lean.Parser.Command.init_quot,
    `Lean.Elab.Command.reprove, `Lean.Elab.Command.aux_def,
    `Lean.guardMsgsCmd, `Lean.GuardMsgs.guardMsgsCmd, `Lean.guardPanicCmd]

private def checkClosureModuleAttrs (repoDir : System.FilePath) (env : Environment) (modName externMod : Name)
    (allowStdSyncMutex : Bool := false) : IO (Option String) := do
  let parts := modName.components.map (·.toString)
  let path : System.FilePath := (parts.foldl (fun p seg => p / seg) repoDir).withExtension "lean"
  unless ← path.pathExists do
    return some s!"TRUSTED_CLOSURE_MISSING_SOURCE: {path} for {modName}"
  let input ← IO.FS.readFile path
  let ictx := Parser.mkInputContext input path.toString
  let (_header, pstate0, msgs0) ← Parser.parseHeader ictx
  if msgs0.hasErrors then
    return some s!"TRUSTED_CLOSURE_PARSE_ERROR: header parse error in {path}"
  let mut pstate := pstate0
  let mut msgs := msgs0
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  let forbidden := if modName == externMod then #["export", "implemented_by", "csimp"] else #["extern", "export", "implemented_by", "csimp"]
  repeat do
    let (stx, nextState, nextMsgs) := Parser.parseCommand ictx pmctx pstate msgs
    pstate := nextState
    msgs := nextMsgs
    if Parser.isTerminalCommand stx then break
    if closureForbiddenMetaSyntaxKinds.any (hasSyntaxKindInClosure · stx) then
      return some s!"TRUSTED_CLOSURE_FORBIDDEN_SYNTAX: {path} uses macro/elab/syntax/notation/run_cmd"
    if modName != `Core.Assumptions && !(allowStdSyncMutex && modName == `LeanSwe.Sqlite.Raw.Interface) &&
        hasSyntaxKindInClosure ``Lean.Parser.Command.initialize stx then
      return some s!"TRUSTED_CLOSURE_FORBIDDEN_INIT_SYNTAX: {path} uses initialize/builtin_initialize"
    if hasAttrNameInStx forbidden stx then
      return some s!"TRUSTED_CLOSURE_FORBIDDEN_SOURCE_ATTR: {path} uses forbidden attribute ({String.intercalate "/" forbidden.toList})"
  if msgs.hasErrors then
    return some s!"TRUSTED_CLOSURE_PARSE_ERROR: command parse error in {path}"
  return none

private def isAllowedCoreInitDecl (modName cName : Name) : Bool :=
  let u := privateToUserName? cName |>.getD cName
  modName == `Core.Assumptions &&
    (u == `Core.assumpLogSinkRef || u == `Core.openedAssumpLogPathsRef)

private def isAllowedCoreInitFnConst (u : Name) : Bool :=
  u == ``IO.mkRef || u == ``IO.Ref || u == ``BaseIO || u == ``EIO || u == ``IO.Error ||
    u == ``liftM || u == ``instMonadLiftTOfMonadLift || u == ``instMonadLiftBaseIOEIO ||
    u == ``instMonadLiftT || u == ``Option || u == ``Option.none || u == ``Array ||
    u == ``String || u == ``List.toArray || u == ``List.nil ||
    (privateToUserName? u == some `Core.AssumpLogSink)

private def isAllowedCoreInitFn (env : Environment) (modName cName initFn : Name) : Bool :=
  if !isAllowedCoreInitDecl modName cName then false
  else match env.find? initFn with
    | some (.defnInfo iv) =>
      iv.safety == .safe &&
        (getExternAttrData? env initFn).isNone &&
        (Lean.Compiler.getImplementedBy? env initFn).isNone &&
        iv.value.getUsedConstants.all isAllowedCoreInitFnConst
    | _ => false

private def isAllowedSqliteInitDecl (modName cName : Name) : Bool :=
  modName == `LeanSwe.Sqlite.Raw.Interface &&
    (privateToUserName? cName |>.getD cName) == `LeanSwe.Sqlite.Raw.gHandleTable

private def allowedSqliteInitConsts : Array Name := #[
  ``Std.Mutex, ``Std.Mutex.new, ``List.nil, ``Prod,
  ``OfNat.ofNat, ``UInt64, ``UInt64.instOfNat, ``Unit, ``liftM, ``BaseIO, ``EIO, ``IO.Error,
  ``instMonadLiftTOfMonadLift, ``instMonadLiftBaseIOEIO, ``instMonadLiftT,
  `LeanSwe.Sqlite.Raw.RawHandleState, `LeanSwe.Sqlite.Raw.RawHandleState.mk,
  `LeanSwe.Sqlite.Raw.RawHandleTable, `LeanSwe.Sqlite.Raw.RawHandleTable.mk,
  `LeanSwe.Sqlite.Raw.RawDbHandle, `LeanSwe.Sqlite.Raw.RawStmtHandle, `LeanSwe.Sqlite.Raw.StmtHandle
]

private def isAllowedSqliteInitFn (env : Environment) (modName cName initFn : Name) : Bool :=
  isAllowedSqliteInitDecl modName cName && match env.find? initFn with
    | some (.defnInfo iv) =>
      iv.safety == .safe && (getExternAttrData? env initFn).isNone &&
        (Lean.Compiler.getImplementedBy? env initFn).isNone &&
        iv.value.getUsedConstants.contains ``Std.Mutex.new &&
        iv.value.getUsedConstants.all (fun u => allowedSqliteInitConsts.contains (privateToUserName? u |>.getD u))
    | _ => false

private def isAllowedCompilerUnsafeDef (env : Environment) (cName : Name) (v : DefinitionVal) : IO Bool := do
  if (Lean.declRangeExt.find? env cName).isSome then
    return false
  match cName with
  | .str parent "_impl" =>
    match env.find? parent with
    | some parentInfo => isCompilerGeneratedCtorIdx env parent cName parentInfo
    | none => return false
  | .str parent "_unsafe_rec" =>
    if v.safety != .partial then return false
    return env.getModuleIdxFor? parent == env.getModuleIdxFor? cName &&
      match env.find? parent with
      | some (.defnInfo pv) => pv.safety == .safe
      | _ => false
  | _ => return false

private unsafe def checkPackageTrustedClosure (repoDir : System.FilePath) (pkgLabel : String) (auditModules : Array Name)
    (isAllowedMod : Name → Bool) (externMod : Name) (allowedExternSyms : Std.HashMap Name String)
    (seedLinuxCommon : Bool := false) (allowIO : Bool := false)
    (allowInternalForIn : Bool := false) (allowStdSyncMutex : Bool := false) : IO (Array String) := do
  enableInitializersExecution
  let trEnv ← importModules (auditModules.map fun m => { module := m }) {} (loadExts := true)
  let csimpState := Lean.Compiler.CSimp.ext.getState trEnv
  let mut errs : Array String := #[]
  for h : i in [0 : trEnv.header.moduleNames.size] do
    let m := trEnv.header.moduleNames[i]
    if isProjectModule m then
      if !isAllowedMod m then
        errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_IMPORT: {m} imported into {pkgLabel} closure"
      else
        if let some attrErr ← checkClosureModuleAttrs repoDir trEnv m externMod allowStdSyncMutex then
          errs := errs.push attrErr
      if let some data := trEnv.header.moduleData[i]? then
        for c in data.constants do
          if (Lean.getExportNameFor? trEnv c.name).isSome then
            errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_EXPORT: {c.name} in {m}"
          if let some initFn := Lean.regularInitAttr.getParam? trEnv c.name then
            if !isAllowedCoreInitFn trEnv m c.name initFn &&
                !(allowStdSyncMutex && isAllowedSqliteInitFn trEnv m c.name initFn) then
              errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_INIT: {c.name} in {m}"
          if (Lean.builtinInitAttr.getParam? trEnv c.name).isSome then
            errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_BUILTIN_INIT: {c.name} in {m}"
    else if !(isAllowedClosureStdlibModule allowInternalForIn m ||
        (allowStdSyncMutex && m.components.take 2 == [`Std, `Sync])) then
      errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_IMPORT: {m} imported into {pkgLabel} closure"
    for scEntry in Lean.Compiler.CSimp.ext.ext.getModuleEntries trEnv i do
      let entry := match scEntry with
        | .global e => e
        | .scoped _ e => e
      let origMod := trEnv.getModuleIdxFor? entry.fromDeclName |>.bind (trEnv.header.moduleNames[·]?) |>.getD .anonymous
      let thmMod := trEnv.getModuleIdxFor? entry.thmName |>.bind (trEnv.header.moduleNames[·]?) |>.getD .anonymous
      let toMod := trEnv.getModuleIdxFor? entry.toDeclName |>.bind (trEnv.header.moduleNames[·]?) |>.getD .anonymous
      if isProjectModule m || isProjectModule origMod || isProjectModule thmMod || isProjectModule toMod then
        errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_CSIMP: {entry.fromDeclName} -> {entry.toDeclName} (thm={entry.thmName}, mod={m})"
  let mut visited : Std.HashSet (Name × Bool × Bool × Bool) := {}
  let mut queue : Array (Name × Bool × Bool × Bool × Name) := #[]
  for h : i in [0 : trEnv.header.moduleNames.size] do
    let m := trEnv.header.moduleNames[i]
    if m.getRoot == `LeanSwe || (m.getRoot == `Core && m != `Core.Assumptions) then
      let some data := trEnv.header.moduleData[i]? | continue
      let fromSpec := m.getString! == "SpecTests"
      for c in data.constants do
        queue := queue.push (m, false, fromSpec, false, c.name)
    else if m == `Core.Assumptions then
      let some data := trEnv.header.moduleData[i]? | continue
      for c in data.constants do
        if c matches .axiomInfo _ && !allowedAxioms.contains c.name then
          errs := errs.push s!"TRUSTED_CLOSURE_AXIOM_FORBIDDEN: {c.name} in {m}"
        if (c matches .opaqueInfo _ || (getExternAttrData? trEnv c.name).isSome) &&
            !(isAllowedCoreInitDecl m c.name && (c matches .opaqueInfo _) && (getExternAttrData? trEnv c.name).isNone) then
          errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_EXTERN: {c.name} in {m}"
        if let .defnInfo v := c then
          if v.safety != .safe then
            if !(← isAllowedCompilerUnsafeDef trEnv c.name v) then
              errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_UNSAFE_DEF: {c.name} in {m}"
  while !queue.isEmpty do
    let (originMod, inStdImpl, fromSpecTests, viaExternMod, cName) := queue.back!
    queue := queue.pop
    if visited.contains (cName, inStdImpl, fromSpecTests, viaExternMod) then
      continue
    visited := visited.insert (cName, inStdImpl, fromSpecTests, viaExternMod)
    let some cinfo := trEnv.find? cName | continue
    if cinfo matches .axiomInfo _ then
      if !allowedAxioms.contains cName && !(inStdImpl && cName == `lcProof) then
        errs := errs.push s!"TRUSTED_CLOSURE_AXIOM_FORBIDDEN: {cName} reachable from {originMod}"
      continue
    let cMod := trEnv.getModuleIdxFor? cName |>.bind (trEnv.header.moduleNames[·]?) |>.getD .anonymous
    if cMod == `Core.Assumptions && fromSpecTests then
      continue
    let projMod := isProjectModule cMod
    let nextViaExt := if projMod then (cMod == externMod) else viaExternMod
    if let some impl := Lean.Compiler.getImplementedBy? trEnv cName then
      let nextStd := inStdImpl || !projMod
      if !visited.contains (impl, nextStd, fromSpecTests, nextViaExt) then
        queue := queue.push (originMod, nextStd, fromSpecTests, nextViaExt, impl)
      if projMod then
        if !(← isCompilerGeneratedCtorIdx trEnv cName impl cinfo) then
          errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_IMPL_BY: {cName} -> {impl} in {cMod} reachable from {originMod}"
    if let some entry := csimpState.map.find? cName then
      let nextStd := inStdImpl || !projMod
      if !visited.contains (entry.toDeclName, nextStd, fromSpecTests, nextViaExt) then
        queue := queue.push (originMod, nextStd, fromSpecTests, nextViaExt, entry.toDeclName)
      let thmMod := trEnv.getModuleIdxFor? entry.thmName |>.bind (trEnv.header.moduleNames[·]?) |>.getD .anonymous
      let toMod := trEnv.getModuleIdxFor? entry.toDeclName |>.bind (trEnv.header.moduleNames[·]?) |>.getD .anonymous
      if projMod || isProjectModule thmMod || isProjectModule toMod then
        errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_CSIMP: {cName} -> {entry.toDeclName} (thm={entry.thmName}) reachable from {originMod}"
    if projMod then
      if !isAllowedMod cMod then
        errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_MODULE: {cName} in {cMod} reachable from {originMod}"
      if let .defnInfo v := cinfo then
        if v.safety != .safe then
          if !(← isAllowedCompilerUnsafeDef trEnv cName v) then
            errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_UNSAFE_DEF: {cName} in {cMod} reachable from {originMod}"
      if cinfo matches .opaqueInfo _ || (getExternAttrData? trEnv cName).isSome then
        let userName := privateToUserName? cName |>.getD cName
        let isAllowedCoreInit :=
          (isAllowedCoreInitDecl cMod cName || (allowStdSyncMutex && isAllowedSqliteInitDecl cMod cName)) &&
          (cinfo matches .opaqueInfo _) &&
          (getExternAttrData? trEnv cName).isNone
        let isRawFdPointed :=
          seedLinuxCommon &&
          cMod == `LeanSwe.LinuxSyscall.Common.Types &&
          userName == `LeanSwe.LinuxSyscall.RawFdPointed &&
          (getExternAttrData? trEnv cName).isNone
        let isRawSqlitePointed :=
          allowStdSyncMutex &&
          cMod == `LeanSwe.Sqlite.Raw.Types &&
          (userName == `LeanSwe.Sqlite.Raw.RawDbExtPointed ||
            userName == `LeanSwe.Sqlite.Raw.RawStmtExtPointed) &&
          (getExternAttrData? trEnv cName).isNone
        let isExpectedInterfaceExtern :=
          cMod == externMod &&
          (!(allowIO || allowStdSyncMutex) || isPrivateName cName) &&
          (cinfo matches .opaqueInfo _) &&
          (cinfo.type.getUsedConstants.contains ``BaseIO ||
            (allowIO && cinfo.type.getUsedConstants.contains ``IO && isPrivateName cName)) &&
          match allowedExternSyms.get? userName, getExternAttrData? trEnv cName with
          | some expectedSym, some extData => extData.entries == [.standard `all expectedSym]
          | _, _ => false
        if !isAllowedCoreInit && !isRawFdPointed && !isRawSqlitePointed && !isExpectedInterfaceExtern then
          errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_EXTERN: {cName} in {cMod} reachable from {originMod}"
    else if let some extData := getExternAttrData? trEnv cName then
      if !(allowStdSyncMutex && viaExternMod && isAllowedSqliteStdMutexOrRef cName extData) &&
          isForbiddenHostExtern cName cinfo extData then
        errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_HOST_IO_EXTERN: {cName} in {cMod} reachable from {originMod}"
    for u in cinfo.type.getUsedConstants do
      if !visited.contains (u, inStdImpl, fromSpecTests, nextViaExt) then
        queue := queue.push (originMod, inStdImpl, fromSpecTests, nextViaExt, u)
    let val? := match cinfo with
      | .defnInfo v => some v.value
      | .thmInfo v => some v.value
      | .opaqueInfo v => some v.value
      | _ => none
    if let some val := val? then
      for u in val.getUsedConstants do
        if !visited.contains (u, inStdImpl, fromSpecTests, nextViaExt) then
          queue := queue.push (originMod, inStdImpl, fromSpecTests, nextViaExt, u)
    let extra : List Name := match cinfo with
      | .ctorInfo v => [v.induct]
      | .recInfo v => v.all
      | .inductInfo v => v.all ++ v.ctors
      | _ => []
    for u in extra do
      if !visited.contains (u, inStdImpl, fromSpecTests, nextViaExt) then
        queue := queue.push (originMod, inStdImpl, fromSpecTests, nextViaExt, u)
  trEnv.freeRegions
  return errs

private def returnsBaseIO (env : Environment) (ty : Expr) : IO Bool := do
  let ctx : Core.Context := { fileName := "<CheckPromises>", fileMap := default }
  let state : Core.State := { env }
  let (res, _) ← (Meta.MetaM.run' do
    Meta.forallTelescope ty fun _ body => do
      let raw := body.consumeMData
      if raw.getAppFn == .const ``BaseIO [] then
        return true
      let b ← Meta.whnf raw
      return b.isAppOfArity ``EIO 2 && b.appFn!.appArg!.consumeMData == .const ``Empty []
  ).toIO ctx state
  return res

private partial def etaReduceExpr (e : Expr) : Expr :=
  let cur := e.consumeMData
  match cur with
  | .lam n ty body bi =>
    let body' := (etaReduceExpr body).consumeMData
    match body' with
    | .app fn (.bvar 0) =>
      let fn' := fn.consumeMData
      if !fn'.hasLooseBVar 0 then
        etaReduceExpr (fn'.lowerLooseBVars 1 1)
      else
        .lam n ty body' bi
    | _ => .lam n ty body' bi
  | _ => cur

private def checkDnsInterfaceWiring (trEnv : Environment) : IO (Array String) := do
  let mut errs : Array String := #[]
  let ifaceMod : Name := `LeanSwe.LinuxSyscall.Dns.Interface
  let some ifaceIdx := trEnv.header.moduleNames.findIdx? (· == ifaceMod)
    | return #[s!"TRUSTED_CLOSURE_DNS_WIRING: missing module {ifaceMod}"]
  let some ifaceData := trEnv.header.moduleData[ifaceIdx]?
    | return #[s!"TRUSTED_CLOSURE_DNS_WIRING: missing moduleData for {ifaceMod}"]
  let findByUser (target : Name) : Array ConstantInfo :=
    ifaceData.constants.filter fun c =>
      ((privateToUserName? c.name).getD c.name) == target
  let rawCands := findByUser `LeanSwe.LinuxSyscall.Dns.rawGetaddrinfo
  let mut rawName? : Option Name := none
  if rawCands.size != 1 then
    errs := errs.push s!"TRUSTED_CLOSURE_DNS_WIRING: expected 1 rawGetaddrinfo in {ifaceMod}, found {rawCands.size}"
  else if let some rc := rawCands[0]? then
    if !isPrivateName rc.name then
      errs := errs.push s!"TRUSTED_CLOSURE_DNS_WIRING: rawGetaddrinfo ({rc.name}) must be private"
    else if !(rc matches .opaqueInfo _) then
      errs := errs.push s!"TRUSTED_CLOSURE_DNS_WIRING: rawGetaddrinfo ({rc.name}) must be opaque"
    else
      match getExternAttrData? trEnv rc.name with
      | some ed =>
        if ed.entries != [.standard `all "leanswe_sys_getaddrinfo"] then
          errs := errs.push s!"TRUSTED_CLOSURE_DNS_WIRING: rawGetaddrinfo extern mismatch"
        if !(← returnsBaseIO trEnv rc.type) then
          errs := errs.push s!"TRUSTED_CLOSURE_DNS_WIRING: rawGetaddrinfo must return BaseIO"
        rawName? := some rc.name
      | none =>
        errs := errs.push s!"TRUSTED_CLOSURE_DNS_WIRING: rawGetaddrinfo missing @[extern]"
  let posixCands := findByUser `LeanSwe.LinuxSyscall.Dns.posixDnsOpsBase
  let mut posixName? : Option Name := none
  if posixCands.size != 1 then
    errs := errs.push s!"TRUSTED_CLOSURE_DNS_WIRING: expected 1 posixDnsOpsBase in {ifaceMod}, found {posixCands.size}"
  else if let some pc := posixCands[0]? then
    if !isPrivateName pc.name then
      errs := errs.push s!"TRUSTED_CLOSURE_DNS_WIRING: posixDnsOpsBase ({pc.name}) must be private"
    else if let .defnInfo dv := pc then
      if dv.safety != .safe then
        errs := errs.push s!"TRUSTED_CLOSURE_DNS_WIRING: posixDnsOpsBase must be safe"
      else if let some rawName := rawName? then
        let v := dv.value.consumeMData
        if v.isAppOfArity `LeanSwe.LinuxSyscall.Dns.Internal.PosixDnsOpsM.mk 2 &&
            v.appFn!.appArg!.consumeMData.isConstOf ``BaseIO &&
            (etaReduceExpr v.appArg!).isConstOf rawName then
          posixName? := some pc.name
        else
          errs := errs.push s!"TRUSTED_CLOSURE_DNS_WIRING: posixDnsOpsBase must wrap rawGetaddrinfo directly"
    else
      errs := errs.push s!"TRUSTED_CLOSURE_DNS_WIRING: posixDnsOpsBase must be def"
  match trEnv.find? `LeanSwe.LinuxSyscall.Dns.defaultOpsBase with
  | some (.defnInfo dv) =>
    if dv.safety != .safe then
      errs := errs.push "TRUSTED_CLOSURE_DNS_WIRING: defaultOpsBase must be safe"
    else if let some posixName := posixName? then
      let v := dv.value.consumeMData
      if !(v.isAppOfArity `LeanSwe.LinuxSyscall.Dns.Internal.mkDnsOpsM 3 &&
          v.appFn!.appFn!.appArg!.consumeMData.isConstOf ``BaseIO &&
          (etaReduceExpr v.appArg!).isConstOf posixName) then
        errs := errs.push "TRUSTED_CLOSURE_DNS_WIRING: defaultOpsBase must apply Internal.mkDnsOpsM to posixDnsOpsBase"
  | _ =>
    errs := errs.push "TRUSTED_CLOSURE_DNS_WIRING: missing defaultOpsBase"
  match trEnv.find? `LeanSwe.LinuxSyscall.Dns.defaultOps with
  | some (.defnInfo dv) =>
    if dv.safety != .safe then
      errs := errs.push "TRUSTED_CLOSURE_DNS_WIRING: defaultOps must be safe"
    else
      let v := dv.value.consumeMData
      let okDefaultOps :=
        if v.isAppOfArity `LeanSwe.LinuxSyscall.Dns.DnsOpsM.mk 2 &&
            v.appFn!.appArg!.consumeMData.isConstOf ``IO then
          match v.appArg!.consumeMData with
          | .lam hn hty (.lam fn fty body fbi) hbi =>
            let b := body.consumeMData
            if b.isAppOfArity `liftM 5 &&
                b.appFn!.appFn!.appFn!.appFn!.appArg!.consumeMData.isConstOf ``BaseIO &&
                b.appFn!.appFn!.appFn!.appArg!.consumeMData.isConstOf ``IO then
              let lifted := etaReduceExpr (.lam hn hty (.lam fn fty b.appArg! fbi) hbi)
              lifted.isAppOfArity `LeanSwe.LinuxSyscall.Dns.DnsOpsM.getaddrinfo 2 &&
                lifted.appFn!.appArg!.consumeMData.isConstOf ``BaseIO &&
                lifted.appArg!.consumeMData.isConstOf `LeanSwe.LinuxSyscall.Dns.defaultOpsBase
            else
              false
          | _ => false
        else
          false
      if !okDefaultOps then
        errs := errs.push "TRUSTED_CLOSURE_DNS_WIRING: defaultOps must lift defaultOpsBase.getaddrinfo directly"
  | _ =>
    errs := errs.push "TRUSTED_CLOSURE_DNS_WIRING: missing defaultOps"
  match trEnv.find? `LeanSwe.LinuxSyscall.Dns.getaddrinfo with
  | some (.defnInfo dv) =>
    if dv.safety != .safe then
      errs := errs.push "TRUSTED_CLOSURE_DNS_WIRING: getaddrinfo must be safe"
    else
      let reduced := etaReduceExpr dv.value
      if !(reduced.isAppOfArity `LeanSwe.LinuxSyscall.Dns.DnsOpsM.getaddrinfo 2 &&
          reduced.appFn!.appArg!.consumeMData.isConstOf ``IO &&
          reduced.appArg!.consumeMData.isConstOf `LeanSwe.LinuxSyscall.Dns.defaultOps) then
        errs := errs.push "TRUSTED_CLOSURE_DNS_WIRING: getaddrinfo must delegate directly to defaultOps.getaddrinfo"
  | _ =>
    errs := errs.push "TRUSTED_CLOSURE_DNS_WIRING: missing getaddrinfo"
  return errs

private def sandboxAuditModules : Array Name := #[
  `LeanSwe.LinuxSyscall.Sandbox.Types,
  `LeanSwe.LinuxSyscall.Sandbox.Model,
  `LeanSwe.LinuxSyscall.Sandbox.Impl,
  `LeanSwe.LinuxSyscall.Sandbox.Interface,
  `LeanSwe.LinuxSyscall.Sandbox.SpecTests,
  `LeanSwe.LinuxSyscall.Sandbox.Proofs
]

private def isAllowedSandboxClosureModule (m : Name) : Bool :=
  m.getRoot == `Core ||
    m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Common] ||
    (m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Sandbox] &&
      m != `LeanSwe.LinuxSyscall.Sandbox.RuntimeTests &&
      m != `LeanSwe.LinuxSyscall.Sandbox.SpecMutants)

private def isSandboxStandardLibModule (m : Name) : Bool :=
  let r := m.getRoot
  (r == `Init || r == `Std) && !m.toString.startsWith "Std.Internal.UV"

private def allowedSandboxExternSyms : Std.HashMap Name String :=
  Std.HashMap.emptyWithCapacity 16
    |>.insert `LeanSwe.LinuxSyscall.Sandbox.rawLandlockQuery "leanswe_sys_landlock_query"
    |>.insert `LeanSwe.LinuxSyscall.Sandbox.rawLandlockCreate "leanswe_sys_landlock_create"
    |>.insert `LeanSwe.LinuxSyscall.Sandbox.rawLandlockAddPathBeneath "leanswe_sys_landlock_add_path_beneath"
    |>.insert `LeanSwe.LinuxSyscall.Sandbox.rawLandlockAddNetPort "leanswe_sys_landlock_add_net_port"
    |>.insert `LeanSwe.LinuxSyscall.Sandbox.rawLandlockRestrictSelf "leanswe_sys_landlock_restrict_self"
    |>.insert `LeanSwe.LinuxSyscall.Sandbox.rawSeccompGetActionAvail "leanswe_sys_seccomp_get_action_avail"
    |>.insert `LeanSwe.LinuxSyscall.Sandbox.rawSeccompSetFilter "leanswe_sys_seccomp_set_filter"
    |>.insert `LeanSwe.LinuxSyscall.Sandbox.rawPrctl "leanswe_sys_prctl"
    |>.insert `LeanSwe.LinuxSyscall.Sandbox.rawSetrlimit "leanswe_sys_setrlimit"
    |>.insert `LeanSwe.LinuxSyscall.Sandbox.rawMemfdCreate "leanswe_sys_memfd_create"

private def isExactStandardExtern (extData? : Option ExternAttrData) (expectedSym : String) : Bool :=
  match extData? with
  | some data =>
    match data.entries with
    | [.standard backend sym] => backend == `all && sym == expectedSym
    | _ => false
  | none => false

private def isPropInductiveType : Expr → Bool
  | .sort .zero => true
  | .forallE _ _ b _ => isPropInductiveType b
  | _ => false

private unsafe def checkSandboxTrustedClosure (env : Environment) : IO (Array String) := do
  let mut discoveredMods : Array Name := #[]
  for m in env.header.moduleNames do
    let s := m.toString
    if ((s == "LeanSwe.LinuxSyscall.Sandbox" || s.startsWith "LeanSwe.LinuxSyscall.Sandbox.") &&
          s != "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests" &&
          s != "LeanSwe.LinuxSyscall.Sandbox.SpecMutants") ||
        s.startsWith "LeanSwe.LinuxSyscall.Common." then
      discoveredMods := discoveredMods.push m
  for reqMod in sandboxAuditModules do
    if !discoveredMods.contains reqMod then
      discoveredMods := discoveredMods.push reqMod
  enableInitializersExecution
  let sbxEnv ← importModules (discoveredMods.map fun m => { module := m }) {} (loadExts := true)
  let csimpState := Lean.Compiler.CSimp.ext.getState sbxEnv
  let mut errs : Array String := #[]
  for m in sbxEnv.header.moduleNames do
    if !isSandboxStandardLibModule m && !isAllowedSandboxClosureModule m then
      errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_IMPORT: {m} imported into Sandbox closure"
  for (origName, csEntry) in csimpState.map.toList do
    let thmMod := sbxEnv.getModuleIdxFor? csEntry.thmName |>.bind (sbxEnv.header.moduleNames[·]?) |>.getD .anonymous
    if isProjectModule thmMod then
      errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_CSIMP: {origName} csimp->{csEntry.toDeclName} via {csEntry.thmName} in {thmMod}"
  let mut visited : Std.HashSet Name := {}
  let mut queue : Array (Name × Name) := #[]
  for h : i in [0 : sbxEnv.header.moduleNames.size] do
    let m := sbxEnv.header.moduleNames[i]
    if discoveredMods.contains m then
      let some data := sbxEnv.header.moduleData[i]? | continue
      for c in data.constants do
        queue := queue.push (m, c.name)
  while !queue.isEmpty do
    let (originMod, cName) := queue.back!
    queue := queue.pop
    if visited.contains cName then
      continue
    visited := visited.insert cName
    let some cinfo := sbxEnv.find? cName | continue
    if cinfo matches .axiomInfo _ then
      if !allowedAxioms.contains cName then
        errs := errs.push s!"TRUSTED_CLOSURE_AXIOM_FORBIDDEN: {cName} reachable from {originMod}"
      continue
    let cMod := sbxEnv.getModuleIdxFor? cName |>.bind (sbxEnv.header.moduleNames[·]?) |>.getD .anonymous
    if isSandboxStandardLibModule cMod then
      let extData? := getExternAttrData? sbxEnv cName
      if extData?.isSome || cinfo matches .opaqueInfo _ then
        let cs := cName.toString
        if (cs.startsWith "IO." || cs.startsWith "System.") && cName != `IO.RealWorld.nonemptyType then
          errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_STDLIB_IO: {cName} in {cMod} reachable from {originMod}"
      if let some ed := extData? then
        let badSyms := ["lean_io_", "lean_uv_", "lean_dbg_", "lean_process_", "lean_st_", "lean_task_"]
        for ent in ed.entries do
          let sym := match ent with
            | .standard _ s => s | .inline _ s => s | .opaque => "" | .adhoc _ => ""
          if badSyms.any (sym.startsWith ·) then
            errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_STDLIB_EXTERN: {cName} ({sym}) in {cMod} reachable from {originMod}"
    else if cMod != .anonymous then
      if !isAllowedSandboxClosureModule cMod then
        errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_MODULE: {cName} in {cMod} reachable from {originMod}"
      if let some implName := Lean.Compiler.getImplementedBy? sbxEnv cName then
        let isCtorIdxImpl :=
          cName.isStr && cName.getString! == "ctorIdx" &&
          implName == Name.str cName "_impl" &&
          (match sbxEnv.find? cName.getPrefix, sbxEnv.find? implName with
           | some (.inductInfo iv), some (.defnInfo implVal) =>
             let ivMod := sbxEnv.getModuleIdxFor? iv.name |>.bind (sbxEnv.header.moduleNames[·]?) |>.getD .anonymous
             !isPropInductiveType iv.type && cMod == ivMod &&
               implVal.value.getUsedConstants.all (fun u =>
                 let uMod := sbxEnv.getModuleIdxFor? u |>.bind (sbxEnv.header.moduleNames[·]?) |>.getD .anonymous
                 isSandboxStandardLibModule uMod || u == `optParam ||
                   u == `LeanSwe.LinuxSyscall.RawFd ||
                   (match sbxEnv.find? u with | some (.inductInfo _) => true | _ => false))
           | _, _ => false)
        if !isCtorIdxImpl then
          errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_IMPLEMENTED_BY: {cName} in {cMod} implemented_by {implName}"
        if !visited.contains implName then
          queue := queue.push (originMod, implName)
      if let some csEntry := csimpState.map.find? cName then
        errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_CSIMP: {cName} in {cMod} csimp->{csEntry.toDeclName} via {csEntry.thmName}"
        if !visited.contains csEntry.toDeclName then
          queue := queue.push (originMod, csEntry.toDeclName)
      if csimpState.thmNames.contains cName then
        errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_CSIMP_THM: {cName} in {cMod} marked @[csimp]"
      let extData? := getExternAttrData? sbxEnv cName
      if cinfo matches .opaqueInfo _ || extData?.isSome then
        let userName := (privateToUserName? cName).getD cName
        let isRawFdPointed :=
          cMod == `LeanSwe.LinuxSyscall.Common.Types &&
          userName == `LeanSwe.LinuxSyscall.RawFdPointed &&
          extData?.isNone
        let isAllowedSandboxExtern :=
          cMod == `LeanSwe.LinuxSyscall.Sandbox.Interface &&
          (cinfo matches .opaqueInfo _) &&
          match allowedSandboxExternSyms.get? userName with
          | some expectedSym => isExactStandardExtern extData? expectedSym
          | none => false
        if !isRawFdPointed && !isAllowedSandboxExtern then
          errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_EXTERN: {cName} in {cMod} reachable from {originMod}"
    for u in cinfo.type.getUsedConstants do
      if !visited.contains u then
        queue := queue.push (originMod, u)
    let val? := match cinfo with
      | .defnInfo v => some v.value
      | .thmInfo v => some v.value
      | .opaqueInfo v => some v.value
      | _ => none
    if let some val := val? then
      for u in val.getUsedConstants do
        if !visited.contains u then
          queue := queue.push (originMod, u)
    let extra : List Name := match cinfo with
      | .ctorInfo v => [v.induct]
      | .recInfo v => v.all
      | .inductInfo v => v.all ++ v.ctors
      | _ => []
    for u in extra do
      if !visited.contains u then
        queue := queue.push (originMod, u)
  let mut modImports : Std.HashMap Name (Array Name) := {}
  for h : i in [0 : sbxEnv.header.moduleNames.size] do
    let m := sbxEnv.header.moduleNames[i]
    if let some data := sbxEnv.header.moduleData[i]? then
      modImports := modImports.insert m (data.imports.map (·.module))
  let isSandboxClosureAllowed (imp : Name) : Bool :=
    isSandboxStandardLibModule imp || isAllowedSandboxClosureModule imp
  let mut sandboxQueue : Array Name := #[]
  let mut sandboxSeen : Std.HashSet Name := {}
  for m in discoveredMods do
    sandboxQueue := sandboxQueue.push m
    sandboxSeen := sandboxSeen.insert m
  let mut qIdx : Nat := 0
  while hq : qIdx < sandboxQueue.size do
    let cur := sandboxQueue[qIdx]
    qIdx := qIdx + 1
    for imp in modImports.getD cur #[] do
      if !isSandboxClosureAllowed imp then
        errs := errs.push s!"TRUSTED_CLOSURE_VIOLATION: {cur} imports forbidden {imp}"
      else if !sandboxSeen.contains imp then
        sandboxSeen := sandboxSeen.insert imp
        sandboxQueue := sandboxQueue.push imp
  IO.println s!"TRUSTED_CLOSURE: sandbox_modules={sandboxSeen.size} discovered={discoveredMods.size} allowlist=Common+Sandbox externs={allowedSandboxExternSyms.size}"
  sbxEnv.freeRegions
  return errs

private def isAllowedGitDirectImport (srcMod imp : Name) : Bool :=
  if !isProjectModule imp then isAllowedProjectDirectImport srcMod imp
  else if imp.getRoot == `Core then true
  else match srcMod with
  | `LeanSwe.Git.Types => false
  | `LeanSwe.Git.Model => imp == `LeanSwe.Git.Types
  | `LeanSwe.Git.Impl => imp == `LeanSwe.Git.Types || imp == `LeanSwe.Git.Model
  | `LeanSwe.Git.Interface =>
    imp ∈ [`LeanSwe.Git.Types, `LeanSwe.Git.Model, `LeanSwe.Git.Impl,
      `LeanSwe.Process.Types, `LeanSwe.Process.Interface, `LeanSwe.EnvVars.Types, `LeanSwe.EnvVars.Interface]
  | `LeanSwe.Git.SpecTests => imp ∈ [`LeanSwe.Git.Types, `LeanSwe.Git.Model, `LeanSwe.Git.Impl, `LeanSwe.Git.Interface]
  | _ => if srcMod == `LeanSwe.Git.Proofs || srcMod.components.contains `Proofs then
      let p := imp.components.take 2; p == [`LeanSwe, `Git] || p == [`LeanSwe, `Process] || p == [`LeanSwe, `EnvVars]
    else false

private def checkGitTrustedClosure (env : Environment) (extraMods : Array Name) : IO (Array String) := do
  let gitMods := discoverPackageModules env extraMods `LeanSwe.Git
    #[`LeanSwe.Git.Types, `LeanSwe.Git.Model, `LeanSwe.Git.Impl, `LeanSwe.Git.Interface, `LeanSwe.Git.SpecTests, `LeanSwe.Git.Proofs]
  let csimpState := Lean.Compiler.CSimp.ext.getState env
  let mut errs : Array String := #[]
  let mut stdVisited : Std.HashSet (Name × Bool) := {}
  let mut stdQueue : Array (Name × Bool × Name) := #[]
  for m in gitMods do
    let some modIdx := env.header.moduleNames.findIdx? (· == m) | do errs := errs.push s!"TRUSTED_CLOSURE_MISSING_GIT_MODULE: {m}"; continue
    let some data := env.header.moduleData[modIdx]? | continue
    for imp in data.imports do
      if !isAllowedGitDirectImport m imp.module then errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_IMPORT: {m} imports {imp.module}"
    for c in data.constants do
      if c matches .opaqueInfo _ || (getExternAttrData? env c.name).isSome then errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_EXTERN: {c.name} in {m}"
      if let some impl := Lean.Compiler.getImplementedBy? env c.name then
        if !(← isCompilerGeneratedCtorIdx env c.name impl c) then errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_IMPL_BY: {c.name} -> {impl} in {m}"
      if let .defnInfo dv := c then
        if dv.safety != .safe && !(← isAllowedCompilerUnsafeDef env c.name dv) then errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_UNSAFE_DEF: {c.name} in {m}"
      for u in c.type.getUsedConstants ++ (c.value?.map (·.getUsedConstants) |>.getD #[]) do
        let uMod := env.getModuleIdxFor? u |>.bind (env.header.moduleNames[·]?) |>.getD .anonymous
        if !isProjectModule uMod then
          if !stdVisited.contains (u, false) then stdQueue := stdQueue.push (m, false, u)
        else if uMod != m && !isAllowedGitDirectImport m uMod &&
            !(m == `LeanSwe.Git.Interface && uMod == `LeanSwe.EnvVars.Raw.Types) then
          errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_REF: {c.name} in {m} references {u} in {uMod}"
        else if m == `LeanSwe.Git.Interface && (uMod == `LeanSwe.Process.Interface || uMod == `LeanSwe.EnvVars.Interface) &&
            u != `LeanSwe.Process.run && u != `LeanSwe.EnvVars.listEnv then
          errs := errs.push s!"TRUSTED_CLOSURE_GIT_WIRING: {c.name} in {m} references {u}"
  while !stdQueue.isEmpty do
    let (originMod, inStdImpl, cName) := stdQueue.back!; stdQueue := stdQueue.pop
    if stdVisited.contains (cName, inStdImpl) then continue
    stdVisited := stdVisited.insert (cName, inStdImpl)
    let some cinfo := env.find? cName | continue
    if cinfo matches .axiomInfo _ then
      if !allowedAxioms.contains cName && !(inStdImpl && cName == `lcProof) then errs := errs.push s!"TRUSTED_CLOSURE_AXIOM_FORBIDDEN: {cName} reachable from {originMod}"
      continue
    let cMod := env.getModuleIdxFor? cName |>.bind (env.header.moduleNames[·]?) |>.getD .anonymous
    if isProjectModule cMod then continue
    if let some impl := Lean.Compiler.getImplementedBy? env cName then
      if !stdVisited.contains (impl, true) then stdQueue := stdQueue.push (originMod, true, impl)
    if let some e := csimpState.map.find? cName then
      if !stdVisited.contains (e.toDeclName, true) then stdQueue := stdQueue.push (originMod, true, e.toDeclName)
    if let some ext := getExternAttrData? env cName then
      if isForbiddenHostExtern cName cinfo ext then errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_HOST_IO_EXTERN: {cName} in {cMod} reachable from {originMod}"
    let extra : List Name := match cinfo with | .ctorInfo v => [v.induct] | .recInfo v => v.all | .inductInfo v => v.all ++ v.ctors | _ => []
    for u in cinfo.type.getUsedConstants ++ (cinfo.value?.map (·.getUsedConstants) |>.getD #[]) ++ extra.toArray do
      if !stdVisited.contains (u, inStdImpl) then stdQueue := stdQueue.push (originMod, inStdImpl, u)
  for fn in [`LeanSwe.Git.defaultRawOps, `LeanSwe.Git.defaultApi] do
    if (env.getModuleIdxFor? fn |>.bind (env.header.moduleNames[·]?)) != some `LeanSwe.Git.Interface || !(env.find? fn matches some (.defnInfo _)) then
      errs := errs.push s!"TRUSTED_CLOSURE_GIT_WIRING: {fn} must be a safe def in LeanSwe.Git.Interface"
  if let some (.defnInfo dv) := env.find? `LeanSwe.Git.defaultApi then
    if !dv.value.consumeMData.getAppFn.consumeMData.isConstOf `LeanSwe.Git.Impl.mkApiM then
      errs := errs.push "TRUSTED_CLOSURE_GIT_WIRING: defaultApi must call LeanSwe.Git.Impl.mkApiM"
  IO.println s!"TRUSTED_CLOSURE: git_modules={gitMods.size} allowlist=Git+Process+EnvVars"
  return errs

private def checkPasswdPrivateWiring (env : Environment) : IO (Array String) := do
  let mut privRawUid? : Option Name := none
  let mut privRawNam? : Option Name := none
  let mut privPosixOps? : Option Name := none
  for h : i in [0 : env.header.moduleNames.size] do
    if env.header.moduleNames[i] == `LeanSwe.LinuxSyscall.Passwd.Interface then
      if let some data := env.header.moduleData[i]? then
        for c in data.constants do
          if isPrivateName c.name then
            match privateToUserName? c.name with
            | some `LeanSwe.LinuxSyscall.Passwd.rawGetpwuidOnce => privRawUid? := some c.name
            | some `LeanSwe.LinuxSyscall.Passwd.rawGetpwnamOnce => privRawNam? := some c.name
            | some `LeanSwe.LinuxSyscall.Passwd.posixPasswdOps => privPosixOps? := some c.name
            | _ => pure ()
  let ctx : Core.Context := { fileName := "<CheckPasswdWiring>", fileMap := default, maxHeartbeats := 0 }
  let state : Core.State := { env }
  let (errs, _) ← (Meta.MetaM.run' do
    let mut wErrs : Array String := #[]
    match privRawUid?, privRawNam?, privPosixOps? with
    | some rawUidName, some rawNamName, some posixOpsName =>
      match env.find? posixOpsName, env.find? `LeanSwe.LinuxSyscall.Passwd.defaultOps with
      | some (.defnInfo pInfo), some (.defnInfo dInfo) =>
        let pWhnf := (← Meta.withTransparency .all (Meta.whnf pInfo.value)).consumeMData
        let pArgs := pWhnf.getAppArgs
        let pOk :=
          pWhnf.getAppFn.constName? == some `LeanSwe.LinuxSyscall.Passwd.Internal.PosixPasswdOpsM.mk &&
          pArgs.size == 3 &&
          pArgs[1]!.consumeMData.constName? == some rawUidName &&
          pArgs[2]!.consumeMData.constName? == some rawNamName
        if !pOk then
          wErrs := wErrs.push "TRUSTED_CLOSURE_INTERFACE_WIRING_MISMATCH: posixPasswdOps does not directly bind (rawGetpwuidOnce, rawGetpwnamOnce)"
        if !dInfo.value.getUsedConstants.contains posixOpsName then
          wErrs := wErrs.push "TRUSTED_CLOSURE_INTERFACE_WIRING_MISMATCH: defaultOps does not reference private posixPasswdOps"
      | _, _ =>
        wErrs := wErrs.push "TRUSTED_CLOSURE_INTERFACE_WIRING_MISMATCH: missing posixPasswdOps or defaultOps definition"
    | _, _, _ =>
      wErrs := wErrs.push "TRUSTED_CLOSURE_INTERFACE_WIRING_MISMATCH: missing private rawGetpwuidOnce/rawGetpwnamOnce/posixPasswdOps in Passwd.Interface"
    return wErrs
  ).toIO ctx state
  return errs

private def unwrapBaseIOLift (e : Expr) : Option Expr :=
  let c := e.consumeMData
  let exp := mkApp5 (mkConst ``instMonadLiftTOfMonadLift [.zero, .zero, .zero, .zero]) (mkConst ``BaseIO) (mkConst ``BaseIO) (mkConst ``IO)
    (mkApp (mkConst ``instMonadLiftBaseIOEIO) (mkConst ``IO.Error)) (mkApp (mkConst ``instMonadLiftT [.zero, .zero]) (mkConst ``BaseIO))
  if c.isAppOfArity ``liftM 5 && c.getAppArgs[0]!.consumeMData.isConstOf ``BaseIO && c.getAppArgs[1]!.consumeMData.isConstOf ``IO && c.getAppArgs[2]!.consumeMData == exp then
    some c.getAppArgs[4]!.consumeMData else none

private def forallBorrowsAndBaseIOErrno (ty : Expr) : Array Bool × Bool := Id.run do
  let mut c := ty.consumeMData
  let mut out : Array Bool := #[]
  while c.isForall do
    let .forallE _ dom body _ := c | break
    out := out.push (Lean.isMarkedBorrowed dom)
    c := body.consumeMData
  return (out, c.isAppOfArity ``BaseIO 1 && c.appArg!.consumeMData.isAppOfArity ``Except 2 && c.appArg!.consumeMData.appFn!.appArg!.consumeMData.isConstOf `LeanSwe.LinuxSyscall.Errno)

private def checkPostForkRuntimeTestsExterns (env : Environment) (consts : Array ConstantInfo) : Array String := Id.run do
  let allowed : Array String := #["rawMkPipeCloexec", "rawCloseFd", "rawWriteOnce", "rawReadOnce", "rawWaitOnce"]
  let mut errs : Array String := #[]
  let mut privRaws : Std.HashSet Name := {}
  for c in consts do
    let ext? := getExternAttrData? env c.name
    if c matches .opaqueInfo _ || ext?.isSome then
      let ok := isPrivateName c.name && (c matches .opaqueInfo _) && match privateToUserName? c.name with
        | some u => u.getPrefix == `LeanSwe.PostFork.RuntimeTests && allowed.contains u.getString! && match postForkExternSpecs.find? (·.1 == Name.str `LeanSwe.PostFork u.getString!) with
          | some (_, sym, _, bs) => let (gb, gc) := forallBorrowsAndBaseIOErrno c.type; isExactStandardExtern ext? sym && bs == gb && gc | none => false
        | none => false
      if ok then privRaws := privRaws.insert c.name else errs := errs.push s!"FORBIDDEN_EXTERN_IN_POSTFORK: {c.name} in LeanSwe.PostFork.RuntimeTests"
    if !isPrivateName c.name && (Lean.declRangeExt.find? env c.name).isSome then
      let s := c.name.getString!
      let okPub := c.name == `LeanSwe.PostFork.RuntimeTests.runAll || c.name == `LeanSwe.PostFork.RuntimeTests.registeredAssumptions ||
        c.name == `LeanSwe.PostFork.RuntimeTests.registeredErrorTests || ((s.startsWith "assume_postfork_" || s.startsWith "err_") && c.name.getPrefix == `LeanSwe.PostFork.RuntimeTests)
      if !okPub || c.type.getUsedConstants.any privRaws.contains || c.type.getUsedConstants.contains `LeanSwe.LinuxSyscall.RawFd then
        errs := errs.push s!"TRUSTED_CLOSURE_PUBLIC_FFI_LEAK: {c.name} in LeanSwe.PostFork.RuntimeTests exposes raw handle/FFI"
  return errs

private def checkPostForkPrivateWiring (env : Environment) : IO (Array String) := do
  let allowPub : Array Name := #[`LeanSwe.PostFork.defaultOps,
    `LeanSwe.PostFork.spawn, `LeanSwe.PostFork.spawnWithBarrier, `LeanSwe.PostFork.releaseBarrier, `LeanSwe.PostFork.abortBarrier]
  let mut privRaw : Std.HashMap Name Name := {}
  let mut privRawSet : Std.HashSet Name := {}
  let mut privPosixOps? : Option Name := none
  let mut ifaceConsts : Array ConstantInfo := #[]
  let mut errs : Array String := #[]
  for h : i in [0 : env.header.moduleNames.size] do
    if env.header.moduleNames[i] == `LeanSwe.PostFork.Interface then
      if let some data := env.header.moduleData[i]? then
        ifaceConsts := data.constants
        for c in data.constants do
          let isUser := (Lean.declRangeExt.find? env c.name).isSome
          if isPrivateName c.name then
            if let some u := privateToUserName? c.name then
              if postForkExternSpecs.any (·.1 == u) then do
                privRaw := privRaw.insert u c.name
                privRawSet := privRawSet.insert c.name
              else if u == `LeanSwe.PostFork.posixHostOps then privPosixOps? := some c.name
              else if isUser then errs := errs.push s!"TRUSTED_CLOSURE_UNEXPECTED_INTERFACE_DECL: unexpected private {c.name} in PostFork.Interface"
          else if (isUser && !allowPub.contains c.name) || (!isUser && (c matches .opaqueInfo _ || (getExternAttrData? env c.name).isSome || (Lean.getExportNameFor? env c.name).isSome)) then
            errs := errs.push s!"TRUSTED_CLOSURE_PUBLIC_FFI_LEAK: unexpected declaration {c.name} in PostFork.Interface"
  let (wErrs, _) ← (Meta.MetaM.run' do
    let mut we := errs
    let mut rawPrivs : Array Name := #[]
    for (u, sym, _, borrows) in postForkExternSpecs do
      match privRaw.get? u with
      | some p =>
        rawPrivs := rawPrivs.push p
        if let some ci := env.find? p then
          let (gotB, gotCod) := forallBorrowsAndBaseIOErrno ci.type
          if !(ci matches .opaqueInfo _) || !isExactStandardExtern (getExternAttrData? env p) sym || borrows != gotB || !gotCod then
            we := we.push s!"TRUSTED_CLOSURE_INTERFACE_WIRING_MISMATCH: {u} extern/borrow/Errno mismatch"
      | none => we := we.push s!"TRUSTED_CLOSURE_INTERFACE_WIRING_MISMATCH: missing private {u} in PostFork.Interface"
    if rawPrivs.size == 9 then
      for c in ifaceConsts do
        if some c.name != privPosixOps? && !privRawSet.contains c.name then
          let used := c.type.getUsedConstants ++ (c.value?.map (·.getUsedConstants) |>.getD #[])
          let okPosix := c.name == `LeanSwe.PostFork.defaultOps || (!(Lean.declRangeExt.find? env c.name).isSome && (c matches .thmInfo _))
          if rawPrivs.any used.contains || (privPosixOps?.any used.contains && !okPosix) then
            we := we.push s!"TRUSTED_CLOSURE_PUBLIC_FFI_LEAK: {c.name} in PostFork.Interface exposes raw FFI"
    match privPosixOps?, rawPrivs.size == 9 with
    | some posixOpsName, true =>
      match env.find? posixOpsName, env.find? `LeanSwe.PostFork.defaultOps with
      | some (.defnInfo pInfo), some (.defnInfo dInfo) =>
        let pWhnf := (← Meta.withTransparency .all (Meta.whnf pInfo.value)).consumeMData
        let pArgs := pWhnf.getAppArgs
        let chkBase (rawP : Name) (ar : Nat) (e : Expr) : Bool := Id.run do
          let mut cur := e.consumeMData
          let mut bs : Array (Name × Expr × BinderInfo) := #[]
          for _ in [0 : ar] do
            let .lam n ty b bi := cur | return false
            bs := bs.push (n, ty, bi)
            cur := b.consumeMData
          let some call := unwrapBaseIOLift cur | return false
          return etaReduceExpr (bs.reverse.foldl (fun acc (n, ty, bi) => .lam n ty acc bi) call) == .const rawP []
        let chkFork (rawP : Name) (e : Expr) : Bool := Id.run do
          let mut cur := e.consumeMData
          for _ in [0 : 11] do
            let .lam _ _ b _ := cur | return false
            cur := b.consumeMData
          let .letE _ _ fv b1 _ := cur | return false
          let rawFd := mkConst `LeanSwe.LinuxSyscall.RawFd
          if fv.consumeMData != mkAppN (mkConst `LeanSwe.PostFork.Impl.Internal.flattenForkArgs) #[rawFd, .bvar 8, .bvar 7, .bvar 6, .bvar 5, .bvar 4, .bvar 1] then return false
          let .letE _ _ iv b2 _ := b1.consumeMData | return false
          if iv.consumeMData != mkApp (mkConst `LeanSwe.PostFork.Impl.Internal.forkModeToUInt32) (.bvar 10) then return false
          let some call := unwrapBaseIOLift b2 | return false
          let pj (s : Name) := mkApp2 (mkConst s) rawFd (.bvar 1)
          return call == mkAppN (mkConst rawP) #[.bvar 12, .bvar 0, pj `LeanSwe.PostFork.Impl.Internal.FlattenedForkArgsM.handles, pj `LeanSwe.PostFork.Impl.Internal.FlattenedForkArgsM.metaSlots, pj `LeanSwe.PostFork.Impl.Internal.FlattenedForkArgsM.closeSlots, pj `LeanSwe.PostFork.Impl.Internal.FlattenedForkArgsM.keepSlots, pj `LeanSwe.PostFork.Impl.Internal.FlattenedForkArgsM.argPrefixes, pj `LeanSwe.PostFork.Impl.Internal.FlattenedForkArgsM.argSuffixes, pj `LeanSwe.PostFork.Impl.Internal.FlattenedForkArgsM.argSlots, .bvar 5, .bvar 4, .bvar 2]
        let pOk := pInfo.safety == .safe && pWhnf.getAppFn.constName? == some `LeanSwe.PostFork.Impl.Internal.PosixHostOpsM.mk && pArgs.size == 11 && pArgs[0]!.consumeMData.isConstOf ``IO && pArgs[1]!.consumeMData.isConstOf `LeanSwe.LinuxSyscall.RawFd && ((List.range 8).all fun i => chkBase rawPrivs[i]! postForkExternSpecs[i]!.2.2.1 pArgs[2 + i]!) && chkFork rawPrivs[8]! pArgs[10]!
        let dArgs := dInfo.value.consumeMData.getAppArgs
        if !pOk || dInfo.safety != .safe || dInfo.type.consumeMData != mkConst `LeanSwe.PostFork.PostForkOps || dInfo.value.consumeMData.getAppFn.constName? != some `LeanSwe.PostFork.Impl.Internal.mkHostOps || dArgs.size != 5 || dArgs[3]!.consumeMData.constName? != some posixOpsName then
          we := we.push "TRUSTED_CLOSURE_INTERFACE_WIRING_MISMATCH: posixHostOps/defaultOps wiring mismatch"
      | _, _ => we := we.push "TRUSTED_CLOSURE_INTERFACE_WIRING_MISMATCH: missing posixHostOps or defaultOps"
    | _, _ => we := we.push "TRUSTED_CLOSURE_INTERFACE_WIRING_MISMATCH: missing private posixHostOps in PostFork.Interface"
    for (w, p) in #[(`LeanSwe.PostFork.spawn, `LeanSwe.PostFork.PostForkOpsM.spawn), (`LeanSwe.PostFork.spawnWithBarrier, `LeanSwe.PostFork.PostForkOpsM.spawnWithBarrier), (`LeanSwe.PostFork.releaseBarrier, `LeanSwe.PostFork.PostForkOpsM.releaseBarrier), (`LeanSwe.PostFork.abortBarrier, `LeanSwe.PostFork.PostForkOpsM.abortBarrier)] do
      match env.find? w with
      | some (.defnInfo wv) => if wv.safety != .safe || etaReduceExpr wv.value != mkApp3 (mkConst p) (mkConst ``IO) (mkConst `LeanSwe.LinuxSyscall.RawFd) (mkConst `LeanSwe.PostFork.defaultOps) then we := we.push s!"TRUSTED_CLOSURE_INTERFACE_WIRING_MISMATCH: {w} does not safely delegate to defaultOps"
      | _ => we := we.push s!"TRUSTED_CLOSURE_INTERFACE_WIRING_MISMATCH: missing public wrapper {w}"
    return we
  ).toIO { fileName := "<CheckPostForkWiring>", fileMap := default, maxHeartbeats := 0 } { env }
  return wErrs

private def checkPostForkAeneasWiring (env : Environment) : Array String := Id.run do
  let targets : Array Name := #[`postfork.child.encode_failure_report, `postfork.child.validate_child_args, `postfork.fd_ops.clear_cloexec, `postfork.fd_ops.set_cloexec, `postfork.fd_ops.relocate_rep_above2, `postfork.fd_ops.setup_stdio, `postfork.fd_ops.close_fds_above2_except, `postfork.fd_ops.parse_dirent_name, `postfork.child.read_sync_byte, `postfork.child.write_all, `postfork.child.run_child]
  let apiConst := `LeanSwe.PostFork.Aeneas.rustAeneasApi
  let some (.defnInfo dv) := env.find? apiConst | return #[s!"TRUSTED_CLOSURE_AENEAS_WIRING_MISMATCH: missing {apiConst}"]
  let v := dv.value.consumeMData
  let args := v.getAppArgs
  if dv.safety != .safe || dv.type.consumeMData != mkConst `LeanSwe.PostFork.Aeneas.PostForkAeneasApi || v.getAppFn.constName? != some `LeanSwe.PostFork.Aeneas.PostForkAeneasApi.mk || args.size != targets.size then
    return #[s!"TRUSTED_CLOSURE_AENEAS_WIRING_MISMATCH: invalid {apiConst}"]
  let mut errs : Array String := #[]
  for i in [0 : targets.size] do
    let exp := targets[i]!
    let tm := env.getModuleIdxFor? exp |>.bind (env.header.moduleNames[·]?) |>.getD .anonymous
    if etaReduceExpr args[i]! != mkConst exp || tm != `LeanSwe.PostFork.Aeneas.Funs || (getExternAttrData? env exp).isSome || (Lean.Compiler.getImplementedBy? env exp).isSome then
      errs := errs.push s!"TRUSTED_CLOSURE_AENEAS_WIRING_MISMATCH: {apiConst} field #{i} mismatch ({exp})"
  return errs

private def canonicalManagedProcessTargets : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity 10
    |>.insert `LeanSwe.Process.defaultApi
    |>.insert `LeanSwe.Process.Proofs.healthySimApi
    |>.insert `LeanSwe.Process.Internal.mkApiM
    |>.insert `LeanSwe.Process.SysBridge.resolveExecutablePath
    |>.insert `LeanSwe.Process.SysBridge.validateWorkingDir
    |>.insert `LeanSwe.Process.SysBridge.streamPipesLoop
    |>.insert `LeanSwe.Process.SysBridge.mkRawOpsM
    |>.insert `LeanSwe.Process.SysBridge.spawnPure

private def hasCanonicalProcessPromiseTarget (prog : Expr) : Bool :=
  let args := prog.consumeMData.getAppArgs
  if args.isEmpty then
    false
  else
    let tgt := (etaReduceExpr args.back!).consumeMData.getAppFn.consumeMData
    match tgt with
    | .const tName _ => canonicalManagedProcessTargets.contains tName
    | _ => false

private def hasCanonicalPromiseTarget (fn : Name) (prog : Expr) : MetaM Bool := do
  if fn.getPrefix == `LeanSwe.Process then
    return hasCanonicalProcessPromiseTarget prog
  if fn.getPrefix != `LeanSwe.PostFork then return true
  let pa := prog.getAppArgs
  let chkMock (e : Expr) : MetaM Bool := do
    let .lam _ _ b _ := e.consumeMData | return false
    let ba := b.consumeMData.getAppArgs
    let ms := mkConst `LeanSwe.PostFork.HostMockState
    if b.consumeMData.getAppFn.constName? != some `LeanSwe.PostFork.Impl.Internal.mkHostOps || ba.size != 5 || !ba[2]!.consumeMData.isConstOf ``Int32 || ba[3]!.consumeMData != .bvar 0 || ba[0]!.consumeMData != mkApp (mkConst ``StateM [.zero]) ms || ba[1]!.consumeMData != mkApp3 (mkConst ``StateT.instMonad [.zero, .zero]) ms (mkConst ``Id [.zero]) (mkConst ``Id.instMonad [.zero]) then return false
    return (← Meta.withTransparency .all (Meta.whnf ba[4]!)).rawNatLit? == some 18
  if fn == `LeanSwe.PostFork.test_postfork_hostOps_validationBarrierEintrAndWire then return pa.size == 3 && (← chkMock pa[2]!)
  else if fn == `LeanSwe.PostFork.test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter then return pa.size == 5 && etaReduceExpr pa[2]! == mkApp (mkConst `LeanSwe.PostFork.Impl.Internal.flattenForkArgs) (mkConst ``Int32) && etaReduceExpr pa[3]! == mkConst `LeanSwe.PostFork.Impl.Internal.forkModeToUInt32 && (← chkMock pa[4]!)
  else return pa.size == 3 && pa[2]!.consumeMData == mkConst `LeanSwe.PostFork.Aeneas.rustAeneasApi

private structure AxCache where
  safe : Std.HashSet Name := {}
  bad : Std.HashMap Name Name := {}
  inStack : Std.HashSet Name := {}

private partial def findBadAxiom (env : Environment) (cName : Name) : StateM AxCache (Option Name) := do
  if allowedAxioms.contains cName then return none
  let st ← get
  if st.safe.contains cName || st.inStack.contains cName then return none
  if let some b := st.bad.get? cName then return some b
  let some cinfo := env.find? cName | do
    modify fun s => { s with safe := s.safe.insert cName }
    return none
  if cinfo matches .axiomInfo _ then
    modify fun s => { s with bad := s.bad.insert cName cName }
    return some cName
  modify fun s => { s with inStack := s.inStack.insert cName }
  let mut foundBad : Option Name := none
  for u in cinfo.type.getUsedConstants do
    if let some b ← findBadAxiom env u then
      foundBad := some b
      break
  if foundBad.isNone then
    let val? := match cinfo with
      | .defnInfo v => some v.value
      | .thmInfo v => some v.value
      | .opaqueInfo v => some v.value
      | _ => none
    if let some val := val? then
      for u in val.getUsedConstants do
        if let some b ← findBadAxiom env u then
          foundBad := some b
          break
  if foundBad.isNone then
    let extra : List Name := match cinfo with
      | .ctorInfo v => [v.induct]
      | .recInfo v => v.all
      | .inductInfo v => v.all ++ v.ctors
      | _ => []
    for u in extra do
      if let some b ← findBadAxiom env u then
        foundBad := some b
        break
  modify fun s => { s with inStack := s.inStack.erase cName }
  if let some b := foundBad then
    modify fun s => { s with bad := s.bad.insert cName b }
    return some b
  modify fun s => { s with safe := s.safe.insert cName }
  return none

private def checkAxiomsOk (cName : Name) : StateT AxCache CoreM (Option String) := do
  let env ← getEnv
  let (b?, st) := (findBadAxiom env cName).run (← get)
  set st
  if b?.isNone then return none
  let axioms ← Lean.collectAxioms cName
  let bad := axioms.filter fun ax => !allowedAxioms.contains ax
  if bad.isEmpty then return none
  else return some (String.intercalate ", " (bad.toList.map (·.toString)))

private def isPrivateOrInternal (n : Name) : Bool :=
  isPrivateName n || n.isInternalOrNum

private def isMutantModule (m : Name) : Bool :=
  nameLastStr m == "SpecMutants" || m.components.contains `SpecMutants

private def isCompilerAuxThm (env : Environment) (n : Name) : Bool :=
  let s := nameLastStr n
  let pref := n.getPrefix
  env.contains pref &&
    (s == "inj" || s == "injEq" || s == "sizeOf_spec" || s == "noConfusion" ||
      s == "noConfusionType" || s == "eq_def" ||
      (s.startsWith "eq_" && (s.drop 3).all Char.isDigit) ||
      (s.startsWith "_proof_" && (s.drop 7).all Char.isDigit))

private def moduleToFilePath (repoDir : System.FilePath) (modName : Name) : System.FilePath :=
  let parts := modName.components.map (·.toString)
  (parts.foldl (fun p seg => p / seg) repoDir).withExtension "lean"

private def moduleToIleanPath (libDir : System.FilePath) (modName : Name) : System.FilePath :=
  let parts := modName.components.map (·.toString)
  (parts.foldl (fun p seg => p / seg) libDir).withExtension "ilean"

private def stripRootPrefix (s : String) : String :=
  if s.startsWith "_root_." then (s.drop 7).toString else s

private partial def hasIdentOrAtom (pred : String → Bool) (stx : Syntax) : Bool :=
  match stx with
  | .ident _ _ val _ =>
    let raw := val.toString
    pred raw || pred (stripRootPrefix raw) || pred (nameLastStr val)
  | .atom _ val => pred val || pred (stripRootPrefix val)
  | .node _ _ args => args.any (hasIdentOrAtom pred)
  | .missing => false

private partial def hasSyntaxKind (k : Name) (stx : Syntax) : Bool :=
  if stx.getKind == k then true
  else match stx with
  | .node _ _ args => args.any (hasSyntaxKind k)
  | _ => false

private partial def findSyntaxKind? (k : Name) (stx : Syntax) : Option Syntax :=
  if stx.getKind == k then some stx
  else match stx with
  | .node _ _ args => args.findSome? (findSyntaxKind? k)
  | _ => none

private def isAllPassToken (s : String) : Bool :=
  s == "AllPass" || s == "Core.AllPass" || s == "AllPassRun" || s == "Core.AllPassRun" ||
    s == "CanReach" || s == "Core.CanReach" || s == "CanReachRun" || s == "Core.CanReachRun"

private def isForbiddenMutantToken (s : String) : Bool :=
  s == "sorry" || s == "admit" || s == "sorryAx" || s == "native_decide" ||
    s == "Lean.ofReduceBool" || s == "Lean.ofReduceNat" || s == "Lean.trustCompiler" ||
    s == "ofReduceBool" || s == "ofReduceNat" || s == "trustCompiler" ||
    s == "lcProof" || s == "lcCast" || s == "lcUnreachable" || s == "unsafe"

private def forbiddenIleanMutantRefs : Array String :=
  #["sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler",
    "Lean.Parser.Tactic.DecideConfig.native"]

private def forbiddenMetaSyntaxKinds : Array Name :=
  #[``Lean.Parser.Command.macro, ``Lean.Parser.Command.macro_rules,
    ``Lean.Parser.Command.elab, ``Lean.Parser.Command.elab_rules,
    ``Lean.Parser.Command.syntax, ``Lean.Parser.Command.syntaxAbbrev,
    ``Lean.Parser.Command.syntaxCat, ``Lean.Parser.Command.binderPredicate,
    ``Lean.Parser.Command.notation, ``Lean.Parser.Command.mixfix,
    ``Lean.Parser.Term.local,
    `Lean.runCmd, `Lean.runElab, `Lean.runMeta, `Lean.testExternCmd,
    ``Lean.Parser.Command.eval, ``Lean.Parser.Command.evalBang,
    `Lean.reduceCmd, ``Lean.Parser.Command.check, ``Lean.Parser.Command.check_failure,
    `Lean.Parser.checkTactic, `Lean.Parser.checkTacticFailure,
    ``Lean.Parser.Command.synth, ``Lean.Parser.Command.init_quot,
    `Lean.Elab.Command.reprove, `Lean.Elab.Command.aux_def,
    `Lean.guardMsgsCmd, `Lean.GuardMsgs.guardMsgsCmd, `Lean.guardPanicCmd]

private partial def hasForbiddenAttr (stx : Syntax) : Bool :=
  if stx.getKind == ``Lean.Parser.Attr.extern || stx.getKind == ``Lean.Parser.Attr.export then true
  else if stx.getKind == ``Lean.Parser.Term.attrInstance then
    hasIdentOrAtom (fun s => s == "extern" || s == "export" || s == "implemented_by" || s == "csimp") stx
  else match stx with
  | .node _ _ args => args.any hasForbiddenAttr
  | _ => false

private partial def hasNativeTacticConfig (stx : Syntax) : Bool :=
  if stx.getKind == ``Lean.Parser.Tactic.posConfigItem || stx.getKind == ``Lean.Parser.Tactic.configItem then
    hasIdentOrAtom (· == "native") stx
  else match stx with
  | .node _ _ args => args.any hasNativeTacticConfig
  | _ => false

private def checkForbiddenMetaOrAttr (path : System.FilePath) (stx : Syntax) : Option String :=
  if forbiddenMetaSyntaxKinds.any (hasSyntaxKind · stx) then
    some s!"FORBIDDEN_SYNTAX_EXT: {path} uses macro/elab/syntax/notation/local/run_cmd"
  else if hasForbiddenAttr stx then
    some s!"FORBIDDEN_ATTRIBUTE: {path} uses extern/implemented_by/csimp attribute"
  else if hasNativeTacticConfig stx then
    some s!"UNALLOWED_AXIOM_IN_MUTANT: {path} uses +native tactic configuration"
  else
    none

private def readIleanRefNames (ileanPath : System.FilePath) : IO (Except String (Array String)) := do
  unless ← ileanPath.pathExists do
    return .error s!"MISSING_ILEAN: {ileanPath}"
  let raw ← IO.FS.readFile ileanPath
  let .ok json := Json.parse raw
    | return .error s!"INVALID_ILEAN_JSON: {ileanPath}"
  let .ok (.obj refs) := json.getObjVal? "references"
    | return .error s!"INVALID_ILEAN_REFS: {ileanPath}"
  let mut names : Array String := #[]
  for (k, _) in refs do
    if let .ok kjson := Json.parse k then
      if let .ok cObj := kjson.getObjVal? "c" then
        if let .ok n := cObj.getObjValAs? String "n" then
          names := names.push n
  return .ok names

private def exprUsesOnlyAllowedAxioms (e : Expr) : MetaM Bool := do
  if e.hasSorry then return false
  let env ← getEnv
  for u in e.getUsedConstants do
    let uMod := env.getModuleIdxFor? u |>.bind (env.header.moduleNames[·]?) |>.getD .anonymous
    if isProjectModule uMod || !allowedAxioms.contains u && (env.find? u |>.map (· matches .axiomInfo _) |>.getD false) then
      let axs ← Lean.collectAxioms u
      if axs.any fun ax => !allowedAxioms.contains ax then
        return false
  return true

mutual
private partial def allCtorFieldsInhabited
    (visited : List Name) (availDoms : List Expr) (ty : Expr) (fuel : Nat) : MetaM Bool := do
  let tyWhnf ← Meta.whnf ty
  match tyWhnf with
  | .forallE n dom body bi =>
    if ← Meta.isProp dom then
      return false
    if !(← isKnownInhabited visited availDoms dom (fuel - 1)) then
      return false
    withLocalDecl n bi dom fun x =>
      allCtorFieldsInhabited visited availDoms (body.instantiate1 x) fuel
  | _ => return true

private partial def isKnownInhabited (visited : List Name) (availDoms : List Expr) (d : Expr) (fuel : Nat := 12) : MetaM Bool := do
  Meta.withTransparency .all do
    if ← Meta.isProp d then
      return false
    if ← availDoms.anyM (fun ad => Meta.isDefEq ad d) then
      return true
    let env ← getEnv
    try
      let neTy ← Meta.mkAppM ``Nonempty #[d]
      if let some inst ← Meta.synthInstance? neTy then
        if ← exprUsesOnlyAllowedAxioms inst then
          return true
    catch _ => pure ()
    if fuel == 0 then
      return false
    let dWhnf ← Meta.whnf d
    if ← availDoms.anyM (fun ad => Meta.isDefEq ad dWhnf) then
      return true
    match dWhnf with
    | .sort (.succ _) => return true
    | .sort .zero => return false
    | .forallE .. =>
      Meta.forallTelescopeReducing dWhnf fun xs ret => do
        let mut ext := availDoms
        for x in xs do
          ext := (← Meta.inferType x) :: ext
        isKnownInhabited visited ext ret (fuel - 1)
    | _ =>
      let fn := dWhnf.getAppFn
      let .const indName lvls := fn | return false
      if visited.contains indName then
        return false
      let some (.inductInfo iv) := env.find? indName | return false
      if iv.ctors.isEmpty || iv.numIndices > 0 then
        return false
      let args := dWhnf.getAppArgs
      if args.size < iv.numParams then
        return false
      let params := args.extract 0 iv.numParams
      for ctorName in iv.ctors do
        let some (.ctorInfo cv) := env.find? ctorName | continue
        let ctorTy := cv.type.instantiateLevelParams cv.levelParams lvls
        let appliedTy ← Meta.instantiateForall ctorTy params
        if ← allCtorFieldsInhabited (indName :: visited) availDoms appliedTy fuel then
          return true
      return false
end

private def hasCanonicalNondetInst (expectedInst : Name) (prog : Expr) : MetaM Bool := do
  Meta.withTransparency .all do
    let prog := prog.consumeMData
    let mut sawNondetInst := false
    for arg in prog.getAppArgs do
      let arg := arg.consumeMData
      let ty ← Meta.inferType arg
      let tyWhnf ← Meta.whnf ty
      if tyWhnf.isAppOfArity `Core.NondetTest 1 then
        sawNondetInst := true
        if arg != .const expectedInst [] then
          return false
    return sawNondetInst

private partial def isValidNegatedAllPassMutant (allowedPromises : Std.HashSet Name) (ty : Expr) : MetaM Bool := do
  let checkProg (arg : Expr) : MetaM Bool := do
    let arg := arg.consumeMData
    if !arg.isAppOfArity `Core.AllPass 1 then
      return false
    let prog := arg.appArg!.consumeMData
    let .const fn _ := prog.getAppFn.consumeMData | return false
    if !allowedPromises.contains fn then
      return false
    hasCanonicalNondetInst `Core.instNondetTestAllPassRun prog
  let cur := ty.consumeMData
  match cur with
  | .forallE n dom body bi =>
    if body.consumeMData == .const ``False [] then
      checkProg dom
    else
      if !(← isKnownInhabited [] [] dom) then
        return false
      withLocalDecl n bi dom fun x =>
        isValidNegatedAllPassMutant allowedPromises (body.instantiate1 x)
  | .letE _ _ v body _ =>
    isValidNegatedAllPassMutant allowedPromises (body.instantiate1 v)
  | .app (.const ``Not []) arg =>
    checkProg arg
  | _ => return false

private def checkValidNegatedMutantIO (env : Environment) (allowedPromises : Std.HashSet Name) (ty : Expr) : IO Bool := do
  let ctx : Core.Context := { fileName := "<MutantSigAudit>", fileMap := default, maxHeartbeats := 0 }
  let state : Core.State := { env }
  let (ok, _) ← (Meta.MetaM.run' (isValidNegatedAllPassMutant allowedPromises ty)).toIO ctx state
  return ok

private def rewriteExampleToAxiom (idx : Nat) (stx : Syntax) : Option Syntax :=
  if stx.getKind == ``Lean.Parser.Command.declaration && stx[1].getKind == ``Lean.Parser.Command.example then
    let exStx := stx[1]
    let optSig := exStx[1]
    let typeSpecNull := optSig[1]
    if typeSpecNull.isNone then none
    else
      let tySpec := typeSpecNull[0]
      let declId := Syntax.node .none ``Lean.Parser.Command.declId
        #[mkIdent (Name.mkSimple s!"_sigAudit_{idx}"), Syntax.node .none `null #[]]
      let declSig := Syntax.node .none ``Lean.Parser.Command.declSig #[optSig[0], tySpec]
      let axStx := Syntax.node .none ``Lean.Parser.Command.axiom #[mkAtom "axiom", declId, declSig]
      let privMods := Syntax.node .none ``Lean.Parser.Command.declModifiers #[
        Syntax.node .none `null #[],
        Syntax.node .none `null #[],
        Syntax.node .none `null #[Syntax.node .none ``Lean.Parser.Command.private #[mkAtom "private"]],
        Syntax.node .none `null #[],
        Syntax.node .none `null #[],
        Syntax.node .none `null #[],
        Syntax.node .none `null #[]
      ]
      some (Syntax.node .none ``Lean.Parser.Command.declaration #[privMods, axStx])
  else
    none

private unsafe def countElaboratedNegatedAllPass
    (headEnv : Environment)
    (allowedPromises : Std.HashSet Name)
    (m : Name)
    (path : System.FilePath) : IO (Except String Nat) := do
  unless ← path.pathExists do
    return .error s!"MISSING_SOURCE_FILE: {path}"
  let input ← IO.FS.readFile path
  let ictx := Parser.mkInputContext input path.toString
  let (_header, pstate0, msgs0) ← Parser.parseHeader ictx
  let mut cmdState := Elab.Command.mkState (headEnv.setMainModule (m ++ `_SigAudit)) msgs0 {}
  let mut pstate := pstate0
  let mut modNeg := 0
  let mut idx := 0
  repeat do
    let scope := cmdState.scopes.head!
    let pmctx : Parser.ParserModuleContext := {
      env := cmdState.env
      options := scope.opts
      currNamespace := scope.currNamespace
      openDecls := scope.openDecls
    }
    let (stx, nextP, nextMsgs) := Parser.parseCommand ictx pmctx pstate cmdState.messages
    pstate := nextP
    cmdState := { cmdState with messages := nextMsgs }
    if Parser.isTerminalCommand stx then break
    let mut isEx := false
    let mut cmdToRun := stx
    if !scope.varDecls.isEmpty then
      return .error s!"FORBIDDEN_VARIABLE_IN_MUTANT: {path} uses section variable"
    if let some axCmd := rewriteExampleToAxiom (idx + 1) stx then
      idx := idx + 1
      isEx := true
      cmdToRun := axCmd
    else if stx.getKind == ``Lean.Parser.Command.declaration && stx[1].getKind == ``Lean.Parser.Command.theorem then
      let thmStx := stx[1]
      let declId := thmStx[1]
      let optSig := thmStx[2]
      let declSig := Syntax.node .none ``Lean.Parser.Command.declSig #[optSig[0], optSig[1]]
      let axStx := Syntax.node .none ``Lean.Parser.Command.axiom #[mkAtom "axiom", declId, declSig]
      cmdToRun := Syntax.node .none ``Lean.Parser.Command.declaration #[stx[0], axStx]
    let ((), nextCmdState) ←
      ((Elab.Command.elabCommand cmdToRun).run
        { fileName := path.toString, fileMap := ictx.fileMap, snap? := none, cancelTk? := none } |>.run cmdState)
        |>.toIO fun _ => IO.Error.userError s!"ELAB_ERROR in {m}"
    cmdState := nextCmdState
    if isEx then
      let cname := cmdState.scopes.head!.currNamespace ++ Name.mkSimple s!"_sigAudit_{idx}"
      let privName := mkPrivateName cmdState.env cname
      let c? := cmdState.env.find? privName |>.orElse fun _ => cmdState.env.find? cname
      if let some c := c? then
        if !c.type.hasSorry then
          if ← checkValidNegatedMutantIO cmdState.env allowedPromises c.type then
            modNeg := modNeg + 1
  return .ok modNeg

private def parseModuleCommands (env : Environment) (path : System.FilePath)
    (allowMacroRecovery : Bool := false) : IO (Except String (Array Syntax)) := do
  unless ← path.pathExists do
    return .error s!"MISSING_SOURCE_FILE: {path}"
  let input ← IO.FS.readFile path
  let ictx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader ictx
  if messages.hasErrors then
    return .error s!"PARSE_ERROR: header parse error in {path}"
  let mut cmds : Array Syntax := #[header]
  let mut pstate := parserState
  let mut msgs := messages
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  repeat do
    let (stx, nextState, nextMsgs) := Parser.parseCommand ictx pmctx pstate msgs
    pstate := nextState
    msgs := nextMsgs
    if Parser.isTerminalCommand stx then
      break
    cmds := cmds.push stx
  if msgs.hasErrors && !allowMacroRecovery then
    return .error s!"PARSE_ERROR: command parse error in {path}"
  return .ok cmds

private partial def collectConclusionAtoms (e : Expr) : Array Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then
    collectConclusionAtoms e.appFn!.appArg! ++ collectConclusionAtoms e.appArg!
  else
    #[e]

private def usesAssumeTransitive
    (env : Environment)
    (start : Name) : Bool := Id.run do
  let mut queue : Array Name := #[start]
  let mut seen : Std.HashSet Name := {}
  while !queue.isEmpty do
    let cName := queue.back!
    queue := queue.pop
    if cName == `Core.NondetTest.assume then
      return true
    if seen.contains cName then
      continue
    seen := seen.insert cName
    if !isProjectModule (env.getModuleIdxFor? cName |>.bind (env.header.moduleNames[·]?) |>.getD .anonymous) then
      continue
    let body? := match env.find? cName with
      | some (.defnInfo dv) => some dv.value
      | some (.opaqueInfo ov) => some ov.value
      | _ => none
    if let some body := body? then
      for u in body.getUsedConstants do
        if !seen.contains u then
          queue := queue.push u
  return false

private partial def withUnconditionalAtoms {α : Type} (ty : Expr) (k : Option (Array Expr) → MetaM α) : MetaM α := do
  let cur := ty.consumeMData
  if let .forallE n d b bi := cur then
    if !(← isKnownInhabited [] [] d) then
      k none
    else
      withLocalDecl n bi d fun x =>
        withUnconditionalAtoms (b.instantiate1 x) k
  else if let .letE _ _ v b _ := cur then
    withUnconditionalAtoms (b.instantiate1 v) k
  else
    k (some (collectConclusionAtoms cur))

private def moduleNameUnderRoot (rootDir entry : System.FilePath) (rootMod : Name) : Name :=
  ((entry.withExtension "").components.drop rootDir.components.length).foldl
    (fun acc seg => if seg == "." || seg.isEmpty then acc else Name.str acc seg) rootMod

private def moduleNameUnderLeanSwe (leanSweDir entry : System.FilePath) : Name :=
  moduleNameUnderRoot leanSweDir entry `LeanSwe

private partial def collectLeanRelFiles (dir : System.FilePath) (relPrefix : String) :
    IO (Array (String × System.FilePath)) := do
  let mut out : Array (String × System.FilePath) := #[]
  let entries ← dir.readDir
  let sorted := entries.qsort fun a b => a.fileName < b.fileName
  for entry in sorted do
    let rel := s!"{relPrefix}/{entry.fileName}"
    if ← entry.path.isDir then
      let sub ← collectLeanRelFiles entry.path rel
      out := out ++ sub
    else if entry.path.extension == some "lean" then
      out := out.push (rel, entry.path)
  return out

private def moduleToOleanPath (libDir : System.FilePath) (modName : Name) : System.FilePath :=
  let parts := modName.components.map (·.toString)
  (parts.foldl (fun p seg => p / seg) libDir).withExtension "olean"

private def compressAuditModules : Array Name := #[
  `LeanSwe.Compress.Types, `LeanSwe.Compress.Model, `LeanSwe.Compress.Impl,
  `LeanSwe.Compress.Interface, `LeanSwe.Compress.SpecTests,
  `LeanSwe.Compress.Proofs
]

private def isAllowedCompressDirectImport (m : Name) : Bool :=
  isAllowedClosureStdlibModule false m || m.getRoot == `Core ||
    ((m.components.take 2 == [`LeanSwe, `Compress] || m.components.take 2 == [`LeanSwe, `Process]) &&
      nameLastStr m != "RuntimeTests" && !isMutantModule m)

private def checkCompressTrustedClosure
    (repoDir : System.FilePath) (env : Environment) (extraMods : Array Name) : IO (Array String) := do
  let compMods := discoverPackageModules env extraMods `LeanSwe.Compress compressAuditModules
  let mut errs : Array String := #[]
  for m in compMods do
    let some mIdx := env.header.moduleNames.findIdx? (· == m)
      | do errs := errs.push s!"TRUSTED_CLOSURE_COMPRESS_MISSING_MODULE: {m}"; continue
    if let some attrErr ← checkClosureModuleAttrs repoDir env m .anonymous then
      errs := errs.push attrErr
    let some data := env.header.moduleData[mIdx]? | continue
    for imp in data.imports do
      if !isAllowedCompressDirectImport imp.module then
        errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_IMPORT: {m} imports {imp.module}"
    for c in data.constants do
      if c matches .opaqueInfo _ || (getExternAttrData? env c.name).isSome then
        errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_EXTERN: {c.name} in {m}"
      if let .defnInfo v := c then
        if v.safety != .safe && !(← isAllowedCompilerUnsafeDef env c.name v) then
          errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_UNSAFE_DEF: {c.name} in {m}"
      if let some impl := Lean.Compiler.getImplementedBy? env c.name then
        if !(← isCompilerGeneratedCtorIdx env c.name impl c) then
          errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_IMPL_BY: {c.name} -> {impl} in {m}"
      for u in c.type.getUsedConstants ++ (c.value?.map (·.getUsedConstants) |>.getD #[]) do
        let uMod := env.getModuleIdxFor? u |>.bind (env.header.moduleNames[·]?) |>.getD .anonymous
        if !isProjectModule uMod then
          if let some uInfo := env.find? u then
            if let some extData := getExternAttrData? env u then
              if isForbiddenHostExtern u uInfo extData then
                errs := errs.push s!"TRUSTED_CLOSURE_FORBIDDEN_HOST_IO_EXTERN: {u} referenced by {c.name} in {m}"
  let ctx : Core.Context := { fileName := "<CheckPromises.CompressWiring>", fileMap := default, maxHeartbeats := 0 }
  let (wErrs, _) ← (Meta.MetaM.run' do
    let mut mErrs : Array String := #[]
    match env.find? `LeanSwe.Compress.defaultApi with
    | some (.defnInfo dv) =>
      let canon ← Meta.mkAppM `LeanSwe.Compress.Internal.mkApiM #[mkConst `LeanSwe.Process.SysBridge.defaultOps]
      if dv.safety != .safe || dv.type.getUsedConstants.contains ``optParam ||
          !(← Meta.withTransparency .none (Meta.isDefEq dv.value canon)) then
        mErrs := mErrs.push "TRUSTED_CLOSURE_COMPRESS_WIRING: invalid defaultApi"
    | _ => mErrs := mErrs.push "TRUSTED_CLOSURE_COMPRESS_WIRING: missing defaultApi"
    for field in #[`compress, `decompress, `compressWith, `decompressWith, `isToolAvailable] do
      let wName := Name.mkStr `LeanSwe.Compress field.getString!
      let projName := Name.mkStr `LeanSwe.Compress.CompressApiM field.getString!
      match env.find? wName with
      | some (.defnInfo wv) =>
        let red := etaReduceExpr wv.value
        if wv.safety != .safe || wv.type.getUsedConstants.contains ``optParam ||
            !(red.isAppOfArity projName 2 && red.appFn!.appArg!.consumeMData.isConstOf ``IO &&
              red.appArg!.consumeMData.isConstOf `LeanSwe.Compress.defaultApi) then
          mErrs := mErrs.push s!"TRUSTED_CLOSURE_COMPRESS_WIRING: invalid wrapper {wName}"
      | _ => mErrs := mErrs.push s!"TRUSTED_CLOSURE_COMPRESS_WIRING: missing wrapper {wName}"
    return mErrs).toIO ctx { env }
  return errs ++ wErrs

private def isAllowedManagedProcessClosureModule (m : Name) : Bool :=
  m.getRoot == `Core ||
    (m.components.take 2 == [`LeanSwe, `Process] &&
      m != `LeanSwe.Process.SpecTests &&
      m != `LeanSwe.Process.SpecMutants &&
      !m.components.contains `Proofs &&
      !m.components.contains `RuntimeTests) ||
    m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Common] ||
    (m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Files] &&
      m != `LeanSwe.LinuxSyscall.Files.RuntimeTests &&
      m != `LeanSwe.LinuxSyscall.Files.SpecMutants &&
      !m.components.contains `Proofs) ||
    (m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Process] &&
      m != `LeanSwe.LinuxSyscall.Process.RuntimeTests &&
      m != `LeanSwe.LinuxSyscall.Process.SpecMutants &&
      !m.components.contains `Proofs) ||
    (m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Poll] &&
      m != `LeanSwe.LinuxSyscall.Poll.RuntimeTests &&
      m != `LeanSwe.LinuxSyscall.Poll.SpecMutants &&
      !m.components.contains `Proofs) ||
    (m.components.take 3 == [`LeanSwe, `LinuxSyscall, `TimeRand] &&
      m != `LeanSwe.LinuxSyscall.TimeRand.RuntimeTests &&
      m != `LeanSwe.LinuxSyscall.TimeRand.SpecMutants &&
      !m.components.contains `Proofs) ||
    postForkAuditModules.contains m ||
    (envVarsAuditModules.contains m &&
      m != `LeanSwe.EnvVars.SpecTests &&
      m != `LeanSwe.EnvVars.Raw.SpecTests &&
      !m.components.contains `Proofs)

private def checkManagedProcessClosure (env : Environment) : IO (Array String) := do
  let mut errs : Array String := #[]
  let seedMods : Array Name := #[
    `LeanSwe.Process.Types,
    `LeanSwe.Process.SysBridge,
    `LeanSwe.Process.Impl,
    `LeanSwe.Process.Interface
  ]
  let mut queue : Array (Name × Name) := #[]
  for h : i in [0 : env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    let some data := env.header.moduleData[i]? | continue
    if m.components.take 2 == [`LeanSwe, `Process] then
      for imp in data.imports do
        if imp.module.components.take 3 == [`LeanSwe, `LinuxSyscall, `Net] ||
            imp.module.components.take 3 == [`LeanSwe, `LinuxSyscall, `Sandbox] then
          errs := errs.push s!"PROCESS_TRUSTED_CLOSURE_FORBIDDEN_IMPORT: {m} imports {imp.module}"
      for c in data.constants do
        if (getExternAttrData? env c.name).isSome then
          errs := errs.push s!"PROCESS_FORBIDDEN_EXTERN: {c.name} in {m}"
        if let some impl := Lean.Compiler.getImplementedBy? env c.name then
          if !(← isCompilerGeneratedCtorIdx env c.name impl c) then
            errs := errs.push s!"PROCESS_FORBIDDEN_IMPLEMENTED_BY: {c.name} -> {impl} in {m}"
        if let .defnInfo v := c then
          if v.safety != .safe then
            if !(← isAllowedCompilerUnsafeDef env c.name v) then
              errs := errs.push s!"PROCESS_FORBIDDEN_UNSAFE: {c.name} in {m}"
        if (Lean.regularInitAttr.getParam? env c.name).isSome then
          let allowedInit :=
            m == `LeanSwe.Process.SysBridge &&
            privateToUserName? c.name == some `LeanSwe.Process.SysBridge.gProcTable
          if !allowedInit then
            errs := errs.push s!"PROCESS_FORBIDDEN_INIT: {c.name} in {m}"
    if seedMods.contains m then
      for c in data.constants do
        queue := queue.push (m, c.name)
  let mut visited : Std.HashSet Name := {}
  while !queue.isEmpty do
    let (originMod, cName) := queue.back!
    queue := queue.pop
    if visited.contains cName then continue
    visited := visited.insert cName
    let some cinfo := env.find? cName | continue
    let cMod := env.getModuleIdxFor? cName |>.bind (env.header.moduleNames[·]?) |>.getD .anonymous
    if isProjectModule cMod then
      if !isAllowedManagedProcessClosureModule cMod then
        errs := errs.push s!"PROCESS_TRUSTED_CLOSURE_UNALLOWED_MODULE: {cName} in {cMod} reachable from {originMod}"
      for u in cinfo.type.getUsedConstants do
        if !visited.contains u then
          queue := queue.push (originMod, u)
      let val? := match cinfo with
        | .defnInfo v => some v.value
        | .opaqueInfo v => some v.value
        | _ => none
      if let some val := val? then
        for u in val.getUsedConstants do
          if !visited.contains u then
            queue := queue.push (originMod, u)
  match env.find? `LeanSwe.Process.defaultApi with
  | some (.defnInfo dv) =>
    let used := dv.value.getUsedConstants
    if !used.contains `LeanSwe.Process.Internal.mkApiM ||
        !used.contains `LeanSwe.Process.SysBridge.defaultOps then
      errs := errs.push "PROCESS_INTERFACE_WIRING_MISMATCH: LeanSwe.Process.defaultApi must wire Internal.mkApiM to SysBridge.defaultOps"
  | _ =>
    errs := errs.push "PROCESS_INTERFACE_WIRING_MISMATCH: missing LeanSwe.Process.defaultApi"
  match env.find? `LeanSwe.Process.Proofs.healthySimApi with
  | some (.defnInfo dv) =>
    let used := dv.value.getUsedConstants
    if !used.contains `LeanSwe.Process.Internal.mkApiM ||
        !used.contains `LeanSwe.Process.Proofs.healthySimRawOps then
      errs := errs.push "PROCESS_PROOF_TARGET_WIRING_MISMATCH: healthySimApi must wire Internal.mkApiM to healthySimRawOps"
  | _ =>
    errs := errs.push "PROCESS_PROOF_TARGET_WIRING_MISMATCH: missing LeanSwe.Process.Proofs.healthySimApi"
  for wrapper in #[`LeanSwe.Process.run, `LeanSwe.Process.runChecked, `LeanSwe.Process.activeProcessCount] do
    match env.find? wrapper with
    | some (.defnInfo dv) =>
      if !dv.value.getUsedConstants.contains `LeanSwe.Process.defaultApi then
        errs := errs.push s!"PROCESS_INTERFACE_WIRING_MISMATCH: {wrapper} must delegate to LeanSwe.Process.defaultApi"
    | _ =>
      errs := errs.push s!"PROCESS_INTERFACE_WIRING_MISMATCH: missing {wrapper}"
  return errs

private def checkProcessSandboxHostClosure (env : Environment) : IO (Array String) := do
  let mut errs : Array String := #[]
  for h : i in [0 : env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    let some data := env.header.moduleData[i]? | continue
    if m.components.take 2 == [`LeanSwe, `ProcessSandbox] then
      for c in data.constants do
        if (getExternAttrData? env c.name).isSome then
          errs := errs.push s!"PSANDBOX_FORBIDDEN_EXTERN: {c.name} in {m}"
        if let some impl := Lean.Compiler.getImplementedBy? env c.name then
          if !(← isCompilerGeneratedCtorIdx env c.name impl c) then
            errs := errs.push s!"PSANDBOX_FORBIDDEN_IMPLEMENTED_BY: {c.name} -> {impl} in {m}"
        if let .defnInfo v := c then
          if v.safety != .safe then
            if !(← isAllowedCompilerUnsafeDef env c.name v) then
              errs := errs.push s!"PSANDBOX_FORBIDDEN_UNSAFE: {c.name} in {m}"
        if (Lean.regularInitAttr.getParam? env c.name).isSome then
          let allowedInit :=
            m == `LeanSwe.ProcessSandbox.Host.SysBridge &&
            privateToUserName? c.name == some `LeanSwe.ProcessSandbox.Host.SysBridge.gHostTable
          if !allowedInit then
            errs := errs.push s!"PSANDBOX_FORBIDDEN_INIT: {c.name} in {m}"
        let usesBaseMutex (e : Expr) : Bool :=
          e.getUsedConstants.any fun u => u.components.take 2 == [`Std, `BaseMutex]
        let val? : Option Expr := match c with
          | .defnInfo v => some v.value
          | .thmInfo v => some v.value
          | .opaqueInfo v => some v.value
          | _ => none
        if usesBaseMutex c.type || (val?.map usesBaseMutex |>.getD false) then
          errs := errs.push s!"PSANDBOX_FORBIDDEN_BASEMUTEX: {c.name} in {m} references Std.BaseMutex"
  match env.find? `LeanSwe.ProcessSandbox.Raw.defaultOps with
  | some (.defnInfo dv) =>
    if !dv.value.getUsedConstants.contains `LeanSwe.ProcessSandbox.Host.SysBridge.defaultOps then
      errs := errs.push "PSANDBOX_INTERFACE_WIRING_MISMATCH: LeanSwe.ProcessSandbox.Raw.defaultOps must delegate to Host.SysBridge.defaultOps"
  | _ =>
    errs := errs.push "PSANDBOX_INTERFACE_WIRING_MISMATCH: missing LeanSwe.ProcessSandbox.Raw.defaultOps"
  return errs

private def connectProxyRequiredModules : Array Name := #[
  `LeanSwe.ConnectProxy.Types,
  `LeanSwe.ConnectProxy.Model,
  `LeanSwe.ConnectProxy.Relay,
  `LeanSwe.ConnectProxy.SysBridge,
  `LeanSwe.ConnectProxy.HealthySys,
  `LeanSwe.ConnectProxy.Impl,
  `LeanSwe.ConnectProxy.Interface,
  `LeanSwe.ConnectProxy.SpecTests,
  `LeanSwe.ConnectProxy.Proofs
]

private partial def peelLambdas (e : Expr) : Expr :=
  match e.consumeMData with
  | .lam _ _ body _ => peelLambdas body
  | cur => cur

private def expectedConnectProxyPromiseTarget? (fn : Name) : Option Name :=
  let s := fn.getString!
  if s.startsWith "test_cproxy_healthy_" then
    some `LeanSwe.ConnectProxy.HealthySys.realBridgeTarget
  else if s.startsWith "test_cproxy_withProxy_" then
    some `LeanSwe.ConnectProxy.Internal.mkApiM
  else if s.startsWith "test_cproxy_model_authorizeConnect_" then
    some `LeanSwe.ConnectProxy.Model.authorizeConnect
  else if s.startsWith "test_cproxy_" then
    some `LeanSwe.ConnectProxy.defaultApi
  else
    none

private def isCanonicalConnectProxyPromiseApp (fn : Name) (prog : Expr) : Except String Unit :=
  if fn.components.take 2 != [`LeanSwe, `ConnectProxy] then
    .ok ()
  else
    match expectedConnectProxyPromiseTarget? fn with
    | none =>
      .error s!"CPROXY_UNPINNED_PROMISE: {fn} lacks canonical target rule"
    | some expectedTarget =>
      let args := prog.consumeMData.getAppArgs
      if args.size != 3 then
        .error s!"CPROXY_DECOY_TARGET: {fn} expected 3 arguments, got {args.size}"
      else
        let tgt := etaReduceExpr args[2]!
        let ok :=
          if expectedTarget == `LeanSwe.ConnectProxy.Internal.mkApiM then
            tgt.isAppOfArity expectedTarget 3
          else
            tgt.isConstOf expectedTarget
        if ok then .ok ()
        else .error s!"CPROXY_DECOY_TARGET: {fn} proved over non-canonical target instead of {expectedTarget}"

private def isAllowedConnectProxyNonProofProjectMod (m : Name) : Bool :=
  let s := m.toString
  if m.getRoot == `Core then
    m != `Core.Assumptions
  else if s == "LeanSwe.LinuxSyscall.Common" || s.startsWith "LeanSwe.LinuxSyscall.Common." then
    true
  else if m.components.take 2 == [`LeanSwe, `LinuxSyscall] then
    match m.components.drop 2 with
    | sub :: rest =>
      (sub == `Files || sub == `Net || sub == `Poll || sub == `Dns || sub == `TimeRand) &&
        !rest.contains `RuntimeTests && !rest.contains `SpecMutants &&
        !rest.contains `Proofs && !rest.contains `SpecTests
    | [] => false
  else if m == `LeanSwe.NetRelay.Types || m == `LeanSwe.NetRelay.Model ||
      m == `LeanSwe.NetRelay.Impl || m == `LeanSwe.NetRelay.Interface then
    true
  else if m.components.take 2 == [`LeanSwe, `ConnectProxy] then
    m != `LeanSwe.ConnectProxy.SpecMutants &&
      nameLastStr m != "RuntimeTests" &&
      !m.components.contains `Proofs
  else
    false

private def isAllowedConnectProxyAnyProjectMod (m : Name) : Bool :=
  if isAllowedConnectProxyNonProofProjectMod m then true
  else if m == `Core.Assumptions then true
  else if m.components.take 2 == [`LeanSwe, `ConnectProxy] then
    m != `LeanSwe.ConnectProxy.SpecMutants && nameLastStr m != "RuntimeTests"
  else if m.getRoot == `LeanSwe then
    (m.components.contains `Proofs || nameLastStr m == "SpecTests") &&
      !isMutantModule m && nameLastStr m != "RuntimeTests"
  else
    false

private def isAllowedConnectProxyProjectExtern (env : Environment) (cMod cName : Name) (cinfo : ConstantInfo) : Bool :=
  let extData? := getExternAttrData? env cName
  let userName := (privateToUserName? cName).getD cName
  if isAllowedCoreInitDecl cMod cName && (cinfo matches .opaqueInfo _) && extData?.isNone then
    true
  else if cMod == `LeanSwe.LinuxSyscall.Common.Types &&
      userName == `LeanSwe.LinuxSyscall.RawFdPointed &&
      (cinfo matches .opaqueInfo _) && extData?.isNone then
    true
  else if !(isPrivateName cName && (cinfo matches .opaqueInfo _)) then
    false
  else
    let symMap? :=
      if cMod == `LeanSwe.LinuxSyscall.Files.Interface then some allowedFilesExternSyms
      else if cMod == `LeanSwe.LinuxSyscall.Net.Interface then some allowedNetExternSyms
      else if cMod == `LeanSwe.LinuxSyscall.Poll.Interface then some allowedPollExternSyms
      else if cMod == `LeanSwe.LinuxSyscall.Dns.Interface then some allowedDnsExternSyms
      else if cMod == `LeanSwe.LinuxSyscall.TimeRand.Interface then some allowedTimeRandExternSyms
      else none
    match symMap?.bind (·.get? userName) with
    | some expectedSym => isExactStandardExtern extData? expectedSym
    | none => false

private def allowedConnectProxyStdExternConsts : Std.HashSet Name :=
  (#[`Task.get, `Task.pure, `Task.map, `Task.bind,
     `BaseIO.asTask, `BaseIO.mapTask, `BaseIO.bindTask, `BaseIO.chainTask,
     `BaseIO.getTaskState, `BaseIO.hasFinished,
     `IO.RealWorld.nonemptyType, `IO.wait, `IO.cancel, `IO.checkCanceled, `IO.getTaskState, `IO.hasFinished,
     `ST.RefPointed, `ST.Prim.mkRef, `ST.Prim.Ref.get, `ST.Prim.Ref.set, `ST.Prim.Ref.put,
     `ST.Prim.Ref.swap, `ST.Prim.Ref.take, `ST.Prim.Ref.modifyGetUnsafe,
     `System.Platform.getNumBits, `System.Platform.numBits] : Array Name).foldl
    (fun s n => s.insert n) (Std.HashSet.emptyWithCapacity 32)

private def allowedConnectProxyStdExternCSyms : Std.HashSet String :=
  (#["lean_task_get", "lean_task_get_own", "lean_task_pure", "lean_task_map", "lean_task_bind",
     "lean_io_as_task", "lean_io_map_task", "lean_io_bind_task", "lean_io_chain_task",
     "lean_io_wait", "lean_io_cancel", "lean_io_check_canceled", "lean_io_get_task_state",
     "lean_st_mk_ref", "lean_st_ref_get", "lean_st_ref_set", "lean_st_ref_put",
     "lean_st_ref_swap", "lean_st_ref_take", "lean_st_ref_modify_get",
     "lean_system_platform_nbits"] : Array String).foldl
    (fun s n => s.insert n) (Std.HashSet.emptyWithCapacity 32)

private def isForbiddenConnectProxyStdExtern (cName : Name) (cinfo : ConstantInfo) (extData? : Option ExternAttrData) : Bool :=
  let cs := cName.toString
  if cName == `dbgTrace || cName == `dbgTraceVal ||
      cs.startsWith "Std.Internal.UV." || cs.startsWith "Std.Internal.Async." ||
      cs.startsWith "Lean.IO." || cs.startsWith "Lean.Loop." ||
      cs.startsWith "IO.FS." || cs.startsWith "IO.Process." ||
      cName == `IO.getEnv || cName == `IO.monoMsNow || cName == `IO.monoNanosNow ||
      cName == `IO.sleep || cName == `IO.getStdin || cName == `IO.getStdout || cName == `IO.getStderr ||
      (cs.startsWith "System." && cName != `System.Platform.getNumBits && cName != `System.Platform.numBits) then
    true
  else if extData?.isSome || cinfo matches .opaqueInfo _ then
    if (cs.startsWith "IO." || cs.startsWith "ST." || cs.startsWith "BaseIO." || cs.startsWith "Task.") &&
        !allowedConnectProxyStdExternConsts.contains cName then
      true
    else
      match extData? with
      | none => false
      | some ed =>
        ed.entries.any fun
          | .adhoc _ => true
          | .opaque => false
          | .inline _ s =>
            forbiddenHostCSymPrefixes.any (s.startsWith ·) && !allowedConnectProxyStdExternCSyms.contains s
          | .standard _ s =>
            forbiddenHostCSymPrefixes.any (s.startsWith ·) && !allowedConnectProxyStdExternCSyms.contains s
  else
    false

private def cproxyProofsForbiddenMetaKinds : Array Name :=
  #[``Lean.Parser.Command.macro_rules,
    ``Lean.Parser.Command.elab, ``Lean.Parser.Command.elab_rules,
    ``Lean.Parser.Command.syntax, ``Lean.Parser.Command.syntaxAbbrev,
    ``Lean.Parser.Command.syntaxCat, ``Lean.Parser.Command.binderPredicate,
    ``Lean.Parser.Command.notation, ``Lean.Parser.Command.mixfix,
    ``Lean.Parser.Command.initialize, `Lean.Parser.Command.builtinInitialize,
    `Lean.runCmd, `Lean.runElab, `Lean.runMeta, `Lean.testExternCmd,
    ``Lean.Parser.Command.eval, ``Lean.Parser.Command.evalBang,
    `Lean.reduceCmd, ``Lean.Parser.Command.check, ``Lean.Parser.Command.check_failure,
    `Lean.Parser.checkTactic, `Lean.Parser.checkTacticFailure,
    ``Lean.Parser.Command.synth, ``Lean.Parser.Command.init_quot,
    `Lean.Elab.Command.reprove, `Lean.Elab.Command.aux_def,
    `Lean.guardMsgsCmd, `Lean.GuardMsgs.guardMsgsCmd, `Lean.guardPanicCmd]

private def checkConnectProxySourceCmd (path : System.FilePath) (isProofs : Bool) (stx : Syntax) : Option String :=
  if !isProofs then
    if hasSyntaxKind ``Lean.Parser.Command.initialize stx ||
        hasSyntaxKind `Lean.Parser.Command.builtinInitialize stx then
      some s!"FORBIDDEN_INIT_SYNTAX: {path} uses initialize/builtin_initialize"
    else
      checkForbiddenMetaOrAttr path stx
  else if cproxyProofsForbiddenMetaKinds.any (hasSyntaxKind · stx) ||
      hasIdentOrAtom (fun s => s == "guard_msgs" || s == "#guard_msgs") stx then
    some s!"FORBIDDEN_SYNTAX_EXT: {path} uses elab/syntax/notation/initialize/eval/reduce/guard_msgs/run_cmd"
  else if hasSyntaxKind ``Lean.Parser.Command.macro stx && !hasSyntaxKind ``Lean.Parser.Term.local stx then
    some s!"FORBIDDEN_SYNTAX_EXT: {path} uses non-local macro in ConnectProxy.Proofs"
  else if hasForbiddenAttr stx then
    some s!"FORBIDDEN_ATTRIBUTE: {path} uses forbidden attribute (extern/implemented_by/csimp/export)"
  else if hasNativeTacticConfig stx then
    some s!"UNALLOWED_AXIOM_IN_MUTANT: {path} uses +native tactic configuration"
  else
    none

private def usesConstWithinModule (env : Environment) (modName root target : Name) : Bool := Id.run do
  let mut q : Array Name := #[root]
  let mut seen : Std.HashSet Name := {}
  while !q.isEmpty do
    let cur := q.back!
    q := q.pop
    if cur == target then return true
    if seen.contains cur then continue
    seen := seen.insert cur
    let cMod := env.getModuleIdxFor? cur |>.bind (env.header.moduleNames[·]?) |>.getD .anonymous
    if cMod != modName then continue
    if let some (.defnInfo dv) := env.find? cur then
      for u in dv.value.getUsedConstants do
        if !seen.contains u then
          q := q.push u
  return false

private def exprUsesStructField (stName : Name) : Expr → Bool
  | .const fn _ => fn.getPrefix == stName
  | .proj pn _ s => pn == stName || exprUsesStructField stName s
  | .app f a => exprUsesStructField stName f || exprUsesStructField stName a
  | .lam _ t b _ | .forallE _ t b _ => exprUsesStructField stName t || exprUsesStructField stName b
  | .letE _ t v b _ =>
    exprUsesStructField stName t || exprUsesStructField stName v || exprUsesStructField stName b
  | .mdata _ b => exprUsesStructField stName b
  | _ => false

private def checkConnectProxyWiring (env : Environment) : Array String := Id.run do
  let mut errs : Array String := #[]
  match env.find? `LeanSwe.ConnectProxy.defaultApi with
  | some (.defnInfo dv) =>
    let v := dv.value.consumeMData
    let args := v.getAppArgs
    let ok :=
      v.isAppOfArity `LeanSwe.ConnectProxy.Internal.mkScopedApiM 4 &&
      args[0]!.consumeMData.isConstOf ``IO &&
      args[3]!.consumeMData.isConstOf `LeanSwe.ConnectProxy.Internal.defaultScopedIoOps
    if !ok then
      errs := errs.push "CPROXY_INTERFACE_WIRING: LeanSwe.ConnectProxy.defaultApi must apply Internal.mkScopedApiM to Internal.defaultScopedIoOps"
  | _ =>
    errs := errs.push "CPROXY_INTERFACE_WIRING: missing LeanSwe.ConnectProxy.defaultApi"
  let pubFns : Array (Name × Name) := #[
    (`LeanSwe.ConnectProxy.parseIpAddr, `LeanSwe.ConnectProxy.ConnectProxyApiM.parseIpAddr),
    (`LeanSwe.ConnectProxy.parseIpPrefix, `LeanSwe.ConnectProxy.ConnectProxyApiM.parseIpPrefix),
    (`LeanSwe.ConnectProxy.isGlobalIp, `LeanSwe.ConnectProxy.ConnectProxyApiM.isGlobalIp),
    (`LeanSwe.ConnectProxy.allowsIp, `LeanSwe.ConnectProxy.ConnectProxyApiM.allowsIp),
    (`LeanSwe.ConnectProxy.parseConnectRequest, `LeanSwe.ConnectProxy.ConnectProxyApiM.parseConnectRequest),
    (`LeanSwe.ConnectProxy.validateConfig, `LeanSwe.ConnectProxy.ConnectProxyApiM.validateConfig),
    (`LeanSwe.ConnectProxy.withProxy, `LeanSwe.ConnectProxy.ConnectProxyApiM.withProxy)
  ]
  for (pubName, projName) in pubFns do
    match env.find? pubName with
    | some (.defnInfo dv) =>
      let used := dv.value.getUsedConstants
      let body := peelLambdas dv.value
      let projOk :=
        body.getAppFn.consumeMData.constName? == some projName ||
          (match body.getAppFn.consumeMData with
           | .proj `LeanSwe.ConnectProxy.ConnectProxyApiM _ s => s.consumeMData.isConstOf `LeanSwe.ConnectProxy.defaultApi
           | _ => false)
      if !projOk || !used.contains `LeanSwe.ConnectProxy.defaultApi then
        errs := errs.push s!"CPROXY_INTERFACE_WIRING: {pubName} must delegate directly to defaultApi"
    | _ =>
      errs := errs.push s!"CPROXY_INTERFACE_WIRING: missing {pubName}"
  match env.find? `LeanSwe.ConnectProxy.Internal.mkScopedApiM with
  | some (.defnInfo dv) =>
    let v := peelLambdas dv.value
    let args := v.getAppArgs
    let ok :=
      v.isAppOfArity `LeanSwe.ConnectProxy.ConnectProxyApiM.mk 8 &&
      (etaReduceExpr args[1]!).isConstOf `LeanSwe.ConnectProxy.Model.parseIpAddr &&
      (etaReduceExpr args[2]!).isConstOf `LeanSwe.ConnectProxy.Model.parseIpPrefix &&
      (etaReduceExpr args[3]!).isConstOf `LeanSwe.ConnectProxy.Model.isGlobalIp &&
      (etaReduceExpr args[4]!).isConstOf `LeanSwe.ConnectProxy.Model.allowsIp &&
      (etaReduceExpr args[5]!).isConstOf `LeanSwe.ConnectProxy.Model.parseConnectRequest &&
      (etaReduceExpr args[6]!).isConstOf `LeanSwe.ConnectProxy.Model.validateConfig &&
      args[7]!.getUsedConstants.contains `LeanSwe.ConnectProxy.Model.validateConfig &&
      exprUsesStructField `LeanSwe.ConnectProxy.ScopedProxyOpsM args[7]!
    if !ok then
      errs := errs.push "CPROXY_IMPL_WIRING: Internal.mkScopedApiM must wire Model.{parseIpAddr,parseIpPrefix,isGlobalIp,allowsIp,parseConnectRequest,validateConfig} and ScopedProxyOpsM.withProxy"
  | _ =>
    errs := errs.push "CPROXY_IMPL_WIRING: missing Internal.mkScopedApiM"
  match env.find? `LeanSwe.ConnectProxy.Internal.defaultScopedIoOps with
  | some (.defnInfo dv) =>
    let v := dv.value.consumeMData
    let args := v.getAppArgs
    let ok :=
      v.isAppOfArity `LeanSwe.ConnectProxy.ScopedProxyOpsM.mk 2 &&
      args[0]!.consumeMData.isConstOf ``IO &&
      (peelLambdas args[1]!).isAppOfArity `LeanSwe.ConnectProxy.SysBridge.withProxyIo 3
    if !ok then
      errs := errs.push "CPROXY_IMPL_WIRING: Internal.defaultScopedIoOps must wire SysBridge.withProxyIo"
  | _ =>
    errs := errs.push "CPROXY_IMPL_WIRING: missing Internal.defaultScopedIoOps"
  match env.find? `LeanSwe.ConnectProxy.SysBridge.withProxyIo with
  | some (.defnInfo dv) =>
    let used := dv.value.getUsedConstants
    if !used.contains `LeanSwe.ConnectProxy.Model.withValidProxyModel ||
        !used.contains `LeanSwe.ConnectProxy.SysBridge.mkIoRawOps then
      errs := errs.push "CPROXY_SYSBRIDGE_WIRING: SysBridge.withProxyIo must wire Model.withValidProxyModel and SysBridge.mkIoRawOps"
  | _ =>
    errs := errs.push "CPROXY_SYSBRIDGE_WIRING: missing SysBridge.withProxyIo"
  match env.find? `LeanSwe.ConnectProxy.SysBridge.mkIoRawOps with
  | some (.defnInfo dv) =>
    let used := dv.value.getUsedConstants
    if !used.contains `LeanSwe.ConnectProxy.SysBridge.createListener ||
        !used.contains `LeanSwe.ConnectProxy.SysBridge.defaultIoSysOps ||
        !used.contains `LeanSwe.ConnectProxy.SysBridge.runIoProxyLoop then
      errs := errs.push "CPROXY_SYSBRIDGE_WIRING: SysBridge.mkIoRawOps must wire createListener, defaultIoSysOps, and runIoProxyLoop"
  | _ =>
    errs := errs.push "CPROXY_SYSBRIDGE_WIRING: missing SysBridge.mkIoRawOps"
  match env.find? `LeanSwe.ConnectProxy.SysBridge.runIoProxyLoop with
  | some (.defnInfo _) =>
    let modSb := `LeanSwe.ConnectProxy.SysBridge
    let rootLoop := `LeanSwe.ConnectProxy.SysBridge.runIoProxyLoop
    if !usesConstWithinModule env modSb rootLoop `LeanSwe.ConnectProxy.SysBridge.pollAndStepTickM ||
        !usesConstWithinModule env modSb rootLoop `LeanSwe.ConnectProxy.SysBridge.defaultIoSysOps then
      errs := errs.push "CPROXY_SYSBRIDGE_WIRING: SysBridge.runIoProxyLoop must execute verified pollAndStepTickM over defaultIoSysOps"
  | _ =>
    errs := errs.push "CPROXY_SYSBRIDGE_WIRING: missing SysBridge.runIoProxyLoop"
  match env.find? `LeanSwe.ConnectProxy.SysBridge.defaultIoSysOps with
  | some (.defnInfo dv) =>
    let v := dv.value.consumeMData
    let used := dv.value.getUsedConstants
    let ok :=
      v.isAppOfArity `LeanSwe.ConnectProxy.SysBridge.CProxySysOpsM.mk 7 &&
      used.contains `LeanSwe.LinuxSyscall.Files.defaultOps &&
      used.contains `LeanSwe.LinuxSyscall.Net.defaultOps &&
      used.contains `LeanSwe.LinuxSyscall.Poll.defaultOps &&
      used.contains `LeanSwe.LinuxSyscall.Dns.defaultOps &&
      used.contains `LeanSwe.LinuxSyscall.TimeRand.defaultOps
    if !ok then
      errs := errs.push "CPROXY_SYSBRIDGE_WIRING: SysBridge.defaultIoSysOps must wire LinuxSyscall.{Files,Net,Poll,Dns,TimeRand}.defaultOps"
  | _ =>
    errs := errs.push "CPROXY_SYSBRIDGE_WIRING: missing SysBridge.defaultIoSysOps"
  match env.find? `LeanSwe.ConnectProxy.HealthySys.realBridgeTarget with
  | some (.defnInfo dv) =>
    let v := dv.value.consumeMData
    let args := v.getAppArgs
    if !v.isAppOfArity `LeanSwe.ConnectProxy.HealthySys.SysBridgeTarget.mk 12 then
      errs := errs.push "CPROXY_BRIDGE_TARGET_WIRING: HealthySys.realBridgeTarget must construct SysBridgeTarget.mk (arity 12)"
    else
      let listenBody := peelLambdas args[3]!
      let listenOk :=
        args[3]!.getUsedConstants.contains `LeanSwe.ConnectProxy.SysBridge.listenPollEvents &&
        (listenBody.getAppFn.consumeMData.constName? == some `LeanSwe.LinuxSyscall.Poll.PollEvents.pollin ||
          match listenBody with
          | .proj `LeanSwe.LinuxSyscall.Poll.PollEvents 0 inner =>
            inner.consumeMData.getAppFn.consumeMData.constName? == some `LeanSwe.ConnectProxy.SysBridge.listenPollEvents
          | _ => false)
      let fieldsOk :=
        (peelLambdas args[0]!).getAppFn.consumeMData.constName? == some `LeanSwe.ConnectProxy.SysBridge.createListener &&
        (peelLambdas args[1]!).getAppFn.consumeMData.constName? == some `LeanSwe.ConnectProxy.SysBridge.handleCompleteHead &&
        args[1]!.getUsedConstants.contains `LeanSwe.ConnectProxy.SysBridge.startDnsSync &&
        (peelLambdas args[2]!).getAppFn.consumeMData.constName? == some `LeanSwe.ConnectProxy.SysBridge.acceptNewClients &&
        listenOk &&
        (peelLambdas args[4]!).getAppFn.consumeMData.constName? == some `LeanSwe.ConnectProxy.SysBridge.buildPollBatchSync &&
        (peelLambdas args[5]!).getAppFn.consumeMData.constName? == some `LeanSwe.ConnectProxy.SysBridge.stepHandshake &&
        args[5]!.getUsedConstants.contains `LeanSwe.ConnectProxy.SysBridge.startDnsSync &&
        (peelLambdas args[6]!).getAppFn.consumeMData.constName? == some `LeanSwe.NetRelay.recvIntoRing &&
        (peelLambdas args[7]!).getAppFn.consumeMData.constName? == some `LeanSwe.NetRelay.flushRingNonblock &&
        (peelLambdas args[8]!).getAppFn.consumeMData.constName? == some `LeanSwe.ConnectProxy.Relay.stepBidirectionalRelay &&
        (peelLambdas args[9]!).getAppFn.consumeMData.constName? == some `LeanSwe.ConnectProxy.SysBridge.stepSyncSlot &&
        (peelLambdas args[10]!).getAppFn.consumeMData.constName? == some `LeanSwe.ConnectProxy.SysBridge.pollAndStepTickSync &&
        (peelLambdas args[11]!).getAppFn.consumeMData.constName? == some `LeanSwe.ConnectProxy.SysBridge.mkSyncRawOps
      if !fieldsOk then
        errs := errs.push "CPROXY_BRIDGE_TARGET_WIRING: HealthySys.realBridgeTarget fields must wire directly to SysBridge and Relay"
  | _ =>
    errs := errs.push "CPROXY_BRIDGE_TARGET_WIRING: missing HealthySys.realBridgeTarget"
  return errs

private def checkConnectProxyTrustedClosure
    (env : Environment)
    (repoDir : System.FilePath)
    (headAllPass headCanReach : Std.HashMap Name (Array Name)) : IO (Array String) := do
  let mut errs : Array String := checkConnectProxyWiring env
  for reqMod in connectProxyRequiredModules do
    if !env.header.moduleNames.contains reqMod then
      errs := errs.push s!"CPROXY_MISSING_REQUIRED_MODULE: {reqMod}"
  let csimpState := Lean.Compiler.CSimp.ext.getState env
  let mut cproxyMods : Array Name := #[]
  let mut queue : Array (Name × Bool × Bool × Name) := #[]
  for h : i in [0 : env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if m.components.take 2 == [`LeanSwe, `ConnectProxy] &&
        !isMutantModule m && nameLastStr m != "RuntimeTests" then
      cproxyMods := cproxyMods.push m
      let isProofs := m.components.contains `Proofs
      let fromSpecOrProof := isProofs || m == `LeanSwe.ConnectProxy.SpecTests
      let path := moduleToFilePath repoDir m
      match ← parseModuleCommands env path (allowMacroRecovery := isProofs) with
      | .error err => errs := errs.push s!"CPROXY_SOURCE_PARSE_ERR: {m} ({err})"
      | .ok cmds =>
        for stx in cmds do
          if let some synErr := checkConnectProxySourceCmd path isProofs stx then
            errs := errs.push synErr
            break
          if hasSyntaxKind ``Lean.Parser.Command.axiom stx then
            errs := errs.push s!"CUSTOM_AXIOM_FORBIDDEN: axiom declaration in {path}"
            break
          if hasIdentOrAtom isForbiddenMutantToken stx then
            errs := errs.push s!"FORBIDDEN_UNSAFE_OR_SORRY: {path} uses sorry/admit/native_decide/unsafe"
            break
      if let some data := env.header.moduleData[i]? then
        for imp in data.imports do
          let impMod := imp.module
          if isProjectModule impMod then
            let impOk :=
              if fromSpecOrProof then isAllowedConnectProxyAnyProjectMod impMod
              else isAllowedConnectProxyNonProofProjectMod impMod
            if !impOk then
              errs := errs.push s!"CPROXY_UNALLOWED_IMPORT: {m} imports {impMod}"
          else if !isAllowedClosureStdlibModule (m := impMod) then
            errs := errs.push s!"CPROXY_UNALLOWED_STDLIB_IMPORT: {m} imports {impMod}"
        for c in data.constants do
          queue := queue.push (m, false, fromSpecOrProof, c.name)
  for (pName, thms) in headAllPass.toList ++ headCanReach.toList do
    if pName.components.take 2 == [`LeanSwe, `ConnectProxy] then
      for t in thms do
        queue := queue.push (pName, false, true, t)
  let mut seen : Std.HashSet (Name × Bool × Bool) := {}
  let mut seenConst : Std.HashSet Name := {}
  while !queue.isEmpty do
    let (originMod, inStdImpl, fromSpecOrProof, cName) := queue.back!
    queue := queue.pop
    if seen.contains (cName, inStdImpl, fromSpecOrProof) then continue
    seen := seen.insert (cName, inStdImpl, fromSpecOrProof)
    seenConst := seenConst.insert cName
    let some cinfo := env.find? cName | continue
    if cinfo matches .axiomInfo _ then
      if !allowedAxioms.contains cName && !(inStdImpl && cName == `lcProof) then
        errs := errs.push s!"CPROXY_CLOSURE_AXIOM_FORBIDDEN: {cName} reachable from {originMod}"
      continue
    let cMod := env.getModuleIdxFor? cName |>.bind (env.header.moduleNames[·]?) |>.getD .anonymous
    if cMod == `Core.Assumptions && fromSpecOrProof then
      continue
    let projMod := isProjectModule cMod
    if let some implTarget := Lean.Compiler.getImplementedBy? env cName then
      let nextStd := inStdImpl || !projMod
      if !seen.contains (implTarget, nextStd, fromSpecOrProof) then
        queue := queue.push (originMod, nextStd, fromSpecOrProof, implTarget)
      if projMod then
        if !(← isCompilerGeneratedCtorIdx env cName implTarget cinfo) then
          errs := errs.push s!"CPROXY_CLOSURE_IMPLEMENTED_BY_FORBIDDEN: {cName} -> {implTarget} reachable from {originMod}"
    if let some csEntry := csimpState.map.find? cName then
      let nextStd := inStdImpl || !projMod
      if !seen.contains (csEntry.toDeclName, nextStd, fromSpecOrProof) then
        queue := queue.push (originMod, nextStd, fromSpecOrProof, csEntry.toDeclName)
      let thmMod := env.getModuleIdxFor? csEntry.thmName |>.bind (env.header.moduleNames[·]?) |>.getD .anonymous
      let toMod := env.getModuleIdxFor? csEntry.toDeclName |>.bind (env.header.moduleNames[·]?) |>.getD .anonymous
      if projMod || isProjectModule thmMod || isProjectModule toMod then
        errs := errs.push s!"CPROXY_CLOSURE_FORBIDDEN_CSIMP: {cName} -> {csEntry.toDeclName} via {csEntry.thmName} reachable from {originMod}"
    if projMod then
      let modOk :=
        if fromSpecOrProof then isAllowedConnectProxyAnyProjectMod cMod
        else isAllowedConnectProxyNonProofProjectMod cMod
      if !modOk then
        errs := errs.push s!"CPROXY_CLOSURE_UNALLOWED_MODULE: {cName} in {cMod} reachable from {originMod}"
      if let some expName := Lean.getExportNameFor? env cName then
        errs := errs.push s!"CPROXY_CLOSURE_FORBIDDEN_EXPORT: {cName} -> {expName} in {cMod}"
      if let .defnInfo v := cinfo then
        if v.safety != .safe then
          if !(← isAllowedCompilerUnsafeDef env cName v) then
            errs := errs.push s!"CPROXY_CLOSURE_FORBIDDEN_UNSAFE_DEF: {cName} in {cMod} reachable from {originMod}"
      if csimpState.thmNames.contains cName then
        errs := errs.push s!"CPROXY_CLOSURE_FORBIDDEN_CSIMP_THM: {cName} in {cMod} marked @[csimp]"
      if cinfo matches .opaqueInfo _ || (getExternAttrData? env cName).isSome then
        if !isAllowedConnectProxyProjectExtern env cMod cName cinfo then
          errs := errs.push s!"CPROXY_CLOSURE_UNALLOWED_EXTERN: {cName} in {cMod} reachable from {originMod}"
    else
      if cMod != .anonymous && !isAllowedClosureStdlibModule (m := cMod) then
        errs := errs.push s!"CPROXY_CLOSURE_UNALLOWED_STDLIB_MOD: {cName} in {cMod} reachable from {originMod}"
      if isForbiddenConnectProxyStdExtern cName cinfo (getExternAttrData? env cName) then
        errs := errs.push s!"CPROXY_CLOSURE_FORBIDDEN_STDLIB_HOST: {cName} in {cMod} reachable from {originMod}"
    for u in cinfo.type.getUsedConstants do
      if !seen.contains (u, inStdImpl, fromSpecOrProof) then
        queue := queue.push (originMod, inStdImpl, fromSpecOrProof, u)
    let val? := match cinfo with
      | .defnInfo v => some v.value
      | .thmInfo v => some v.value
      | .opaqueInfo v => some v.value
      | _ => none
    if let some val := val? then
      for u in val.getUsedConstants do
        if !seen.contains (u, inStdImpl, fromSpecOrProof) then
          queue := queue.push (originMod, inStdImpl, fromSpecOrProof, u)
    let extra : List Name := match cinfo with
      | .ctorInfo v => [v.induct]
      | .recInfo v => v.all
      | .inductInfo v => v.all ++ v.ctors
      | _ => []
    for u in extra do
      if !seen.contains (u, inStdImpl, fromSpecOrProof) then
        queue := queue.push (originMod, inStdImpl, fromSpecOrProof, u)
  IO.println s!"TRUSTED_CLOSURE: bundle=LeanSwe.ConnectProxy modules={cproxyMods.size} visited={seenConst.size} errors={errs.size}"
  return errs

private inductive DagModuleRole where
  | types
  | model
  | specTests
  | impl
  | sysBridge
  | iface
  | proofs
  | specMutants
  | runtimeTests
  | testSupport
  | umbrella
  | other
  deriving BEq, Inhabited

private def DagModuleRole.label : DagModuleRole → String
  | .types => "Types"
  | .model => "Model"
  | .specTests => "SpecTests"
  | .impl => "Impl"
  | .sysBridge => "SysBridge"
  | .iface => "Interface"
  | .proofs => "Proofs"
  | .specMutants => "SpecMutants"
  | .runtimeTests => "RuntimeTests"
  | .testSupport => "TestSupport"
  | .umbrella => "Umbrella"
  | .other => "Other"

private def dagPkgMarkerSegs : Array String := #[
  "Types", "Model", "Impl", "Interface", "SpecTests", "Properties",
  "SpecMutants", "RuntimeTests", "Proofs", "SysBridge"
]

private def dagSubdirExcludeSegs : Array Name := #[
  `Proofs, `Model, `SpecTests, `Properties, `SpecMutants, `RuntimeTests,
  `Impl, `Interface, `SysBridge, `Host, `Init, `Aeneas, `TestSupport
]

private def isNamePrefixComps (pfx comps : List Name) : Bool :=
  pfx.length <= comps.length && comps.take pfx.length == pfx

private def discoverDagPackages (modNames : Array Name) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut pkgs : Array Name := #[]
  for m in modNames do
    if m.getRoot != `LeanSwe || m == `LeanSwe then
      continue
    match m with
    | .str p seg =>
      if dagPkgMarkerSegs.contains seg && p.getRoot == `LeanSwe && p != `LeanSwe then
        if !(p.components.any dagSubdirExcludeSegs.contains) && !seen.contains p then
          seen := seen.insert p
          pkgs := pkgs.push p
    | _ => pure ()
  return pkgs.qsort fun a b =>
    let la := a.components.length
    let lb := b.components.length
    if la != lb then la > lb else a.toString < b.toString

private def dagPkgOf (knownPkgs : Array Name) (m : Name) : Name := Id.run do
  if m == `LeanSwe then
    return `LeanSwe
  let mc := m.components
  for p in knownPkgs do
    if isNamePrefixComps p.components mc then
      return p
  if mc.take 2 == [`LeanSwe, `LinuxSyscall] && mc.length >= 3 then
    return Name.str `LeanSwe.LinuxSyscall mc[2]!.getString!
  if mc.length >= 2 then
    return Name.str `LeanSwe mc[1]!.getString!
  return m

private def dagRoleOf (knownPkgs : Array Name) (m : Name) : DagModuleRole :=
  if m == `LeanSwe then .umbrella
  else if m.getRoot != `LeanSwe then .other
  else if cryptoHashVectorModules.contains m then .proofs
  else
    let pkg := dagPkgOf knownPkgs m
    if pkg == `LeanSwe.LinuxSyscall.TestSupport then .testSupport
    else
      let rem := m.components.drop pkg.components.length
      if rem.isEmpty then .umbrella
      else
        let head := rem.head!
        let headStr := head.toString
        let last := rem.getLast!
        let lastStr := last.toString
        if rem.contains `Proofs || headStr.endsWith "Proofs" || lastStr.endsWith "Proofs" ||
            head == `Verified || last == `Verified then
          .proofs
        else if head == `SpecMutants || rem.contains `SpecMutants then
          .specMutants
        else if head == `RuntimeTests || rem.contains `RuntimeTests then
          .runtimeTests
        else if head == `SpecTests || head == `Properties ||
            rem.contains `SpecTests || rem.contains `Properties then
          .specTests
        else if head == `Types then
          .types
        else if head == `Model || m == `LeanSwe.LinuxSyscall.Files.Seed then
          .model
        else if head == `Interface then
          .iface
        else if head == `SysBridge then
          .sysBridge
        else if head == `Host then
          if last == `SysBridge then .sysBridge else .impl
        else if rem.contains `Aeneas then
          if last == `Types || last == `TypesExternal then .types
          else if last == `Model then .model
          else .impl
        else if head == `Init then
          .impl
        else if head == `Impl || head == `Relay || head == `HealthySys || head == `InitData then
          .impl
        else
          .other

private def isLazyAuxModelSuffix (s : String) : Bool :=
  s == "eq_def" || s == "eq_unfold" || s == "splitter" || s == "elim" ||
    s == "congr_simp" || s == "fun_cases" || s == "induct" || s == "induct_unfolding" ||
    s == "sizeOf_spec" || s == "inj" || s == "injEq" || s == "noConfusion" ||
    s == "noConfusionType" || s == "below" || s == "brecOn" || s == "else_eq" ||
    (s.startsWith "eq_" && !(s.drop 3).isEmpty && (s.drop 3).all Char.isDigit) ||
    (s.startsWith "congr_eq_" && !(s.drop 9).isEmpty && (s.drop 9).all Char.isDigit) ||
    (s.startsWith "match_" && !(s.drop 6).isEmpty && (s.drop 6).all Char.isDigit) ||
    (s.startsWith "_sparseCasesOn_" && !(s.drop 15).isEmpty && (s.drop 15).all Char.isDigit) ||
    (s.startsWith "_proof_" && !(s.drop 7).isEmpty && (s.drop 7).all Char.isDigit)

private def isModelNamespaceDeclName (uName : Name) : Bool :=
  let comps := uName.components
  if comps.head? != some `LeanSwe then false
  else
    let rec scan : List Name → Bool
      | [] => false
      | seg :: rest =>
        if seg == `Proofs || seg.toString.endsWith "Proofs" then false
        else if seg == `Model then true
        else scan rest
    scan (comps.drop 1)

private def hasNonProofUserDeclPrefix (nonProofUsers : Std.HashSet Name) (u : Name) : Bool :=
  let rec go : Nat → Name → Bool
    | 0, _ | _, .anonymous => false
    | k + 1, .str p _ => if nonProofUsers.contains p then true else go k p
    | k + 1, .num p _ => go k p
  go 8 u

private def isCompilerLazyModelAux (env : Environment) (nonProofUsers : Std.HashSet Name) (c : ConstantInfo) : Bool :=
  if (Lean.declRangeExt.find? env c.name).isSome then false
  else
    let u := (privateToUserName? c.name).getD c.name
    isLazyAuxModelSuffix u.getString! && hasNonProofUserDeclPrefix nonProofUsers u

private def stableConstLabel (n : Name) : String :=
  match privateToUserName? n with
  | some u => s!"private:{u}"
  | none => n.toString

private def computeLeanSweTransImports (env : Environment) : Array (Std.HashSet Nat) := Id.run do
  let n := env.header.moduleNames.size
  let mut idxMap : Std.HashMap Name Nat := Std.HashMap.emptyWithCapacity n
  for h : i in [0 : n] do
    idxMap := idxMap.insert env.header.moduleNames[i] i
  let mut adj : Array (Array Nat) := Array.replicate n #[]
  for i in [0 : n] do
    let m := env.header.moduleNames[i]!
    if !isProjectModule m || m == `LeanSwe then continue
    let some data := env.header.moduleData[i]? | continue
    let mut deps : Array Nat := #[]
    for imp in data.imports do
      if let some j := idxMap.get? imp.module then
        let jm := env.header.moduleNames[j]!
        if isProjectModule jm && jm != `LeanSwe then
          deps := deps.push j
    adj := adj.set! i deps
  let mut trans : Array (Std.HashSet Nat) := Array.replicate n {}
  for i in [0 : n] do
    let m := env.header.moduleNames[i]!
    if m.getRoot != `LeanSwe || m == `LeanSwe then continue
    let mut visited : Std.HashSet Nat := {}
    let mut leanSweSeen : Std.HashSet Nat := {}
    let mut stack : Array Nat := adj[i]!
    while !stack.isEmpty do
      let j := stack.back!
      stack := stack.pop
      if visited.contains j then continue
      visited := visited.insert j
      if env.header.moduleNames[j]!.getRoot == `LeanSwe then
        leanSweSeen := leanSweSeen.insert j
      for k in adj[j]! do
        if !visited.contains k then
          stack := stack.push k
    trans := trans.set! i leanSweSeen
  return trans

private structure DagAuditReport where
  violations : Std.HashMap String String := {}
  sigProofCounts : Std.HashMap String (Nat × Array String) := {}
  checkedModules : Nat := 0

private def recordDagViolation (m : Std.HashMap String String) (key msg : String) :
    Std.HashMap String String :=
  if m.contains key then m else m.insert key msg

private def recordSigProofHit (m : Std.HashMap String (Nat × Array String)) (key thmName : String) :
    Std.HashMap String (Nat × Array String) :=
  match m.get? key with
  | some (cnt, sample) =>
    let sample' := if sample.size < 3 && !sample.contains thmName then sample.push thmName else sample
    m.insert key (cnt + 1, sample')
  | none => m.insert key (1, #[thmName])

private def auditImportDagEnv
    (env : Environment)
    (includeMod : Name → Bool)
    (allPassMap canReachMap : Std.HashMap Name (Array Name))
    (scanPublicAllPassDirect : Bool := false) : DagAuditReport := Id.run do
  let knownPkgs := discoverDagPackages env.header.moduleNames
  let trans := computeLeanSweTransImports env
  let mut nonProofUsers : Std.HashSet Name := {}
  for h : i in [0 : env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if m.getRoot != `LeanSwe || m == `LeanSwe then continue
    if dagRoleOf knownPkgs m == .proofs then continue
    let some data := env.header.moduleData[i]? | continue
    for c in data.constants do
      let u := (privateToUserName? c.name).getD c.name
      nonProofUsers := nonProofUsers.insert u
  let mut qualifyingThms : Std.HashSet Name := {}
  for (_, ts) in allPassMap.toList do
    for t in ts do
      qualifyingThms := qualifyingThms.insert t
  for (_, ts) in canReachMap.toList do
    for t in ts do
      qualifyingThms := qualifyingThms.insert t
  let modOf (c : Name) : Name :=
    env.getModuleIdxFor? c |>.bind (env.header.moduleNames[·]?) |>.getD .anonymous
  let mut violations : Std.HashMap String String := {}
  let mut sigCounts : Std.HashMap String (Nat × Array String) := {}
  let mut checkedModules : Nat := 0
  for h : i in [0 : env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if m.getRoot != `LeanSwe || m == `LeanSwe || !includeMod m then continue
    let some data := env.header.moduleData[i]? | continue
    checkedModules := checkedModules + 1
    let pkgM := dagPkgOf knownPkgs m
    let roleM := dagRoleOf knownPkgs m
    for j in trans[i]! do
      let t := env.header.moduleNames[j]!
      if t == m then continue
      let pkgT := dagPkgOf knownPkgs t
      let roleT := dagRoleOf knownPkgs t
      if pkgM == pkgT then
        if (roleM == .types || roleM == .model || roleM == .specTests) &&
            (roleT == .impl || roleT == .sysBridge || roleT == .iface || roleT == .proofs ||
             roleT == .specMutants || roleT == .runtimeTests || roleT == .testSupport || roleT == .other) then
          let key := s!"WITHIN|{m}|{t}"
          let msg := s!"DAG_WITHIN_VIOLATION: {m} ({roleM.label}) transitively imports same-package {t} ({roleT.label})"
          violations := recordDagViolation violations key msg
        if (roleM == .impl || roleM == .sysBridge || roleM == .iface) &&
            (roleT == .proofs || roleT == .specTests || roleT == .specMutants || roleT == .runtimeTests) then
          let key := s!"WITHIN|{m}|{t}"
          let msg := s!"DAG_WITHIN_VIOLATION: {m} ({roleM.label}) transitively imports same-package {t} ({roleT.label})"
          violations := recordDagViolation violations key msg
      else
        if (roleM == .types || roleM == .model || roleM == .impl || roleM == .sysBridge || roleM == .iface) &&
            (roleT == .proofs || roleT == .specTests || roleT == .specMutants || roleT == .runtimeTests) then
          let key := s!"TRANS_LEAK|{m}|{t}"
          let msg := s!"DAG_TRANS_LEAK: {m} ({roleM.label}) transitively imports cross-package {t} ({roleT.label})"
          violations := recordDagViolation violations key msg
        if roleM == .specTests && (roleT == .proofs || roleT == .specMutants || roleT == .runtimeTests) then
          let key := s!"TRANS_LEAK|{m}|{t}"
          let msg := s!"DAG_TRANS_LEAK: {m} ({roleM.label}) transitively imports cross-package {t} ({roleT.label})"
          violations := recordDagViolation violations key msg
    let mut directCrossNonPublic : Std.HashSet Name := {}
    for imp in data.imports do
      let t := imp.module
      if t.getRoot != `LeanSwe || t == `LeanSwe then continue
      let pkgT := dagPkgOf knownPkgs t
      let roleT := dagRoleOf knownPkgs t
      if pkgM != pkgT && roleT != .types && roleT != .model && roleT != .iface then
        directCrossNonPublic := directCrossNonPublic.insert t
        let key := s!"CROSS|{m}|{t}"
        let msg := s!"DAG_CROSS_IMPORT_VIOLATION: {m} ({roleM.label}) directly imports cross-package {t} ({roleT.label}; only Types/Model/Interface allowed)"
        violations := recordDagViolation violations key msg
    for c in data.constants do
      let uName := (privateToUserName? c.name).getD c.name
      if roleM == .proofs && isModelNamespaceDeclName uName && !isCompilerLazyModelAux env nonProofUsers c then
        let key := s!"PROOF_NS_MODEL|{m}|{uName}"
        let msg := s!"PROOF_MODEL_NS_FORBIDDEN: {m} defines {stableConstLabel c.name} inside Model namespace"
        violations := recordDagViolation violations key msg
      let usedTy := c.type.getUsedConstants
      let usedVal := match c with
        | .defnInfo v => v.value.getUsedConstants
        | .opaqueInfo v => v.value.getUsedConstants
        | .thmInfo v => v.value.getUsedConstants
        | _ => #[]
      if roleM == .specTests then
        for u in usedTy ++ usedVal do
          let um := modOf u
          if um.getRoot == `LeanSwe && dagRoleOf knownPkgs um == .proofs then
            let uLbl := stableConstLabel u
            let key := s!"SPEC_PROOF_CONST|{m}|{stableConstLabel c.name}|{um}|{uLbl}"
            let msg := s!"PROOF_CONST_IN_SPEC: {stableConstLabel c.name} in {m} references proof constant {uLbl} from {um}"
            violations := recordDagViolation violations key msg
      if roleM != .specMutants && roleM != .runtimeTests &&
          !isPrivateName c.name && !c.name.isInternalOrNum && !env.isProjectionFn c.name then
        let short := c.name.getString!
        let isRefinesOrObeys := short == "refines_model" || short == "obeys_model"
        if isRefinesOrObeys then
          let mut seenU : Std.HashSet String := {}
          for u in c.type.getUsedConstants do
            let um := modOf u
            if um.getRoot == `LeanSwe && dagRoleOf knownPkgs um == .proofs then
              let uLbl := stableConstLabel u
              if !seenU.contains uLbl then
                seenU := seenU.insert uLbl
                let key := s!"REFINES_PROOF_CONST|{c.name}|{um}|{uLbl}"
                let msg := s!"PROOF_CONST_IN_SIGNATURE: {c.name} in {m} uses proof constant {uLbl} from {um}"
                violations := recordDagViolation violations key msg
        else if let .thmInfo v := c then
          let isTrackedPromiseThm :=
            qualifyingThms.contains c.name ||
            (scanPublicAllPassDirect && v.type.getUsedConstants.any fun k => k == `Core.AllPass || k == `Core.CanReach)
          if isTrackedPromiseThm then
            let mut seenU : Std.HashSet String := {}
            for u in v.type.getUsedConstants do
              let um := modOf u
              if um.getRoot == `LeanSwe && dagRoleOf knownPkgs um == .proofs then
                let uLbl := stableConstLabel u
                let sKey := s!"{m}|{um}|{uLbl}"
                if !seenU.contains sKey then
                  seenU := seenU.insert sKey
                  sigCounts := recordSigProofHit sigCounts sKey c.name.toString
      if roleM != .proofs then
        for u in usedTy ++ usedVal do
          let um := modOf u
          if um.getRoot == `LeanSwe && um != `LeanSwe then
            let pkgU := dagPkgOf knownPkgs um
            if pkgU != pkgM then
              let roleU := dagRoleOf knownPkgs um
              if roleU != .types && roleU != .model && roleU != .iface then
                if !directCrossNonPublic.contains um then
                  let key := s!"CROSS_REF|{m}|{um}"
                  let msg := s!"DAG_CROSS_REACHIN_VIOLATION: {m} ({roleM.label}) reaches into cross-package {um} ({roleU.label}) via {stableConstLabel c.name} -> {stableConstLabel u}"
                  violations := recordDagViolation violations key msg
              else
                let uUser := (privateToUserName? u).getD u
                if uUser.components.contains `Internal then
                  let key := s!"CROSS_INTERNAL|{m}|{um}|{uUser}"
                  let msg := s!"DAG_CROSS_INTERNAL_REACHIN: {m} ({roleM.label}) references cross-package internal constant {uUser} in {um}"
                  violations := recordDagViolation violations key msg
  return { violations, sigProofCounts := sigCounts, checkedModules }

/-- Shrinking ratchet allowlist of pre-existing import-DAG violations seeded at commit `84750ac`
(after removing the unused `import LeanSwe.LinuxSyscall.Net.Interface` from
`LeanSwe/LinuxSyscall/Net/Model/State.lean`). Every entry must stay active; removing a listed
violation forces removing its entry from this table, and any new violation fails the audit gate. -/
private def importDagAllowlist : Array String := #[
  "CROSS|LeanSwe.CmdLine.Proofs.ErrorBounds|LeanSwe.EnvVars.Proofs",
  "CROSS|LeanSwe.Compress.Impl|LeanSwe.Process.Impl",
  "CROSS|LeanSwe.Compress.Interface|LeanSwe.Process.SysBridge",
  "CROSS|LeanSwe.ConnectProxy.Proofs.HealthyWitness|LeanSwe.LinuxSyscall.Dns.Proofs",
  "CROSS|LeanSwe.ConnectProxy.Proofs.HealthyWitness|LeanSwe.LinuxSyscall.TimeRand.Proofs",
  "CROSS|LeanSwe.ConnectProxy.Proofs.SysBridgeCoreProofs|LeanSwe.LinuxSyscall.Dns.Proofs",
  "CROSS|LeanSwe.ConnectProxy.Proofs.SysBridgeCoreProofs|LeanSwe.LinuxSyscall.Net.Proofs.HealthyStep",
  "CROSS|LeanSwe.ConnectProxy.Proofs.SysBridgeCoreProofs|LeanSwe.LinuxSyscall.Poll.Proofs",
  "CROSS|LeanSwe.ConnectProxy.Proofs.SysBridgeCoreProofs|LeanSwe.NetRelay.Proofs",
  "CROSS|LeanSwe.CryptoHash.Proofs|LeanSwe.CryptoHash.Raw.Proofs",
  "CROSS|LeanSwe.EnvVars.Proofs|LeanSwe.EnvVars.Raw.Proofs",
  "CROSS|LeanSwe.Fs.RuntimeTests|LeanSwe.Process.SysBridge",
  "CROSS|LeanSwe.Git.Proofs.ImpossibleProofs|LeanSwe.EnvVars.Proofs",
  "CROSS|LeanSwe.Git.Proofs.ImpossibleProofs|LeanSwe.Process.Impl",
  "CROSS|LeanSwe.Git.Proofs.ImpossibleProofs|LeanSwe.Process.Proofs.EndToEnd",
  "CROSS|LeanSwe.Process.Proofs.HealthySimBase|LeanSwe.LinuxSyscall.Files.Proofs",
  "CROSS|LeanSwe.Process.Proofs.HealthySimBase|LeanSwe.LinuxSyscall.Process.Proofs",
  "CROSS|LeanSwe.Process.Proofs.HealthySimBase|LeanSwe.LinuxSyscall.TimeRand.Proofs",
  "CROSS|LeanSwe.Process.Proofs.HealthyStep|LeanSwe.LinuxSyscall.Files.Proofs.HealthyStep",
  "CROSS|LeanSwe.Process.Proofs.HealthyStep|LeanSwe.LinuxSyscall.Process.Proofs.HealthyStep",
  "CROSS|LeanSwe.ProcessSandbox.Host.Bwrap|LeanSwe.ProcessSandbox.Raw.Impl",
  "CROSS|LeanSwe.ProcessSandbox.Host.StreamIo|LeanSwe.Process.SysBridge",
  "CROSS|LeanSwe.ProcessSandbox.Host.StreamIo|LeanSwe.ProcessSandbox.Raw.Impl",
  "CROSS|LeanSwe.ProcessSandbox.Host.SysBridge|LeanSwe.ProcessSandbox.Raw.Impl",
  "CROSS|LeanSwe.ProcessSandbox.Impl|LeanSwe.ProcessSandbox.Seccomp.Impl",
  "CROSS|LeanSwe.ProcessSandbox.Proofs.SeccompApiProofs|LeanSwe.ProcessSandbox.Seccomp.Impl",
  "CROSS|LeanSwe.ProcessSandbox.Proofs.SeccompApiProofs|LeanSwe.ProcessSandbox.Seccomp.Proofs",
  "CROSS|LeanSwe.ProcessSandbox.Proofs.SeccompBytesLemma|LeanSwe.ProcessSandbox.Seccomp.Impl",
  "CROSS|LeanSwe.ProcessSandbox.Raw.Interface|LeanSwe.ProcessSandbox.Host.SysBridge",
  "CROSS|LeanSwe.ProcessSandbox.Raw.RuntimeTests|LeanSwe.ProcessSandbox.Host.Bwrap",
  "CROSS|LeanSwe.SlotPool.RuntimeTests|LeanSwe.Fs.Impl",
  "CROSS|LeanSwe.SlotPool.RuntimeTests|LeanSwe.Process.SysBridge",
  "CROSS|LeanSwe.Sqlite.Proofs|LeanSwe.Sqlite.Raw.Proofs",
  "CROSS|LeanSwe.TempDir.RuntimeTests|LeanSwe.Process.SysBridge",
  "CROSS|LeanSwe.Time.RuntimeTests|LeanSwe.LinuxSyscall.TestSupport.Seccomp",
  "CROSS|LeanSwe.Toml.Proofs.Core|LeanSwe.NumParse.SpecTests",
  "CROSS|LeanSwe.Toml.Proofs.FormatBridge|LeanSwe.NumParse.SpecTests",
  "CROSS|LeanSwe.Toml.Proofs|LeanSwe.NumParse.Proofs",
  "CROSS|LeanSwe.Toml.Proofs|LeanSwe.NumParse.SpecTests",
  "CROSS|LeanSwe.Uuid.RuntimeTests|LeanSwe.LinuxSyscall.TestSupport.Seccomp",
  "CROSS_REF|LeanSwe.Compress.RuntimeTests|LeanSwe.Process.SysBridge",
  "WITHIN|LeanSwe.ConnectProxy.SpecTests|LeanSwe.ConnectProxy.HealthySys",
  "WITHIN|LeanSwe.ConnectProxy.SpecTests|LeanSwe.ConnectProxy.Relay",
  "WITHIN|LeanSwe.ConnectProxy.SpecTests|LeanSwe.ConnectProxy.SysBridge",
  "WITHIN|LeanSwe.LinuxSyscall.Files.SpecTests|LeanSwe.LinuxSyscall.Files.Impl",
  "WITHIN|LeanSwe.LinuxSyscall.Files.SpecTests|LeanSwe.LinuxSyscall.Files.Interface",
  "WITHIN|LeanSwe.LinuxSyscall.Passwd.SpecTests|LeanSwe.LinuxSyscall.Passwd.Impl",
  "WITHIN|LeanSwe.LinuxSyscall.Passwd.SpecTests|LeanSwe.LinuxSyscall.Passwd.Interface",
  "WITHIN|LeanSwe.LinuxSyscall.Process.SpecTests|LeanSwe.LinuxSyscall.Process.Impl",
  "WITHIN|LeanSwe.LinuxSyscall.Process.SpecTests|LeanSwe.LinuxSyscall.Process.Interface",
  "WITHIN|LeanSwe.PostFork.Aeneas.Model|LeanSwe.PostFork.Aeneas.FunsExternal",
  "WITHIN|LeanSwe.PostFork.SpecTests|LeanSwe.PostFork.Aeneas.Api",
  "WITHIN|LeanSwe.PostFork.SpecTests|LeanSwe.PostFork.Aeneas.Bridge",
  "WITHIN|LeanSwe.PostFork.SpecTests|LeanSwe.PostFork.Aeneas.Funs",
  "WITHIN|LeanSwe.PostFork.SpecTests|LeanSwe.PostFork.Aeneas.FunsExternal",
  "WITHIN|LeanSwe.PostFork.SpecTests|LeanSwe.PostFork.Impl",
  "WITHIN|LeanSwe.Process.SpecTests|LeanSwe.Process.SysBridge"
]

/-- Shrinking ratchet allowlist of pre-existing `*.Proofs*`-defined constants referenced in
qualifying `Core.AllPass`/`Core.CanReach` promised theorem signatures (`thmMod|proofMod|const`,
paired with the exact active theorem count at `84750ac`). Any new constant, increased count, or
stale/lower count fails the gate so the table strictly shrinks as proof-local mock helpers move
into `Model.lean`. -/
private def sigProofConstAllowlist : Array (String × Nat) := #[
  ("LeanSwe.Fs.Proofs.AtomicWriteProofs|LeanSwe.Fs.Proofs.VfsShared|LeanSwe.Fs.Proofs.VfsState", 48),
  ("LeanSwe.Fs.Proofs.AtomicWriteProofs|LeanSwe.Fs.Proofs.VfsShared|LeanSwe.Fs.Proofs.vfsApi", 6),
  ("LeanSwe.Fs.Proofs.AtomicWriteProofs|LeanSwe.Fs.Proofs.VfsShared|LeanSwe.Fs.Proofs.vfsOps", 42),
  ("LeanSwe.Fs.Proofs.CopyTreeProofs|LeanSwe.Fs.Proofs.VfsShared|LeanSwe.Fs.Proofs.VfsState", 14),
  ("LeanSwe.Fs.Proofs.CopyTreeProofs|LeanSwe.Fs.Proofs.VfsShared|LeanSwe.Fs.Proofs.vfsApi", 14),
  ("LeanSwe.Fs.Proofs.LockProofs|LeanSwe.Fs.Proofs.VfsShared|LeanSwe.Fs.Proofs.VfsState", 26),
  ("LeanSwe.Fs.Proofs.LockProofs|LeanSwe.Fs.Proofs.VfsShared|LeanSwe.Fs.Proofs.vfsApi", 26),
  ("LeanSwe.LinuxSyscall.Files.Proofs.ExecCases|LeanSwe.LinuxSyscall.Files.Proofs.ExecCases|LeanSwe.LinuxSyscall.Files.lroState", 1),
  ("LeanSwe.LinuxSyscall.Files.Proofs|LeanSwe.LinuxSyscall.Files.Proofs.ExecCases|LeanSwe.LinuxSyscall.Files.lroState", 2),
  ("LeanSwe.LinuxSyscall.Net.Proofs.CodecsAndBounds|LeanSwe.LinuxSyscall.Net.Proofs.CodecsAndBounds|private:LeanSwe.LinuxSyscall.Net.dummyRawNetOps", 1),
  ("LeanSwe.LinuxSyscall.Poll.Proofs|LeanSwe.LinuxSyscall.Poll.Proofs|private:LeanSwe.LinuxSyscall.Poll.dummyRawPollOps", 1),
  ("LeanSwe.LinuxSyscall.Sandbox.Proofs.Ops|LeanSwe.LinuxSyscall.Sandbox.Proofs.Ops|private:LeanSwe.LinuxSyscall.Sandbox.unprivInitWithHostFds", 1),
  ("LeanSwe.Process.Proofs.EndToEnd|LeanSwe.Process.Proofs.EndToEnd|LeanSwe.Process.Proofs.healthySimApi", 1),
  ("LeanSwe.Process.Proofs.EndToEnd|LeanSwe.Process.Proofs.HealthySimBase|LeanSwe.Process.Proofs.HealthySimState", 1),
  ("LeanSwe.Process.Proofs|LeanSwe.Process.Proofs.EndToEnd|LeanSwe.Process.Proofs.healthySimApi", 34),
  ("LeanSwe.Process.Proofs|LeanSwe.Process.Proofs.HealthySimBase|LeanSwe.Process.Proofs.HealthySimState", 34),
  ("LeanSwe.ProcessSandbox.Raw.Proofs|LeanSwe.ProcessSandbox.Raw.Proofs|LeanSwe.ProcessSandbox.Raw.Proofs.MockRawState", 8),
  ("LeanSwe.ProcessSandbox.Raw.Proofs|LeanSwe.ProcessSandbox.Raw.Proofs|LeanSwe.ProcessSandbox.Raw.Proofs.mockRawOps", 8),
  ("LeanSwe.TempDir.Proofs.LockedProofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.TempDirMockState", 6),
  ("LeanSwe.TempDir.Proofs.LockedProofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.mockEnv", 4),
  ("LeanSwe.TempDir.Proofs.LockedProofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.mockEnvEx", 2),
  ("LeanSwe.TempDir.Proofs.LockedProofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.mockFs", 6),
  ("LeanSwe.TempDir.Proofs.LockedProofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.mockFsEx", 2),
  ("LeanSwe.TempDir.Proofs.LockedProofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.mockTime", 4),
  ("LeanSwe.TempDir.Proofs.LockedProofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.mockTimeEx", 2),
  ("LeanSwe.TempDir.Proofs.LockedProofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.mockUuid", 6),
  ("LeanSwe.TempDir.Proofs.LockedProofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.mockUuidEx", 2),
  ("LeanSwe.TempDir.Proofs.WithTempDirProofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.TempDirMockState", 14),
  ("LeanSwe.TempDir.Proofs.WithTempDirProofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.mockEnv", 14),
  ("LeanSwe.TempDir.Proofs.WithTempDirProofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.mockFs", 14),
  ("LeanSwe.TempDir.Proofs.WithTempDirProofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.mockTime", 14),
  ("LeanSwe.TempDir.Proofs.WithTempDirProofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.mockUuid", 14),
  ("LeanSwe.TempDir.Proofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.TempDirMockState", 10),
  ("LeanSwe.TempDir.Proofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.mockEnv", 10),
  ("LeanSwe.TempDir.Proofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.mockFs", 10),
  ("LeanSwe.TempDir.Proofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.mockTime", 10),
  ("LeanSwe.TempDir.Proofs|LeanSwe.TempDir.Proofs.Shared|LeanSwe.TempDir.Proofs.mockUuid", 10)
]

private def mergeDagReports (a b : DagAuditReport) : DagAuditReport := Id.run do
  let mut v := a.violations
  for (k, msg) in b.violations.toList do
    v := recordDagViolation v k msg
  let mut sc := a.sigProofCounts
  for (k, (cnt, samples)) in b.sigProofCounts.toList do
    sc := match sc.get? k with
      | some (prev, pSamples) =>
        let merged := samples.foldl (fun acc s => if acc.size < 3 && !acc.contains s then acc.push s else acc) pSamples
        sc.insert k (prev + cnt, merged)
      | none =>
        let capped := samples.foldl (fun acc s => if acc.size < 3 && !acc.contains s then acc.push s else acc) #[]
        sc.insert k (cnt, capped)
  return { violations := v, sigProofCounts := sc, checkedModules := a.checkedModules + b.checkedModules }

private def encodeDagReportWireLines (rep : DagAuditReport) : Array String := Id.run do
  let mut lines : Array String := #[]
  for (k, msg) in rep.violations.toList do
    lines := lines.push s!"PFW_DAG_V:{k}\t{msg}"
  for (k, (cnt, samples)) in rep.sigProofCounts.toList do
    lines := lines.push s!"PFW_DAG_S:{k}\t{cnt}\t{String.intercalate "," samples.toList}"
  lines := lines.push s!"PFW_DAG_MODS:{rep.checkedModules}"
  return lines

private def parseDagWireLine? (ln : String) : Option DagAuditReport :=
  if ln.startsWith "PFW_DAG_V:" then
    let body := (ln.drop 10).toString
    match body.splitOn "\t" with
    | k :: rest =>
      let msg := String.intercalate "\t" rest
      some { violations := recordDagViolation {} k msg }
    | [] => none
  else if ln.startsWith "PFW_DAG_S:" then
    let body := (ln.drop 10).toString
    match body.splitOn "\t" with
    | [k, cntStr, sampleCsv] =>
      let cnt := cntStr.toNat!
      let samples := (sampleCsv.splitOn ",").filter (!·.isEmpty) |>.toArray
      some { sigProofCounts := ({} : Std.HashMap String (Nat × Array String)).insert k (cnt, samples) }
    | _ => none
  else if ln.startsWith "PFW_DAG_MODS:" then
    some { checkedModules := (ln.drop 13).toString.toNat! }
  else
    none

private def decodeDagReportWireLines (lines : Array String) : DagAuditReport :=
  lines.foldl (init := {}) fun acc ln =>
    match parseDagWireLine? ln with
    | some delta => mergeDagReports acc delta
    | none => acc

private def evaluateDagRatchetWith
    (allowEdges : Array String)
    (allowSigs : Array (String × Nat))
    (rep : DagAuditReport) : Array String := Id.run do
  let mut errs : Array String := #[]
  let mut allowSet : Std.HashSet String := {}
  for entry in allowEdges do
    if allowSet.contains entry then
      errs := errs.push s!"DUPLICATE_DAG_ALLOWLIST_ENTRY: {entry}"
    allowSet := allowSet.insert entry
  let obsKeys := (rep.violations.toList.map (·.1)).toArray.qsort (· < ·)
  for k in obsKeys do
    if !allowSet.contains k then
      errs := errs.push s!"{rep.violations.getD k k} [key={k}]"
  for entry in allowEdges do
    if !rep.violations.contains entry then
      errs := errs.push s!"STALE_IMPORT_DAG_ALLOWLIST: {entry} no longer occurs; remove it from importDagAllowlist"
  let mut sigAllowMap : Std.HashMap String Nat := {}
  for (k, expCnt) in allowSigs do
    if sigAllowMap.contains k then
      errs := errs.push s!"DUPLICATE_SIG_PROOF_ALLOWLIST_ENTRY: {k}"
    sigAllowMap := sigAllowMap.insert k expCnt
  let obsSigKeys := (rep.sigProofCounts.toList.map (·.1)).toArray.qsort (· < ·)
  for k in obsSigKeys do
    let (obsCnt, samples) := rep.sigProofCounts.getD k (0, #[])
    match sigAllowMap.get? k with
    | none =>
      let sampleStr := String.intercalate ", " samples.toList
      errs := errs.push s!"PROOF_CONST_IN_SIGNATURE: {k} count={obsCnt} (e.g. {sampleStr})"
    | some expCnt =>
      if obsCnt > expCnt then
        let sampleStr := String.intercalate ", " samples.toList
        errs := errs.push s!"PROOF_CONST_IN_SIGNATURE_GREW: {k} count={obsCnt} exceeds allowlisted {expCnt} (e.g. {sampleStr})"
      else if obsCnt < expCnt then
        errs := errs.push s!"STALE_SIG_PROOF_ALLOWLIST: {k} observed count={obsCnt} < allowlisted {expCnt}; shrink sigProofConstAllowlist"
  for (k, expCnt) in allowSigs do
    if !rep.sigProofCounts.contains k then
      errs := errs.push s!"STALE_SIG_PROOF_ALLOWLIST: {k} (expected count={expCnt}) no longer occurs; remove it from sigProofConstAllowlist"
  return errs

private def evaluateDagRatchet (rep : DagAuditReport) : Array String :=
  evaluateDagRatchetWith importDagAllowlist sigProofConstAllowlist rep

/-- Audit compiled `.olean` artifacts reachable from `LeanSwe` for promise coverage. -/
unsafe def main (args : List String) : IO UInt32 := do
  let isWorker := args.head? == some "--internal-postfork-worker"
  let args' := if isWorker then args.drop 1 else args
  if args'.length > 2 then
    IO.eprintln s!"USAGE_ERROR: expected at most 2 arguments ([libDir] [repoDir]), got {args'.length}"
    return 1
  let mut libDir : System.FilePath := ".lake/build/lib/lean"
  let mut repoDir : System.FilePath := "."
  match args' with
  | [] => pure ()
  | [arg1] =>
    let p1 : System.FilePath := arg1
    if !(← (p1 / "LeanSwe.olean").pathExists) &&
        (← (p1 / ".lake" / "build" / "lib" / "lean" / "LeanSwe.olean").pathExists) then
      repoDir := p1
      libDir := p1 / ".lake" / "build" / "lib" / "lean"
    else
      libDir := p1
      let absLib? ← try some <$> IO.FS.realPath libDir catch _ => pure none
      let some absLib := absLib?
        | do
            IO.eprintln s!"MISSING_OLEAN: LeanSwe ({libDir / "LeanSwe.olean"})"
            return 1
      let comps := absLib.components
      if comps.length >= 5 && comps.drop (comps.length - 4) == [".lake", "build", "lib", "lean"] then
        repoDir := System.mkFilePath (comps.take (comps.length - 4))
      else
        IO.eprintln s!"MISSING_SOURCE_DIR: libDir {libDir} must reside at <repoDir>/.lake/build/lib/lean"
        return 1
  | [arg1, arg2] =>
    libDir := arg1
    repoDir := arg2
    let absLib? ← try some <$> IO.FS.realPath libDir catch _ => pure none
    let absExp? ← try some <$> IO.FS.realPath (repoDir / ".lake" / "build" / "lib" / "lean") catch _ => pure none
    match absLib?, absExp? with
    | some absLib, some absExp =>
      if absLib != absExp then
        IO.eprintln s!"SPLIT_BRAIN_REPO_DIR: libDir {libDir} ({absLib}) does not match {repoDir}/.lake/build/lib/lean ({absExp})"
        return 1
    | _, _ =>
      IO.eprintln s!"SPLIT_BRAIN_REPO_DIR: could not resolve {libDir} against {repoDir}/.lake/build/lib/lean"
      return 1
  | _ => unreachable!
  unless ← (libDir / "LeanSwe.olean").pathExists do
    IO.eprintln s!"MISSING_OLEAN: LeanSwe ({libDir / "LeanSwe.olean"})"
    return 1
  unless ← (libDir / "LeanSwe" / "PostFork" / "Verified.olean").pathExists do
    IO.eprintln s!"MISSING_OLEAN: LeanSwe.PostFork.Verified ({libDir / "LeanSwe" / "PostFork" / "Verified.olean"})"
    return 1
  unless ← (libDir / "LeanSwe" / "ProcessSandbox" / "Init" / "Verified.olean").pathExists do
    IO.eprintln s!"MISSING_OLEAN: LeanSwe.ProcessSandbox.Init.Verified ({libDir / "LeanSwe" / "ProcessSandbox" / "Init" / "Verified.olean"})"
    return 1
  let leanSweDir := repoDir / "LeanSwe"
  let coreDir := repoDir / "Core"
  unless (← leanSweDir.isDir) && (← coreDir.isDir) do
    IO.eprintln s!"MISSING_SOURCE_DIR: {leanSweDir} or {coreDir}"
    return 1
  initSearchPath (← findSysroot) [libDir]
  let shouldForbidModuleInit (m : Name) : Bool :=
    m == `LeanSwe || isMutantModule m || nameLastStr m == "RuntimeTests" ||
      nameLastStr m == "SpecTests" || (nameLastStr m).endsWith "Proofs" ||
      m.components.contains `Proofs || m.getRoot == `Core ||
      m.components.take 2 == [`LeanSwe, `Compress] ||
      m.components.take 2 == [`LeanSwe, `EnvVars] ||
      m.components.take 2 == [`LeanSwe, `CryptoHash] ||
      m.components.take 2 == [`LeanSwe, `LinuxSyscall] ||
      m.components.take 2 == [`LeanSwe, `PostFork] ||
      m.components.take 3 == [`LeanSwe, `ProcessSandbox, `Init] ||
      m.components.take 2 == [`LeanSwe, `Sqlite] ||
      m.components.take 2 == [`LeanSwe, `Git] ||
      m.components.take 2 == [`LeanSwe, `ConnectProxy]

  let auditEnvPhase (auditE : Environment) (onlyPf : Bool) :
      IO (Array String × Nat × Array Name × Std.HashSet Name × Array (Name × Name) × Std.HashMap Name (Array Name) × Std.HashMap Name (Array Name) × Nat) := do
    let mut pErrs : Array String := #[]
    let mut companionPromisesByMutMod : Std.HashMap Name (Std.HashSet Name) := {}
    for h : i in [0 : auditE.header.moduleNames.size] do
      let m := auditE.header.moduleNames[i]
      if (onlyPf && !isPostForkVerifiedMod m) || (!onlyPf && isPostForkVerifiedMod m) then continue
      if isProjectModule m && m.getString! == "SpecTests" then
        let some data := auditE.header.moduleData[i]? | continue
        let mut s : Std.HashSet Name := {}
        for c in data.constants do
          if isPrivateOrInternal c.name then continue
          let short := c.name.getString!
          let trackEmpirical := short.startsWith "empirical_" && !legacyEmpiricalModules.contains m
          if short.startsWith "test_" || trackEmpirical then
            s := s.insert c.name
        companionPromisesByMutMod := companionPromisesByMutMod.insert (m.getPrefix.str "SpecMutants") s
    let mut specModCount := 0
    let mut specMods : Array Name := #[]
    let mut mutantModsWithAllPass : Std.HashSet Name := {}
    let mut sigAuditTasks : Array (Name × Task (Except IO.Error (Except String Nat))) := #[]
    let mut promises : Array (Name × Name) := #[]
    let mut promiseSet : Std.HashSet Name := {}
    for h : i in [0 : auditE.header.moduleNames.size] do
      let m := auditE.header.moduleNames[i]
      if !isProjectModule m || (onlyPf && !isPostForkVerifiedMod m) || (!onlyPf && isPostForkVerifiedMod m) then continue
      let some data := auditE.header.moduleData[i]? | continue
      for imp in data.imports do
        if !isAllowedProjectDirectImport m imp.module then
          pErrs := pErrs.push s!"FORBIDDEN_IMPORT: {m} imports {imp.module}"
      for c in data.constants do
        if let .axiomInfo _ := c then
          if !allowedAxioms.contains c.name then
            pErrs := pErrs.push s!"CUSTOM_AXIOM_FORBIDDEN: {c.name} in {m}"
        if (Lean.getExportNameFor? auditE c.name).isSome then
          pErrs := pErrs.push s!"FORBIDDEN_EXPORT: {c.name} in {m}"
        if let some initFn := Lean.regularInitAttr.getParam? auditE c.name then
          if isMutantModule m then
            pErrs := pErrs.push s!"FORBIDDEN_INIT_IN_MUTANT: {c.name} in {m}"
          else if shouldForbidModuleInit m && !isAllowedCoreInitFn auditE m c.name initFn &&
              !isAllowedSqliteInitFn auditE m c.name initFn then
            pErrs := pErrs.push s!"FORBIDDEN_INIT: {c.name} in {m}"
        if (Lean.builtinInitAttr.getParam? auditE c.name).isSome then
          if isMutantModule m then
            pErrs := pErrs.push s!"FORBIDDEN_INIT_IN_MUTANT: {c.name} in {m}"
          else
            pErrs := pErrs.push s!"FORBIDDEN_BUILTIN_INIT: {c.name} in {m}"
      for scEntry in Lean.Compiler.CSimp.ext.ext.getModuleEntries auditE i do
        let entry := match scEntry with | .global e => e | .scoped _ e => e
        let origMod := auditE.getModuleIdxFor? entry.fromDeclName |>.bind (auditE.header.moduleNames[·]?) |>.getD .anonymous
        let thmMod := auditE.getModuleIdxFor? entry.thmName |>.bind (auditE.header.moduleNames[·]?) |>.getD .anonymous
        let toMod := auditE.getModuleIdxFor? entry.toDeclName |>.bind (auditE.header.moduleNames[·]?) |>.getD .anonymous
        if isProjectModule m || isProjectModule origMod || isProjectModule thmMod || isProjectModule toMod then
          pErrs := pErrs.push s!"FORBIDDEN_CSIMP: {entry.fromDeclName} -> {entry.toDeclName} (thm={entry.thmName}, mod={m})"
      if m.getString! == "SpecTests" then
        specModCount := specModCount + 1
        specMods := specMods.push m
        let mut hasBadSpecConst := false
        for c in data.constants do
          let usedInType := c.type.getUsedConstants
          let usedInVal := (c.value?.map (·.getUsedConstants) |>.getD #[])
          let usesGateConst :=
            usedInType.contains `Core.AllPass || usedInType.contains `Core.CanReach ||
              usedInType.contains `Core.AllPassRun || usedInType.contains `Core.CanReachRun ||
              usedInVal.contains `Core.AllPass || usedInVal.contains `Core.CanReach ||
              usedInVal.contains `Core.AllPassRun || usedInVal.contains `Core.CanReachRun
          if usesGateConst then
            pErrs := pErrs.push s!"MUTANT_OR_THEOREM_IN_SPECTESTS: {c.name} in {m} references Core.AllPass or Core.CanReach"
            hasBadSpecConst := true
          else if c matches .thmInfo _ && !isCompilerAuxThm auditE c.name then
            pErrs := pErrs.push s!"MUTANT_OR_THEOREM_IN_SPECTESTS: {c.name} in {m} is a theorem or example"
            hasBadSpecConst := true
          if isPrivateOrInternal c.name then continue
          let short := c.name.getString!
          let trackEmpirical := short.startsWith "empirical_" && !legacyEmpiricalModules.contains m
          if short.startsWith "test_" || trackEmpirical then
            promises := promises.push (m, c.name)
            promiseSet := promiseSet.insert c.name
        match ← readIleanRefNames (moduleToIleanPath libDir m) with
        | .error err => pErrs := pErrs.push s!"MUTANT_OR_THEOREM_IN_SPECTESTS: {m} ({err})"
        | .ok refs =>
          for r in refs do
            if r == "Core.AllPass" || r == "Core.CanReach" || r == "Core.AllPassRun" || r == "Core.CanReachRun" then
              pErrs := pErrs.push s!"MUTANT_OR_THEOREM_IN_SPECTESTS: {m} .ilean references {r}"
              hasBadSpecConst := true
              break
        let specPath := moduleToFilePath repoDir m
        if !hasBadSpecConst then
          match ← parseModuleCommands auditE specPath with
          | .error err => pErrs := pErrs.push s!"MUTANT_OR_THEOREM_IN_SPECTESTS: {m} ({err})"
          | .ok cmds =>
            for stx in cmds do
              if hasSyntaxKind ``Lean.Parser.Command.example stx ||
                  hasSyntaxKind ``Lean.Parser.Command.theorem stx then
                pErrs := pErrs.push s!"MUTANT_OR_THEOREM_IN_SPECTESTS: {specPath} contains example or theorem"
                break
              if let some sig := findSyntaxKind? ``Lean.Parser.Term.typeSpec stx then
                if hasIdentOrAtom isAllPassToken sig then
                  pErrs := pErrs.push s!"MUTANT_OR_THEOREM_IN_SPECTESTS: {specPath} references AllPass"
                  break
              if let some metaErr := checkForbiddenMetaOrAttr specPath stx then
                pErrs := pErrs.push metaErr
                break
      else if isMutantModule m then
        let companionPromises := companionPromisesByMutMod.getD m {}
        let mut hasAllPassMutantThm := false
        for c in data.constants do
          if let .thmInfo v := c then
            if ← checkValidNegatedMutantIO auditE companionPromises v.type then
              hasAllPassMutantThm := true
              break
        if hasAllPassMutantThm then
          mutantModsWithAllPass := mutantModsWithAllPass.insert m
        match ← readIleanRefNames (moduleToIleanPath libDir m) with
        | .error err => pErrs := pErrs.push s!"UNALLOWED_AXIOM_IN_MUTANT: {m} ({err})"
        | .ok refs =>
          for r in refs do
            if forbiddenIleanMutantRefs.contains r then
              pErrs := pErrs.push s!"UNALLOWED_AXIOM_IN_MUTANT: {m} .ilean references {r}"
        let mutPath := moduleToFilePath repoDir m
        match ← parseModuleCommands auditE mutPath with
        | .error err => pErrs := pErrs.push s!"MISSING_SPECMUTANTS: {m} ({err})"
        | .ok cmds =>
          for stx in cmds do
            if hasSyntaxKind ``Lean.Parser.Command.axiom stx then
              pErrs := pErrs.push s!"CUSTOM_AXIOM_FORBIDDEN: axiom declaration in {mutPath}"
            if hasSyntaxKind ``Lean.Parser.Command.variable stx ||
                hasSyntaxKind ``Lean.Parser.Command.include stx then
              pErrs := pErrs.push s!"FORBIDDEN_VARIABLE_IN_MUTANT: {mutPath} uses variable/include"
            if hasIdentOrAtom isForbiddenMutantToken stx then
              pErrs := pErrs.push s!"UNALLOWED_AXIOM_IN_MUTANT: {mutPath} uses forbidden sorry/admit/native_decide/unsafe"
            if let some metaErr := checkForbiddenMetaOrAttr mutPath stx then
              pErrs := pErrs.push metaErr
        if !hasAllPassMutantThm then
          let t ← IO.asTask (countElaboratedNegatedAllPass auditE companionPromises m mutPath)
          sigAuditTasks := sigAuditTasks.push (m, t)
    for (m, t) in sigAuditTasks do
      match t.get with
      | .error e => pErrs := pErrs.push s!"MISSING_SPECMUTANTS: {m} ({e})"
      | .ok (.error err) => pErrs := pErrs.push s!"MISSING_SPECMUTANTS: {m} ({err})"
      | .ok (.ok negCount) =>
        if negCount > 0 then
          mutantModsWithAllPass := mutantModsWithAllPass.insert m
    let ctx : Core.Context := { fileName := "<CheckPromises>", fileMap := default, maxHeartbeats := 0 }
    let state : Core.State := { env := auditE }
    let ((allPass, canReach, axErrs), _) ← (Meta.MetaM.run' do
      let mut allPass : Std.HashMap Name (Array Name) := {}
      let mut canReach : Std.HashMap Name (Array Name) := {}
      let mut axErrs : Array String := #[]
      let mut axCache : AxCache := {}
      for h : i in [0 : auditE.header.moduleNames.size] do
        let m := auditE.header.moduleNames[i]
        if !isProjectModule m || m.getString! == "SpecTests" || m.getString! == "RuntimeTests" ||
            m.components.contains `SpecTests || m.components.contains `RuntimeTests ||
            (onlyPf && !isPostForkVerifiedMod m) || (!onlyPf && isPostForkVerifiedMod m) then
          continue
        let some data := auditE.header.moduleData[i]? | continue
        if isMutantModule m || isInitVerifiedMod m then
          for c in data.constants do
            if c matches .thmInfo _ || c matches .defnInfo _ || c matches .opaqueInfo _ then
              let (badAx?, nextCache) ← (checkAxiomsOk c.name).run axCache
              axCache := nextCache
              if let some badAx := badAx? then
                let tag := if isMutantModule m then "UNALLOWED_AXIOM_IN_MUTANT" else "UNALLOWED_AXIOM_IN_THEOREM"
                axErrs := axErrs.push s!"{tag}: {c.name} in {m} uses [{badAx}]"
          continue
        for c in data.constants do
          let .thmInfo v := c | continue
          if isPrivateOrInternal c.name || auditE.isProjectionFn c.name then continue
          let used := v.type.getUsedConstants
          if !used.any (fun k => k == `Core.AllPass || k == `Core.CanReach) then continue
          let (nextAllPass, nextCanReach, nextAxErrs, nextCache) ←
            withUnconditionalAtoms v.type fun atoms? => do
              let mut lAllPass := allPass
              let mut lCanReach := canReach
              let mut lAxErrs := axErrs
              let mut lCache := axCache
              let some atoms := atoms? | return (lAllPass, lCanReach, lAxErrs, lCache)
              let mut hasPromiseAtom := false
              for atom in atoms do
                if atom.isAppOfArity `Core.AllPass 1 || atom.isAppOfArity `Core.CanReach 1 then
                  if let .const fn _ := atom.appArg!.consumeMData.getAppFn.consumeMData then
                    if promiseSet.contains fn || fn.getString!.startsWith "test_" || fn.getString!.startsWith "empirical_" then
                      hasPromiseAtom := true
              if hasPromiseAtom then
                let (badAx?, nc) ← (checkAxiomsOk c.name).run lCache
                lCache := nc
                if let some badAx := badAx? then
                  lAxErrs := lAxErrs.push s!"UNALLOWED_AXIOM_IN_THEOREM: {c.name} uses [{badAx}]"
                  return (lAllPass, lCanReach, lAxErrs, lCache)
              for atom in atoms do
                if atom.isAppOfArity `Core.AllPass 1 then
                  let prog := atom.appArg!.consumeMData
                  if let .const fn _ := prog.getAppFn.consumeMData then
                    if promiseSet.contains fn then
                      if !(← hasCanonicalPromiseTarget fn prog) then
                        lAxErrs := lAxErrs.push s!"NON_CANONICAL_PROMISE_TARGET: {c.name} in {m} proves {fn} against non-canonical target"
                      else if ← hasCanonicalNondetInst `Core.instNondetTestAllPassRun prog then
                        match isCanonicalConnectProxyPromiseApp fn prog with
                        | .ok () =>
                          lAllPass := lAllPass.insert fn ((lAllPass.getD fn #[]).push c.name)
                        | .error tgtErr =>
                          lAxErrs := lAxErrs.push s!"{tgtErr} (in {c.name})"
                      else
                        lAxErrs := lAxErrs.push s!"NON_CANONICAL_NONDET_INST: {c.name} in {m} uses non-canonical NondetTest AllPassRun instance for {fn}"
                else if atom.isAppOfArity `Core.CanReach 1 then
                  let prog := atom.appArg!.consumeMData
                  if let .const fn _ := prog.getAppFn.consumeMData then
                    if promiseSet.contains fn then
                      if !(← hasCanonicalPromiseTarget fn prog) then
                        lAxErrs := lAxErrs.push s!"NON_CANONICAL_PROMISE_TARGET: {c.name} in {m} proves {fn} against non-canonical target"
                      else if ← hasCanonicalNondetInst `Core.instNondetTestCanReachRun prog then
                        match isCanonicalConnectProxyPromiseApp fn prog with
                        | .ok () =>
                          lCanReach := lCanReach.insert fn ((lCanReach.getD fn #[]).push c.name)
                        | .error tgtErr =>
                          lAxErrs := lAxErrs.push s!"{tgtErr} (in {c.name})"
                      else
                        lAxErrs := lAxErrs.push s!"NON_CANONICAL_NONDET_INST: {c.name} in {m} uses non-canonical NondetTest CanReachRun instance for {fn}"
              return (lAllPass, lCanReach, lAxErrs, lCache)
          allPass := nextAllPass
          canReach := nextCanReach
          axErrs := nextAxErrs
          axCache := nextCache
      return (allPass, canReach, axErrs)
    ).toIO ctx state
    let mut assumesCount := 0
    for (m, pName) in promises do
      let usesAssume := usesAssumeTransitive auditE pName
      if usesAssume then assumesCount := assumesCount + 1
      if (allPass.getD pName #[]).isEmpty then
        pErrs := pErrs.push s!"MISSING_ALLPASS: {pName} (defined in {m})"
      if usesAssume && (canReach.getD pName #[]).isEmpty then
        pErrs := pErrs.push s!"MISSING_CANREACH: {pName} (defined in {m}, uses assume)"
    return (pErrs ++ axErrs, specModCount, specMods, mutantModsWithAllPass, promises, allPass, canReach, assumesCount)

  if isWorker then
    enableInitializersExecution
    let pfEnv ← importModules #[{ module := `LeanSwe.PostFork.Verified }, { module := `LeanSwe.ProcessSandbox.Init.Verified }] {} (loadExts := true)
    for modName in pfEnv.header.moduleNames do
      if isPostForkVerifiedMod modName then
        IO.println s!"PFW_MOD:{modName}"
    let (eErrs2, sCnt2, sMods2, mutOk2, prom2, ap2, cr2, wAss2) ← auditEnvPhase pfEnv true
    let pfAeneasErrs := checkPostForkAeneasWiring pfEnv
    let pfDagRep := auditImportDagEnv pfEnv isPostForkVerifiedMod ap2 cr2
    for m in sMods2 do
      IO.println s!"PFW_SPEC:{m}"
    for m in mutOk2 do
      IO.println s!"PFW_MUT:{m}"
    for err in eErrs2 ++ pfAeneasErrs do
      IO.println s!"PFW_ERR:{err}"
    for ln in encodeDagReportWireLines pfDagRep do
      IO.println ln
    IO.println s!"PFW_STATS:{sCnt2}:{prom2.size}:{wAss2}"
    return 0

  let leanExe := (← findSysroot) / "bin" / "lean"
  let workerOut ← IO.Process.output {
    cmd := leanExe.toString
    args := #["--run", (repoDir / "scripts" / "CheckPromises.lean").toString, "--internal-postfork-worker", libDir.toString, repoDir.toString]
  }
  if workerOut.exitCode != 0 then
    IO.eprintln s!"POSTFORK_VERIFIED_WORKER_FAILED: exit={workerOut.exitCode} stderr={workerOut.stderr.trimAscii.toString}"
    return 1
  let workerLines := (workerOut.stdout.splitOn "\n").toArray
  let mut pfModNames : Std.HashSet String := {}
  let mut eErrs2 : Array String := #[]
  let mut sMods2 : Array String := #[]
  let mut mutOk2 : Std.HashSet String := {}
  let mut sCnt2 : Nat := 0
  let mut prom2Count : Nat := 0
  let mut wAss2 : Nat := 0
  let pfDagRep := decodeDagReportWireLines workerLines
  for ln in workerLines do
    if ln.startsWith "PFW_MOD:" then pfModNames := pfModNames.insert (ln.drop 8).toString
    else if ln.startsWith "PFW_SPEC:" then sMods2 := sMods2.push (ln.drop 9).toString
    else if ln.startsWith "PFW_MUT:" then mutOk2 := mutOk2.insert (ln.drop 8).toString
    else if ln.startsWith "PFW_ERR:" then eErrs2 := eErrs2.push (ln.drop 8).toString
    else if ln.startsWith "PFW_STATS:" then
      match (ln.drop 10).toString.splitOn ":" with
      | [a, b, c] =>
        sCnt2 := a.toNat!
        prom2Count := b.toNat!
        wAss2 := c.toNat!
      | _ => pure ()

  enableInitializersExecution
  let env ← importModules #[{ module := `LeanSwe }] {} (loadExts := true)
  let mut visited : Std.HashSet Name := {}
  let mut pubClosureCount := 0
  let mut pubClosureErrs := 0
  let mut errors : Array String := #[]
  for modName in env.header.moduleNames do
    let ms := modName.toString
    if ms == "Aeneas" || ms.startsWith "Aeneas." || ms == "Mathlib" || ms.startsWith "Mathlib." || isPostForkVerifiedMod modName then
      errors := errors.push s!"POSTFORK_PUBLIC_CLOSURE_VIOLATION: LeanSwe transitively imports {modName}"
      pubClosureErrs := pubClosureErrs + 1
    if isProjectModule modName then
      visited := visited.insert modName
      pubClosureCount := pubClosureCount + 1
  IO.println s!"POSTFORK_PUBLIC_CLOSURE: modules={pubClosureCount} errors={pubClosureErrs}"

  let mut extraProjectMods : Array Name := #[]
  let mut runtimeTestMods : Array Name := #[]
  let pushDiscovered (m : Name) (arr : Array Name) : Array Name :=
    if arr.contains m then arr else arr.push m
  for entry in (← System.FilePath.walkDir leanSweDir) do
    if !(← entry.isDir) && entry.extension == some "lean" then
      let modName := moduleNameUnderLeanSwe leanSweDir entry
      extraProjectMods := pushDiscovered modName extraProjectMods
      if nameLastStr modName == "RuntimeTests" then
        runtimeTestMods := pushDiscovered modName runtimeTestMods
      if !visited.contains modName && !pfModNames.contains modName.toString then
        if entry.fileName == some "SpecTests.lean" then
          errors := errors.push s!"UNIMPORTED_SPECTESTS: {entry} (module {modName} is not imported by LeanSwe)"
        else if isMutantModule modName then
          errors := errors.push s!"UNIMPORTED_SPECMUTANTS: {entry} (module {modName} is not imported by LeanSwe)"
        else
          errors := errors.push s!"UNIMPORTED_LEANSWE_MODULE: {entry} (module {modName} is not imported by LeanSwe)"
  for entry in (← System.FilePath.walkDir coreDir) do
    if !(← entry.isDir) && entry.extension == some "lean" then
      let modName := moduleNameUnderRoot coreDir entry `Core
      extraProjectMods := pushDiscovered modName extraProjectMods
      if !visited.contains modName then
        errors := errors.push s!"UNIMPORTED_CORE_MODULE: {entry} (module {modName} is not imported by LeanSwe)"

  let mut importableExtraMods : Array Name := #[]
  for m in extraProjectMods do
    if !visited.contains m && !pfModNames.contains m.toString then
      let oleanPath := moduleToOleanPath libDir m
      if ← oleanPath.pathExists then
        importableExtraMods := importableExtraMods.push m
      else
        errors := errors.push s!"MISSING_OLEAN_FOR_SOURCE: {m} ({oleanPath})"

  let rootLeanSwePath := repoDir / "LeanSwe.lean"
  match ← parseModuleCommands env rootLeanSwePath with
  | .error err => errors := errors.push s!"ROOT_PARSE_ERROR: LeanSwe ({err})"
  | .ok cmds =>
    for stx in cmds do
      if hasSyntaxKind ``Lean.Parser.Command.initialize stx then
        errors := errors.push s!"FORBIDDEN_INIT_SYNTAX: {rootLeanSwePath} uses initialize"
        break
      if let some metaErr := checkForbiddenMetaOrAttr rootLeanSwePath stx then
        errors := errors.push metaErr
        break

  let (rtParseEnv, extraDagRep) ← if !importableExtraMods.isEmpty then do
    enableInitializersExecution
    let extraEnv ← importModules (importableExtraMods.map fun m => { module := m }) {} (loadExts := true)
    for h : i in [0 : extraEnv.header.moduleNames.size] do
      let m := extraEnv.header.moduleNames[i]
      if !isProjectModule m || visited.contains m then continue
      let some data := extraEnv.header.moduleData[i]? | continue
      for imp in data.imports do
        if !isAllowedProjectDirectImport m imp.module then
          errors := errors.push s!"FORBIDDEN_IMPORT: {m} imports {imp.module}"
      for c in data.constants do
        if let .axiomInfo _ := c then
          if !allowedAxioms.contains c.name then
            errors := errors.push s!"CUSTOM_AXIOM_FORBIDDEN: {c.name} in {m}"
        if (Lean.getExportNameFor? extraEnv c.name).isSome then
          errors := errors.push s!"FORBIDDEN_EXPORT: {c.name} in {m}"
        if let some initFn := Lean.regularInitAttr.getParam? extraEnv c.name then
          if !isAllowedCoreInitFn extraEnv m c.name initFn &&
              !isAllowedSqliteInitFn extraEnv m c.name initFn then
            errors := errors.push s!"FORBIDDEN_INIT: {c.name} in {m}"
        if (Lean.builtinInitAttr.getParam? extraEnv c.name).isSome then
          errors := errors.push s!"FORBIDDEN_BUILTIN_INIT: {c.name} in {m}"
      for scEntry in Lean.Compiler.CSimp.ext.ext.getModuleEntries extraEnv i do
        let entry := match scEntry with | .global e => e | .scoped _ e => e
        errors := errors.push s!"FORBIDDEN_CSIMP: {entry.fromDeclName} -> {entry.toDeclName} in {m}"
    for extraMod in importableExtraMods do
      let extraPath := moduleToFilePath repoDir extraMod
      match ← parseModuleCommands extraEnv extraPath with
      | .error err => errors := errors.push s!"EXTRA_MOD_PARSE_ERROR: {extraMod} ({err})"
      | .ok cmds =>
        for stx in cmds do
          if hasSyntaxKind ``Lean.Parser.Command.initialize stx then
            errors := errors.push s!"FORBIDDEN_INIT_SYNTAX: {extraPath} uses initialize"
            break
          if let some metaErr := checkForbiddenMetaOrAttr extraPath stx then
            errors := errors.push metaErr
            break
    let exDag := auditImportDagEnv extraEnv
      (fun m => !visited.contains m && !isPostForkVerifiedMod m) {} {} true
    pure (extraEnv, exDag)
  else
    pure (env, {})

  for rtMod in runtimeTestMods do
    if rtMod == `LeanSwe.PostFork.RuntimeTests then
      if let some idx := rtParseEnv.header.moduleNames.findIdx? (· == rtMod) then
        if let some data := rtParseEnv.header.moduleData[idx]? then
          errors := errors ++ checkPostForkRuntimeTestsExterns rtParseEnv data.constants
    let rtPath := moduleToFilePath repoDir rtMod
    match ← parseModuleCommands rtParseEnv rtPath with
    | .error err => errors := errors.push s!"RUNTIMETESTS_PARSE_ERROR: {rtMod} ({err})"
    | .ok cmds =>
      for stx in cmds do
        if hasAttrNameInStx #["export"] stx then
          errors := errors.push s!"FORBIDDEN_EXPORT_IN_RUNTIMETESTS: {rtPath} uses @[export]"
          break
        if hasAttrNameInStx #["implemented_by", "csimp"] stx then
          errors := errors.push s!"FORBIDDEN_ATTR_IN_RUNTIMETESTS: {rtPath} uses @[implemented_by] or @[csimp]"
          break
        if hasSyntaxKind ``Lean.Parser.Command.initialize stx then
          errors := errors.push s!"FORBIDDEN_INIT_IN_RUNTIMETESTS: {rtPath} uses initialize"
          break
        if closureForbiddenMetaSyntaxKinds.any (hasSyntaxKind · stx) then
          errors := errors.push s!"FORBIDDEN_SYNTAX_IN_RUNTIMETESTS: {rtPath} uses forbidden meta/eval command"
          break

  let mut auxFiles : Array (String × System.FilePath) := #[]
  let testsDir := repoDir / "harness" / "Tests"
  if ← testsDir.pathExists then
    auxFiles := auxFiles ++ (← collectLeanRelFiles testsDir "harness/Tests")
  let fuzzDir := repoDir / "harness" / "Fuzz"
  if ← fuzzDir.pathExists then
    auxFiles := auxFiles ++ (← collectLeanRelFiles fuzzDir "harness/Fuzz")
  for (relPath, filePath) in auxFiles do
    match ← parseModuleCommands rtParseEnv filePath (allowMacroRecovery := true) with
    | .error _ => pure ()
    | .ok cmds =>
      if cmds.any (hasAttrNameInStx #["export"]) then
        errors := errors.push s!"FORBIDDEN_EXPORT_ATTR: {relPath} uses @[export]"
  if !importableExtraMods.isEmpty then
    rtParseEnv.freeRegions

  let (eErrs1, sCnt1, sMods1, mutOk1, prom1, ap1, cr1, wAss1) ← auditEnvPhase env false
  let pwWiringErrs ← checkPasswdPrivateWiring env
  let dnsWiringErrs ← checkDnsInterfaceWiring env
  let pfWiringErrs ← checkPostForkPrivateWiring env
  let trAuditMods := discoverPackageModules env importableExtraMods `LeanSwe.LinuxSyscall.TimeRand timeRandAuditModules
  let filesAuditMods := discoverPackageModules env importableExtraMods `LeanSwe.LinuxSyscall.Files filesAuditModules
  let pwAuditMods := discoverPackageModules env importableExtraMods `LeanSwe.LinuxSyscall.Passwd passwdAuditModules
  let dnsAuditMods := discoverPackageModules env importableExtraMods `LeanSwe.LinuxSyscall.Dns dnsAuditModules
  let pollAuditMods := discoverPackageModules env importableExtraMods `LeanSwe.LinuxSyscall.Poll pollAuditModules
  let netAuditMods := discoverPackageModules env importableExtraMods `LeanSwe.LinuxSyscall.Net netAuditModules
  let procAuditMods := discoverPackageModules env importableExtraMods `LeanSwe.LinuxSyscall.Process processAuditModules
  let envAuditMods := discoverPackageModules env importableExtraMods `LeanSwe.EnvVars envVarsAuditModules
  let chAuditMods := discoverPackageModules env importableExtraMods `LeanSwe.CryptoHash cryptoHashAuditModules

  let trClosureErrs ← checkPackageTrustedClosure repoDir "TimeRand" trAuditMods
    isAllowedTimeRandClosureModule `LeanSwe.LinuxSyscall.TimeRand.Interface allowedTimeRandExternSyms true
  let filesClosureErrs ← checkPackageTrustedClosure repoDir "Files" filesAuditMods
    isAllowedFilesClosureModule `LeanSwe.LinuxSyscall.Files.Interface allowedFilesExternSyms true true
  IO.println s!"TRUSTED_CLOSURE: files_modules={filesAuditMods.size} allowlist=Common+Files externs={allowedFilesExternSyms.size}"
  let pwClosureErrs ← checkPackageTrustedClosure repoDir "Passwd" pwAuditMods
    isAllowedPasswdClosureModule `LeanSwe.LinuxSyscall.Passwd.Interface allowedPasswdExternSyms true
  let dnsClosureErrs ← checkPackageTrustedClosure repoDir "Dns" dnsAuditMods
    isAllowedDnsClosureModule `LeanSwe.LinuxSyscall.Dns.Interface allowedDnsExternSyms true
  IO.println s!"TRUSTED_CLOSURE: dns_modules={dnsAuditMods.size} allowlist=Core+Common+Dns externs={allowedDnsExternSyms.size}"
  let pollClosureErrs ← checkPackageTrustedClosure repoDir "Poll" pollAuditMods
    isAllowedPollClosureModule `LeanSwe.LinuxSyscall.Poll.Interface allowedPollExternSyms true true
  IO.println s!"TRUSTED_CLOSURE: poll_modules={pollAuditMods.size} allowlist=Core+Common+Poll externs={allowedPollExternSyms.size}"
  let netClosureErrs ← checkPackageTrustedClosure repoDir "Net" netAuditMods
    isAllowedNetClosureModule `LeanSwe.LinuxSyscall.Net.Interface allowedNetExternSyms true true
  IO.println s!"TRUSTED_CLOSURE: net_modules={netAuditMods.size} allowlist=Core+Common+Net externs={allowedNetExternSyms.size}"
  let procClosureErrs ← checkPackageTrustedClosure repoDir "Process" procAuditMods
    isAllowedProcessClosureModule `LeanSwe.LinuxSyscall.Process.Interface allowedProcessExternSyms true true
  IO.println s!"TRUSTED_CLOSURE: process_modules={procAuditMods.size} allowlist=Core+Common+Process externs={allowedProcessExternSyms.size}"
  let envClosureErrs ← checkPackageTrustedClosure repoDir "EnvVars" envAuditMods
    isAllowedEnvVarsClosureModule `LeanSwe.EnvVars.Raw.Interface allowedEnvVarsExternSyms false
  let chClosureErrs ← checkPackageTrustedClosure repoDir "CryptoHash" chAuditMods
    isAllowedCryptoHashClosureModule `LeanSwe.CryptoHash.Raw.Interface allowedCryptoHashExternSyms false
  let sqAuditMods := discoverPackageModules env importableExtraMods `LeanSwe.Sqlite sqliteAuditModules
  let sqClosureErrs ← checkPackageTrustedClosure repoDir "Sqlite" sqAuditMods
    isAllowedSqliteClosureModule `LeanSwe.Sqlite.Raw.Interface allowedSqliteExternSyms false false false true
  IO.println s!"TRUSTED_CLOSURE: sqlite_modules={sqAuditMods.size} allowlist=Sqlite+Sqlite.Raw"
  let sbxClosureErrs ← checkSandboxTrustedClosure env
  let compClosureErrs ← checkCompressTrustedClosure repoDir env importableExtraMods
  let managedProcErrs ← checkManagedProcessClosure env
  let psandboxHostErrs ← checkProcessSandboxHostClosure env
  let pfClosureErrs ← checkPackageTrustedClosure repoDir "PostFork" postForkAuditModules
    isAllowedPostForkClosureModule `LeanSwe.PostFork.Interface allowedPostForkExternSyms true true true
  let gitClosureErrs ← checkGitTrustedClosure env importableExtraMods
  let cproxyClosureErrs ← checkConnectProxyTrustedClosure env repoDir ap1 cr1

  let mainDagRep := auditImportDagEnv env (fun m => !isPostForkVerifiedMod m) ap1 cr1
  let combinedDagRep := mergeDagReports (mergeDagReports mainDagRep pfDagRep) extraDagRep
  let dagErrs := evaluateDagRatchet combinedDagRep
  let totalSigHits := combinedDagRep.sigProofCounts.fold (init := 0) fun acc _ (cnt, _) => acc + cnt
  IO.println s!"IMPORT_DAG_CHECK: modules={combinedDagRep.checkedModules} edges_obs={combinedDagRep.violations.size} edges_allow={importDagAllowlist.size} sig_keys_obs={combinedDagRep.sigProofCounts.size} sig_hits_obs={totalSigHits} sig_allow={sigProofConstAllowlist.size} errors={dagErrs.size}"

  let specModCount := sCnt1 + sCnt2
  let specModStrs := (sMods1.map (·.toString)) ++ sMods2
  let mutOkAll : Std.HashSet String := mutOk1.fold (fun acc m => acc.insert m.toString) mutOk2
  for ms in specModStrs do
    let mutMod := (ms.toName.getPrefix.str "SpecMutants").toString
    if !mutOkAll.contains mutMod then
      errors := errors.push s!"MISSING_SPECMUTANTS: {ms} lacks companion {mutMod} with at least 1 negated Core.AllPass mutant"

  let promCount := prom1.size + prom2Count
  let withAssumeCount := wAss1 + wAss2
  errors := errors ++ eErrs1 ++ eErrs2 ++ trClosureErrs ++ filesClosureErrs ++ pwClosureErrs ++ pwWiringErrs ++ dnsClosureErrs ++ dnsWiringErrs ++ pollClosureErrs ++ netClosureErrs ++ procClosureErrs ++ envClosureErrs ++ chClosureErrs ++ sqClosureErrs ++ sbxClosureErrs ++ compClosureErrs ++ managedProcErrs ++ psandboxHostErrs ++ pfClosureErrs ++ pfWiringErrs ++ gitClosureErrs ++ cproxyClosureErrs ++ dagErrs
  IO.println s!"PROMISE_CHECK: spec_modules={specModCount} promises={promCount} with_assume={withAssumeCount} errors={errors.size}"
  if errors.isEmpty then
    return 0
  else
    for err in errors do
      IO.eprintln err
    return 1
