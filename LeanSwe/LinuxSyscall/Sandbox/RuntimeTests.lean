import Core.Assumptions
import LeanSwe.LinuxSyscall.Sandbox.Interface
import LeanSwe.LinuxSyscall.Fuzz.SandboxEnv

namespace LeanSwe.LinuxSyscall.Sandbox.RuntimeTests

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Sandbox
open LeanSwe.LinuxSyscall.Fuzz

private local instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e1, .error e2 => e1 == e2
    | _, _ => false

private local instance : Repr RawFd where
  reprPrec _ _ := "<RawFd>"

private def assertTrue (ok : Bool) (msg : String) : IO Unit := do
  if !ok then
    throw (IO.userError msg)

private def assertErr {α : Type} (r : Except Errno α) (expected : Errno) (label : String) : IO Unit := do
  match r with
  | .error e =>
    if e != expected then
      throw (IO.userError s!"{label}: expected errno {expected}, got {e}")
  | .ok _ =>
    throw (IO.userError s!"{label}: expected error {expected}, got ok")

private def encodeFilter (insns : List SockFilterInsn) : ByteArray :=
  Id.run do
    let mut bytes := ByteArray.empty
    for insn in insns do
      bytes := bytes.push (UInt8.ofNat (insn.code.toNat % 256))
      bytes := bytes.push (UInt8.ofNat ((insn.code.toNat / 256) % 256))
      bytes := bytes.push insn.jt
      bytes := bytes.push insn.jf
      bytes := bytes.push (UInt8.ofNat (insn.k.toNat % 256))
      bytes := bytes.push (UInt8.ofNat ((insn.k.toNat / 256) % 256))
      bytes := bytes.push (UInt8.ofNat ((insn.k.toNat / 65536) % 256))
      bytes := bytes.push (UInt8.ofNat ((insn.k.toNat / 16777216) % 256))
    return bytes

private def allowAllFilter : ByteArray :=
  encodeFilter [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]

private def repBytes (n : Nat) (b : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate n b)

private def waitExitedZero (st : UInt32) : Bool :=
  (st &&& 0x7F) == 0 && ((st >>> 8) &&& 0xFF) == 0

private def runForkedOk (label : String) (action : IO Unit) : IO Unit := do
  let (st, _) ← SandboxEnv.runForked do
    action
    return ByteArray.empty
  assertTrue (waitExitedZero st) s!"{label}: child wait status {st} != exited 0"

private def mkMockOps (err : Errno) : SandboxOps :=
  Internal.mkSandboxOps
    { landlockQuery := fun _ => pure (.error err)
    , landlockCreate := fun _ _ => pure (.error err)
    , landlockAddPathBeneath := fun _ _ _ => pure (.error err)
    , landlockAddNetPort := fun _ _ _ => pure (.error err)
    , landlockRestrictSelf := fun _ => pure (.error err)
    , seccompGetActionAvail := fun _ => pure (.error err)
    , seccompSetFilter := fun _ _ => pure (.error err)
    , prctl := fun _ _ => pure (.error err)
    , setrlimit := fun _ _ _ => pure (.error err)
    , memfdCreate := fun _ _ => pure (.error err) }

private def withTempHostPaths {α : Type} (f : String → String → IO α) : IO α := do
  let pid ← SandboxEnv.getTid
  let dir := s!"/tmp/leanswe-sbx-rt-{pid}"
  let file := s!"{dir}/probe.txt"
  IO.FS.createDirAll dir
  IO.FS.writeFile file "ok"
  try
    f dir file
  finally
    try IO.FS.removeFile file catch _ => pure ()
    try IO.FS.removeDir dir catch _ => pure ()

private def openHostOrThrow (path : String) (modeSel : UInt32) (label : String) : IO RawFd := do
  match ← SandboxEnv.openHostFd path.toUTF8 modeSel with
  | .ok fd => return fd
  | .error e => throw (IO.userError s!"{label}: openHostFd failed ({e})")

private def closeFdChecked (fd : RawFd) : IO Unit := do
  let _ ← SandboxEnv.closeFd fd

/-- Verify `landlock_create_ruleset` version/errata queries, `16`-byte ABI attr alignment, and error guards. -/
def assume_sandbox_landlockCreateRuleset_versionAndRuleset : IO Unit := do
  match ← landlockCreateRuleset none LANDLOCK_CREATE_RULESET_VERSION with
  | .ok (.version abi) =>
    assertTrue (abi ≥ 4) s!"expected Landlock ABI >= 4, got {abi}"
  | other =>
    throw (IO.userError s!"expected version, got {repr other}")
  match ← landlockCreateRuleset none LANDLOCK_CREATE_RULESET_ERRATA with
  | .ok (.version _) => pure ()
  | other => throw (IO.userError s!"expected errata version, got {repr other}")
  assertErr (← landlockCreateRuleset none 0) Errno.EINVAL "null attr with flags=0"
  assertErr (← landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 1)
    Errno.EINVAL "attr with nonzero flags"
  assertErr (← landlockCreateRuleset (some {}) 0) ENOMSG "empty ruleset attr"
  let netAttr : LandlockRulesetAttr := {
    handledAccessFs := LANDLOCK_ACCESS_FS_READ_FILE ||| LANDLOCK_ACCESS_FS_READ_DIR
    handledAccessNet := LANDLOCK_ACCESS_NET_CONNECT_TCP
  }
  match ← landlockCreateRuleset (some netAttr) 0 with
  | .ok (.ruleset rs) =>
    closeFdChecked rs
  | other =>
    throw (IO.userError s!"expected ruleset fd, got {repr other}")

/-- Verify `landlock_add_rule` `PATH_BENEATH` (normal & `O_PATH` dir/file, `EBADFD` on `memfd`/`pipe`) and `NET_PORT` bounds. -/
def assume_sandbox_landlockAddRule_pathBeneathAndNetPort : IO Unit := do
  withTempHostPaths fun dirPath filePath => do
    let attr : LandlockRulesetAttr := {
      handledAccessFs := LANDLOCK_ACCESS_FS_READ_FILE ||| LANDLOCK_ACCESS_FS_READ_DIR
      handledAccessNet := LANDLOCK_ACCESS_NET_CONNECT_TCP
    }
    let rs ← match ← landlockCreateRuleset (some attr) 0 with
      | .ok (.ruleset r) => pure r
      | other => throw (IO.userError s!"createRuleset failed: {repr other}")
    try
      let dirNormal ← openHostOrThrow dirPath 0 "dir normal"
      let dirOpath ← openHostOrThrow dirPath 1 "dir O_PATH"
      let fileOpath ← openHostOrThrow filePath 3 "file O_PATH"
      let mfd ← match ← memfdCreate "ll-nonrs".toUTF8 {} with
        | .ok f => pure f
        | .error e => throw (IO.userError s!"memfdCreate failed: {e}")
      let pipeFd ← match ← SandboxEnv.openPipeFd 0 with
        | .ok f => pure f
        | .error e => throw (IO.userError s!"openPipeFd failed: {e}")
      try
        assertTrue ((← landlockAddRule rs (.pathBeneath dirNormal LANDLOCK_ACCESS_FS_READ_DIR)) == .ok ())
          "add PATH_BENEATH dir normal failed"
        assertTrue ((← landlockAddRule rs (.pathBeneath dirOpath LANDLOCK_ACCESS_FS_READ_DIR)) == .ok ())
          "add PATH_BENEATH dir O_PATH failed"
        assertTrue ((← landlockAddRule rs (.pathBeneath fileOpath LANDLOCK_ACCESS_FS_READ_FILE)) == .ok ())
          "add PATH_BENEATH file O_PATH failed"
        assertErr (← landlockAddRule rs (.pathBeneath fileOpath LANDLOCK_ACCESS_FS_READ_DIR))
          Errno.EINVAL "dir access on regular file"
        assertErr (← landlockAddRule rs (.pathBeneath mfd LANDLOCK_ACCESS_FS_READ_FILE))
          EBADFD "memfd parentFd must fail EBADFD"
        assertErr (← landlockAddRule rs (.pathBeneath pipeFd LANDLOCK_ACCESS_FS_READ_FILE))
          EBADFD "pipe parentFd must fail EBADFD"
        assertErr (← landlockAddRule mfd (.pathBeneath dirOpath LANDLOCK_ACCESS_FS_READ_DIR))
          EBADFD "memfd ruleset must fail EBADFD"
        assertErr (← landlockAddRule pipeFd (.pathBeneath dirOpath LANDLOCK_ACCESS_FS_READ_DIR))
          EBADFD "pipe ruleset must fail EBADFD"
        assertTrue ((← landlockAddRule rs (.netPort 0 LANDLOCK_ACCESS_NET_CONNECT_TCP)) == .ok ())
          "NET_PORT 0 failed"
        assertTrue ((← landlockAddRule rs (.netPort 65535 LANDLOCK_ACCESS_NET_CONNECT_TCP)) == .ok ())
          "NET_PORT 65535 failed"
        assertErr (← landlockAddRule rs (.netPort 65536 LANDLOCK_ACCESS_NET_CONNECT_TCP))
          Errno.EINVAL "NET_PORT > 65535 must fail EINVAL"
        assertErr (← landlockAddRule rs (.netPort 80 LANDLOCK_ACCESS_NET_BIND_TCP))
          Errno.EINVAL "unhandled NET_PORT right must fail EINVAL"
      finally
        closeFdChecked dirNormal
        closeFdChecked dirOpath
        closeFdChecked fileOpath
        closeFdChecked mfd
        closeFdChecked pipeFd
    finally
      closeFdChecked rs

/-- Verify `landlock_restrict_self` `no_new_privs` vs `CLONE_NEWUSER` `CAP_SYS_ADMIN`, `EBADF`/`EBADFD`, and `16`-layer `E2BIG`. -/
def assume_sandbox_landlockRestrictSelf_nnpAndLayerCap : IO Unit := do
  runForkedOk "landlock_restrict_self nnp and 16-layer cap" do
    let rs ← match ← landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0 with
      | .ok (.ruleset r) => pure r
      | other => throw (IO.userError s!"createRuleset failed: {repr other}")
    let nnpBefore ← match ← prctl .getNoNewPrivs with
      | .ok v => pure v
      | .error e => throw (IO.userError s!"getNoNewPrivs failed: {e}")
    if nnpBefore == 0 then
      assertErr (← landlockRestrictSelf rs) Errno.EPERM "restrict_self before nnp"
    assertTrue ((← prctl .setNoNewPrivs) == .ok 0) "setNoNewPrivs failed"
    for idx in List.range LANDLOCK_MAX_STACKED_LAYERS do
      assertTrue ((← landlockRestrictSelf rs) == .ok ()) s!"layer {idx} failed"
    assertErr (← landlockRestrictSelf rs) Errno.E2BIG "17th Landlock layer must fail E2BIG"
    let mfd ← match ← memfdCreate "ll-mfd".toUTF8 {} with
      | .ok f => pure f
      | .error e => throw (IO.userError s!"memfdCreate failed: {e}")
    assertErr (← landlockRestrictSelf mfd) EBADFD "restrict_self on memfd must fail EBADFD"
    closeFdChecked mfd
    closeFdChecked rs
    assertErr (← landlockRestrictSelf rs) Errno.EBADF "restrict_self on closed rs must fail EBADF"
  runForkedOk "landlock_restrict_self in CLONE_NEWUSER with nnp=0" do
    match ← SandboxEnv.enterUserns with
    | .error e => throw (IO.userError s!"unshare CLONE_NEWUSER failed: {e}")
    | .ok () => pure ()
    let nnpUser ← match ← prctl .getNoNewPrivs with
      | .ok v => pure v
      | .error e => throw (IO.userError s!"getNoNewPrivs in userns failed: {e}")
    assertTrue (nnpUser == 0) s!"expected nnp==0 in fresh userns, got {nnpUser}"
    let rs ← match ← landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0 with
      | .ok (.ruleset r) => pure r
      | other => throw (IO.userError s!"createRuleset in userns failed: {repr other}")
    assertTrue ((← landlockRestrictSelf rs) == .ok ()) "restrict_self in userns with CAP_SYS_ADMIN failed"
    assertTrue ((← prctl .getNoNewPrivs) == .ok 0) "restrict_self must not toggle nnp"
    closeFdChecked rs

/-- Verify `seccomp` `GET_ACTION_AVAIL`, pure-Lean unsafe return rejection, safe DAG BPF filter install, and `TSYNC` / `TSYNC_ESRCH`. -/
def assume_sandbox_seccomp_actionAvailAndFilterAbi : IO Unit := do
  assertTrue ((← seccomp (.getActionAvail SECCOMP_RET_ALLOW) {} ByteArray.empty) == .ok 0) "RET_ALLOW avail"
  assertTrue ((← seccomp (.getActionAvail SECCOMP_RET_ERRNO) {} ByteArray.empty) == .ok 0) "RET_ERRNO avail"
  assertTrue ((← seccomp (.getActionAvail SECCOMP_RET_LOG) {} ByteArray.empty) == .ok 0) "RET_LOG avail"
  assertTrue ((← seccomp (.getActionAvail SECCOMP_RET_KILL_PROCESS) {} ByteArray.empty) == .ok 0) "KILL_PROCESS avail"
  assertErr (← seccomp (.getActionAvail 0x12340000) {} ByteArray.empty) Errno.EOPNOTSUPP "unknown seccomp action"
  assertErr (← seccomp (.getActionAvail SECCOMP_RET_ALLOW) { tsync := true } ByteArray.empty) Errno.EINVAL "nonzero flags"
  let unsafeZero := encodeFilter [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO }]
  let unsafeEfault := encodeFilter [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO ||| Errno.EFAULT }]
  let unsafeRetA := encodeFilter [{ code := 0x0016, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]
  let unsafeDivX := encodeFilter
    [{ code := 0x003c, jt := 0, jf := 0, k := 0 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]
  assertErr (← seccomp .setModeFilter {} unsafeZero) Errno.EINVAL "RET_ERRNO|0 guard"
  assertErr (← seccomp .setModeFilter {} unsafeEfault) Errno.EINVAL "RET_ERRNO|EFAULT guard"
  assertErr (← seccomp .setModeFilter {} unsafeRetA) Errno.EINVAL "BPF_RET|BPF_A guard"
  assertErr (← seccomp .setModeFilter {} unsafeDivX) Errno.EINVAL "BPF_DIV|BPF_X guard"
  runForkedOk "seccomp safe filter and TSYNC" do
    let euid ← SandboxEnv.getEuid
    let nnp0 ← match ← prctl .getNoNewPrivs with
      | .ok v => pure v
      | .error e => throw (IO.userError s!"getNoNewPrivs failed: {e}")
    if nnp0 == 0 && euid != 0 then
      assertErr (← seccomp .setModeFilter {} allowAllFilter) Errno.EACCES "seccomp before nnp"
    assertTrue ((← prctl .setNoNewPrivs) == .ok 0) "setNoNewPrivs failed"
    let argFilter := encodeFilter
      [ { code := 0x0020, jt := 0, jf := 0, k := 0 }
      , { code := 0x0015, jt := 1, jf := 0, k := 999999 }
      , { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }
      , { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO ||| Errno.EPERM } ]
    assertTrue ((← seccomp .setModeFilter {} argFilter) == .ok 0) "install allow/errno filter failed"
    assertTrue ((← seccomp .setModeFilter { tsync := true } allowAllFilter) == .ok 0) "TSYNC on same thread failed"
  runForkedOk "seccomp TSYNC_ESRCH across diverged sibling thread" do
    let _tid ← match ← SandboxEnv.spawnSyncThread with
      | .ok t => pure t
      | .error e => throw (IO.userError s!"spawnSyncThread failed: {e}")
    try
      assertTrue ((← prctl .setNoNewPrivs) == .ok 0) "setNoNewPrivs failed"
      assertTrue ((← seccomp .setModeFilter {} allowAllFilter) == .ok 0) "un-synced first filter failed"
      assertErr (← seccomp .setModeFilter { tsync := true, tsyncEsrch := true } allowAllFilter)
        Errno.ESRCH "diverged TSYNC_ESRCH must fail ESRCH"
    finally
      let _ ← SandboxEnv.stopSyncThread

/-- Verify 5-arg `prctl` ABI (`NO_NEW_PRIVS`, `CHILD_SUBREAPER`, `PDEATHSIG` bounds). -/
def assume_sandbox_prctl_nnpSubreaperAndPdeathsig : IO Unit := do
  runForkedOk "prctl commands" do
    let _ ← prctl .getNoNewPrivs
    assertErr (← prctl (.setPdeathsig 65)) Errno.EINVAL "PDEATHSIG 65"
    assertErr (← prctl (.setPdeathsig 100)) Errno.EINVAL "PDEATHSIG 100"
    assertTrue ((← prctl (.setPdeathsig 64)) == .ok 0) "PDEATHSIG 64"
    assertTrue ((← prctl (.setPdeathsig 9)) == .ok 0) "PDEATHSIG 9"
    assertTrue ((← prctl (.setPdeathsig 0)) == .ok 0) "PDEATHSIG 0"
    assertTrue ((← prctl (.setChildSubreaper true)) == .ok 0) "subreaper 1"
    assertTrue ((← prctl (.setChildSubreaper false)) == .ok 0) "subreaper 0"
    assertTrue ((← prctl .setNoNewPrivs) == .ok 0) "setNoNewPrivs"
    assertTrue ((← prctl .getNoNewPrivs) == .ok 1) "getNoNewPrivs == 1"
    assertTrue ((← prctl .setNoNewPrivs) == .ok 0) "idempotent setNoNewPrivs"

/-- Verify `setrlimit` `.core`/`.fsize`/`.nofile` monotonic `rlim_max` lowering, `cur <= max`, `RLIMIT_NOFILE=0` `EMFILE`, and `NOFILE_KERNEL_MAX` cap. -/
def assume_sandbox_setrlimit_curMaxAndHardCap : IO Unit := do
  runForkedOk "setrlimit cur/max/hard cap" do
    assertErr (← setrlimit .core 100 50) Errno.EINVAL "cur > max"
    assertTrue ((← setrlimit .core 0 0) == .ok ()) "core (0,0)"
    assertTrue ((← setrlimit .fsize 65536 131072) == .ok ()) "fsize (65536,131072)"
    assertTrue ((← setrlimit .fsize 131072 131072) == .ok ()) "fsize (131072,131072)"
    let (_, curMaxNofile) ← match ← SandboxEnv.getRlimit 2 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"getRlimit(nofile) failed: {e}")
    let safeHigh := if curMaxNofile > 64 then 64 else curMaxNofile
    assertTrue ((← setrlimit .nofile 0 safeHigh) == .ok ()) "nofile cur=0"
    assertErr (← memfdCreate "nf0".toUTF8 {}) Errno.EMFILE "memfd under NOFILE=0"
    assertErr (← landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0)
      Errno.EMFILE "landlockCreate under NOFILE=0"
    assertTrue ((← setrlimit .nofile safeHigh safeHigh) == .ok ()) "restore nofile"
    let mfd ← match ← memfdCreate "nfok".toUTF8 {} with
      | .ok f => pure f
      | .error e => throw (IO.userError s!"memfd after restore failed: {e}")
    closeFdChecked mfd
    assertErr (← setrlimit .nofile RLIM_INFINITY RLIM_INFINITY) Errno.EPERM "nofile RLIM_INFINITY"

/-- Verify `memfd_create` `0..249` name bounds, embedded NUL guard, and sealing flags. -/
def assume_sandbox_memfdCreate_nameBoundsAndSeals : IO Unit := do
  assertErr (← memfdCreate (ByteArray.mk #[97, 0, 98]) {}) Errno.EINVAL "embedded NUL"
  assertErr (← memfdCreate (repBytes 250 97) {}) Errno.EINVAL "name > 249"
  assertErr (← memfdCreate "a".toUTF8 { noexecSeal := true, exec := true }) Errno.EINVAL "noexecSeal|exec"
  let fdEmpty ← match ← memfdCreate ByteArray.empty { cloexec := true, allowSealing := true } with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"memfd empty name failed: {e}")
  let fdMax ← match ← memfdCreate (repBytes MFD_NAME_MAX 98) { cloexec := true, noexecSeal := true } with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"memfd 249-byte name failed: {e}")
  let fdNoClose ← match ← memfdCreate "x".toUTF8 { cloexec := false, allowSealing := false } with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"memfd cloexec=false failed: {e}")
  assertTrue ((← SandboxEnv.closeFd fdEmpty) == .ok ()) "close fdEmpty"
  assertTrue ((← SandboxEnv.closeFd fdMax) == .ok ()) "close fdMax"
  assertTrue ((← SandboxEnv.closeFd fdNoClose) == .ok ()) "close fdNoClose"

/-- Registry of all `7` external trust-boundary assumption probes matching `SpecTests.externalAssumptions`. -/
def registeredAssumptions : Array Core.RegisteredAssumption := #[
  ⟨"LeanSwe.LinuxSyscall.Sandbox.assume_sandbox_landlockCreateRuleset_versionAndRuleset",
    assume_sandbox_landlockCreateRuleset_versionAndRuleset⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.assume_sandbox_landlockAddRule_pathBeneathAndNetPort",
    assume_sandbox_landlockAddRule_pathBeneathAndNetPort⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.assume_sandbox_landlockRestrictSelf_nnpAndLayerCap",
    assume_sandbox_landlockRestrictSelf_nnpAndLayerCap⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.assume_sandbox_seccomp_actionAvailAndFilterAbi",
    assume_sandbox_seccomp_actionAvailAndFilterAbi⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.assume_sandbox_prctl_nnpSubreaperAndPdeathsig",
    assume_sandbox_prctl_nnpSubreaperAndPdeathsig⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.assume_sandbox_setrlimit_curMaxAndHardCap",
    assume_sandbox_setrlimit_curMaxAndHardCap⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.assume_sandbox_memfdCreate_nameBoundsAndSeals",
    assume_sandbox_memfdCreate_nameBoundsAndSeals⟩
]

/-- Real error test for `landlockCreateRuleset` (`EINVAL`, `ENOMSG`). -/
def err_landlockCreateRuleset_invalidArg : IO Unit := do
  assertErr (← landlockCreateRuleset none 0) Errno.EINVAL "null attr flags=0"
  assertErr (← landlockCreateRuleset none 7) Errno.EINVAL "null attr invalid query flags"
  assertErr (← landlockCreateRuleset (some {}) 0) ENOMSG "empty masks"

/-- Real error test for `landlockCreateRuleset` (`EMFILE` under `RLIMIT_NOFILE=0`). -/
def err_landlockCreateRuleset_transientOrResource : IO Unit := do
  runForkedOk "landlockCreateRuleset EMFILE" do
    assertTrue ((← setrlimit .nofile 0 64) == .ok ()) "setrlimit nofile 0"
    assertErr (← landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0)
      Errno.EMFILE "EMFILE expected"

/-- Real error test for `landlockAddRule` (`EBADF`, `EBADFD`). -/
def err_landlockAddRule_badFd : IO Unit := do
  withTempHostPaths fun dirPath _ => do
    let rs ← match ← landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_READ_DIR }) 0 with
      | .ok (.ruleset r) => pure r
      | other => throw (IO.userError s!"createRuleset: {repr other}")
    let mfd ← match ← memfdCreate "r".toUTF8 {} with
      | .ok f => pure f
      | .error e => throw (IO.userError s!"memfdCreate: {e}")
    let dirFd ← openHostOrThrow dirPath 1 "dir O_PATH"
    let closedFd ← match ← memfdCreate "closed".toUTF8 {} with
      | .ok f => pure f
      | .error e => throw (IO.userError s!"memfdCreate closed: {e}")
    closeFdChecked closedFd
    try
      assertErr (← landlockAddRule mfd (.pathBeneath dirFd LANDLOCK_ACCESS_FS_READ_DIR)) EBADFD "non-ruleset fd"
      assertErr (← landlockAddRule rs (.pathBeneath mfd LANDLOCK_ACCESS_FS_READ_DIR)) EBADFD "memfd parent"
      assertErr (← landlockAddRule closedFd (.pathBeneath dirFd LANDLOCK_ACCESS_FS_READ_DIR)) Errno.EBADF "closed ruleset"
    finally
      closeFdChecked rs
      closeFdChecked mfd
      closeFdChecked dirFd

/-- Real error test for `landlockAddRule` (`EINVAL`, `ENOMSG`). -/
def err_landlockAddRule_invalidArg : IO Unit := do
  withTempHostPaths fun _ filePath => do
    let rs ← match ← landlockCreateRuleset
        (some { handledAccessFs := LANDLOCK_ACCESS_FS_READ_FILE ||| LANDLOCK_ACCESS_FS_READ_DIR
                handledAccessNet := LANDLOCK_ACCESS_NET_CONNECT_TCP }) 0 with
      | .ok (.ruleset r) => pure r
      | other => throw (IO.userError s!"createRuleset: {repr other}")
    let fileFd ← openHostOrThrow filePath 3 "file O_PATH"
    try
      assertErr (← landlockAddRule rs (.pathBeneath fileFd LANDLOCK_ACCESS_FS_READ_DIR)) Errno.EINVAL "dir bit on file"
      assertErr (← landlockAddRule rs (.pathBeneath fileFd 0)) ENOMSG "empty access mask"
      assertErr (← landlockAddRule rs (.netPort 65536 LANDLOCK_ACCESS_NET_CONNECT_TCP)) Errno.EINVAL "port > 65535"
    finally
      closeFdChecked rs
      closeFdChecked fileFd

/-- Real error test for `landlockRestrictSelf` (`EBADF`, `EBADFD`). -/
def err_landlockRestrictSelf_badFd : IO Unit := do
  runForkedOk "landlockRestrictSelf badFd" do
    assertTrue ((← prctl .setNoNewPrivs) == .ok 0) "setNoNewPrivs"
    let mfd ← match ← memfdCreate "m".toUTF8 {} with
      | .ok f => pure f
      | .error e => throw (IO.userError s!"memfdCreate: {e}")
    assertErr (← landlockRestrictSelf mfd) EBADFD "memfd"
    closeFdChecked mfd
    assertErr (← landlockRestrictSelf mfd) Errno.EBADF "closed fd"

/-- Real error test for `landlockRestrictSelf` (`EPERM` before `no_new_privs`). -/
def err_landlockRestrictSelf_permissionDenied : IO Unit := do
  runForkedOk "landlockRestrictSelf EPERM" do
    let rs ← match ← landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0 with
      | .ok (.ruleset r) => pure r
      | other => throw (IO.userError s!"createRuleset: {repr other}")
    let nnp ← match ← prctl .getNoNewPrivs with
      | .ok v => pure v
      | .error e => throw (IO.userError s!"getNoNewPrivs: {e}")
    if nnp == 0 then
      assertErr (← landlockRestrictSelf rs) Errno.EPERM "expected EPERM before nnp"
    closeFdChecked rs

/-- Real error test for `landlockRestrictSelf` (`E2BIG` after 16 stacked layers). -/
def err_landlockRestrictSelf_limitOrUnsupported : IO Unit := do
  runForkedOk "landlockRestrictSelf E2BIG" do
    assertTrue ((← prctl .setNoNewPrivs) == .ok 0) "setNoNewPrivs"
    let rs ← match ← landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0 with
      | .ok (.ruleset r) => pure r
      | other => throw (IO.userError s!"createRuleset: {repr other}")
    for _ in List.range LANDLOCK_MAX_STACKED_LAYERS do
      assertTrue ((← landlockRestrictSelf rs) == .ok ()) "layer restrict"
    assertErr (← landlockRestrictSelf rs) Errno.E2BIG "17th layer E2BIG"
    closeFdChecked rs

/-- Real error test for `seccomp` (`EINVAL`). -/
def err_seccomp_invalidArg : IO Unit := do
  assertErr (← seccomp (.getActionAvail SECCOMP_RET_ALLOW) { tsync := true } ByteArray.empty) Errno.EINVAL "nonzero flags"
  assertErr (← seccomp .setModeFilter {} ByteArray.empty) Errno.EINVAL "empty filter"
  assertErr (← seccomp .setModeFilter {} (repBytes 7 0)) Errno.EINVAL "unaligned len"
  let badNoRet := encodeFilter [{ code := 0x0000, jt := 0, jf := 0, k := 0 }]
  runForkedOk "seccomp bad bpf EINVAL" do
    assertTrue ((← prctl .setNoNewPrivs) == .ok 0) "setNoNewPrivs"
    assertErr (← seccomp .setModeFilter {} badNoRet) Errno.EINVAL "program without RET"

/-- Real error test for `seccomp` (`EACCES` before `no_new_privs`). -/
def err_seccomp_permissionDenied : IO Unit := do
  runForkedOk "seccomp EACCES" do
    let nnp ← match ← prctl .getNoNewPrivs with
      | .ok v => pure v
      | .error e => throw (IO.userError s!"getNoNewPrivs: {e}")
    let euid ← SandboxEnv.getEuid
    if nnp == 0 && euid != 0 then
      assertErr (← seccomp .setModeFilter {} allowAllFilter) Errno.EACCES "expected EACCES before nnp"

/-- Real error test for `seccomp` (`EOPNOTSUPP`, `ESRCH`). -/
def err_seccomp_limitOrUnsupported : IO Unit := do
  assertErr (← seccomp (.getActionAvail 0x12340000) {} ByteArray.empty) Errno.EOPNOTSUPP "unknown action"
  runForkedOk "seccomp TSYNC_ESRCH" do
    let _ ← match ← SandboxEnv.spawnSyncThread with
      | .ok t => pure t
      | .error e => throw (IO.userError s!"spawnSyncThread: {e}")
    try
      assertTrue ((← prctl .setNoNewPrivs) == .ok 0) "setNoNewPrivs"
      assertTrue ((← seccomp .setModeFilter {} allowAllFilter) == .ok 0) "install base filter"
      assertErr (← seccomp .setModeFilter { tsync := true, tsyncEsrch := true } allowAllFilter)
        Errno.ESRCH "expected ESRCH"
    finally
      let _ ← SandboxEnv.stopSyncThread

/-- Real error test for `prctl` (`EINVAL`). -/
def err_prctl_invalidArg : IO Unit := do
  assertErr (← prctl (.setPdeathsig 65)) Errno.EINVAL "PDEATHSIG > 64"

/-- Real error test for `setrlimit` (`EINVAL`). -/
def err_setrlimit_invalidArg : IO Unit := do
  assertErr (← setrlimit .core 100 50) Errno.EINVAL "core cur > max"
  assertErr (← setrlimit .fsize 200 100) Errno.EINVAL "fsize cur > max"

/-- Real error test for `setrlimit` (`EPERM`). -/
def err_setrlimit_permissionDenied : IO Unit := do
  runForkedOk "setrlimit EPERM" do
    assertTrue ((← setrlimit .fsize 65536 131072) == .ok ()) "lower fsize"
    assertErr (← setrlimit .fsize 65536 131073) Errno.EPERM "raise fsize hard limit"
    assertErr (← setrlimit .nofile RLIM_INFINITY RLIM_INFINITY) Errno.EPERM "nofile RLIM_INFINITY"

/-- Real error test for `memfdCreate` (`EINVAL`). -/
def err_memfdCreate_invalidArg : IO Unit := do
  assertErr (← memfdCreate (ByteArray.mk #[97, 0]) {}) Errno.EINVAL "embedded NUL"
  assertErr (← memfdCreate (repBytes 250 97) {}) Errno.EINVAL "name > 249"
  assertErr (← memfdCreate "a".toUTF8 { noexecSeal := true, exec := true }) Errno.EINVAL "conflicting flags"
  assertErr (← (mkMockOps Errno.EIO).memfdCreate (ByteArray.mk #[97, 0]) {}) Errno.EINVAL "wrapper NUL guard"
  assertErr (← (mkMockOps Errno.EIO).memfdCreate (repBytes 250 97) {}) Errno.EINVAL "wrapper len guard"

/-- Real error test for `memfdCreate` (`EMFILE` under `RLIMIT_NOFILE=0`). -/
def err_memfdCreate_transientOrResource : IO Unit := do
  runForkedOk "memfdCreate EMFILE" do
    assertTrue ((← setrlimit .nofile 0 64) == .ok ()) "setrlimit nofile 0"
    assertErr (← memfdCreate "x".toUTF8 {}) Errno.EMFILE "EMFILE expected"

/-- Mocked error test for `landlockCreateRuleset` (`badFd`, `permissionDenied`, `limitOrUnsupported`). -/
def err_landlockCreateRuleset_mocked : IO Unit := do
  assertErr (← (mkMockOps Errno.EBADF).landlockCreateRuleset none 1) Errno.EBADF "mock EBADF"
  assertErr (← (mkMockOps Errno.EPERM).landlockCreateRuleset (some { handledAccessFs := 1 }) 0) Errno.EPERM "mock EPERM"
  assertErr (← (mkMockOps Errno.ENOSYS).landlockCreateRuleset none 1) Errno.ENOSYS "mock ENOSYS"

/-- Mocked error test for `landlockAddRule` (`permissionDenied`, `limitOrUnsupported`, `transientOrResource`). -/
def err_landlockAddRule_mocked : IO Unit := do
  let fd ← match ← memfdCreate "mk".toUTF8 {} with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"memfdCreate: {e}")
  try
    assertErr (← (mkMockOps Errno.EPERM).landlockAddRule fd (.netPort 80 1)) Errno.EPERM "mock EPERM"
    assertErr (← (mkMockOps Errno.EOPNOTSUPP).landlockAddRule fd (.netPort 80 1)) Errno.EOPNOTSUPP "mock EOPNOTSUPP"
    assertErr (← (mkMockOps Errno.ENOMEM).landlockAddRule fd (.netPort 80 1)) Errno.ENOMEM "mock ENOMEM"
  finally
    closeFdChecked fd

/-- Mocked error test for `landlockRestrictSelf` (`invalidArg`, `transientOrResource`). -/
def err_landlockRestrictSelf_mocked : IO Unit := do
  let fd ← match ← memfdCreate "mk".toUTF8 {} with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"memfdCreate: {e}")
  try
    assertErr (← (mkMockOps Errno.EINVAL).landlockRestrictSelf fd) Errno.EINVAL "mock EINVAL"
    assertErr (← (mkMockOps Errno.ENOMEM).landlockRestrictSelf fd) Errno.ENOMEM "mock ENOMEM"
  finally
    closeFdChecked fd

/-- Mocked error test for `seccomp` (`badFd`, `transientOrResource`). -/
def err_seccomp_mocked : IO Unit := do
  assertErr (← (mkMockOps Errno.EBADF).seccomp (.getActionAvail SECCOMP_RET_ALLOW) {} ByteArray.empty)
    Errno.EBADF "mock EBADF"
  assertErr (← (mkMockOps Errno.ENOMEM).seccomp .setModeFilter {} allowAllFilter)
    Errno.ENOMEM "mock ENOMEM"

/-- Mocked error test for `prctl` (`badFd`, `permissionDenied`, `limitOrUnsupported`, `transientOrResource`). -/
def err_prctl_mocked : IO Unit := do
  assertErr (← (mkMockOps Errno.EBADF).prctl .getNoNewPrivs) Errno.EBADF "mock EBADF"
  assertErr (← (mkMockOps Errno.EPERM).prctl .setNoNewPrivs) Errno.EPERM "mock EPERM"
  assertErr (← (mkMockOps Errno.ENOSYS).prctl .getNoNewPrivs) Errno.ENOSYS "mock ENOSYS"
  assertErr (← (mkMockOps Errno.EINTR).prctl .getNoNewPrivs) Errno.EINTR "mock EINTR"

/-- Mocked error test for `setrlimit` (`badFd`, `limitOrUnsupported`, `transientOrResource`). -/
def err_setrlimit_mocked : IO Unit := do
  assertErr (← (mkMockOps Errno.EBADF).setrlimit .core 0 0) Errno.EBADF "mock EBADF"
  assertErr (← (mkMockOps Errno.ENOSYS).setrlimit .core 0 0) Errno.ENOSYS "mock ENOSYS"
  assertErr (← (mkMockOps Errno.EINTR).setrlimit .core 0 0) Errno.EINTR "mock EINTR"

/-- Mocked error test for `memfdCreate` (`badFd`, `permissionDenied`, `limitOrUnsupported`). -/
def err_memfdCreate_mocked : IO Unit := do
  assertErr (← (mkMockOps Errno.EBADF).memfdCreate "m".toUTF8 {}) Errno.EBADF "mock EBADF"
  assertErr (← (mkMockOps Errno.EACCES).memfdCreate "m".toUTF8 {}) Errno.EACCES "mock EACCES"
  assertErr (← (mkMockOps Errno.ENOSYS).memfdCreate "m".toUTF8 {}) Errno.ENOSYS "mock ENOSYS"

/-- Registry of all `22` unique error-coverage tests matching `SpecTests.errorCoverage`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest := #[
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockCreateRuleset_invalidArg", .real, err_landlockCreateRuleset_invalidArg⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockCreateRuleset_transientOrResource", .real, err_landlockCreateRuleset_transientOrResource⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockAddRule_badFd", .real, err_landlockAddRule_badFd⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockAddRule_invalidArg", .real, err_landlockAddRule_invalidArg⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockRestrictSelf_badFd", .real, err_landlockRestrictSelf_badFd⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockRestrictSelf_permissionDenied", .real, err_landlockRestrictSelf_permissionDenied⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockRestrictSelf_limitOrUnsupported", .real, err_landlockRestrictSelf_limitOrUnsupported⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_seccomp_invalidArg", .real, err_seccomp_invalidArg⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_seccomp_permissionDenied", .real, err_seccomp_permissionDenied⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_seccomp_limitOrUnsupported", .real, err_seccomp_limitOrUnsupported⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_prctl_invalidArg", .real, err_prctl_invalidArg⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_setrlimit_invalidArg", .real, err_setrlimit_invalidArg⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_setrlimit_permissionDenied", .real, err_setrlimit_permissionDenied⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_memfdCreate_invalidArg", .real, err_memfdCreate_invalidArg⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_memfdCreate_transientOrResource", .real, err_memfdCreate_transientOrResource⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockCreateRuleset_mocked", .mocked, err_landlockCreateRuleset_mocked⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockAddRule_mocked", .mocked, err_landlockAddRule_mocked⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockRestrictSelf_mocked", .mocked, err_landlockRestrictSelf_mocked⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_seccomp_mocked", .mocked, err_seccomp_mocked⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_prctl_mocked", .mocked, err_prctl_mocked⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_setrlimit_mocked", .mocked, err_setrlimit_mocked⟩,
  ⟨"LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_memfdCreate_mocked", .mocked, err_memfdCreate_mocked⟩
]

/-- Worker entry point invoked under `strace -f -e inject=...` to check real C-ABI errno propagation for a single syscall (`EINTR`, `ENOMEM`, `EMFILE`/`ENFILE`, `ENOSYS`). -/
def runStraceWorker (mode : String) : IO Unit := do
  match mode with
  | "landlock_create_ruleset" =>
    match ← landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0 with
    | .error e => IO.println s!"STRACE_ERR={e}"
    | .ok _ => throw (IO.userError "strace injection did not intercept landlock_create_ruleset")
  | "landlock_add_rule" =>
    let rs ← match ← landlockCreateRuleset (some { handledAccessNet := LANDLOCK_ACCESS_NET_CONNECT_TCP }) 0 with
      | .ok (.ruleset r) => pure r
      | other => throw (IO.userError s!"createRuleset: {repr other}")
    try
      match ← landlockAddRule rs (.netPort 80 LANDLOCK_ACCESS_NET_CONNECT_TCP) with
      | .error e => IO.println s!"STRACE_ERR={e}"
      | .ok () => throw (IO.userError "strace injection did not intercept landlock_add_rule")
    finally
      closeFdChecked rs
  | "landlock_restrict_self" =>
    assertTrue ((← prctl .setNoNewPrivs) == .ok 0) "setNoNewPrivs"
    let rs ← match ← landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0 with
      | .ok (.ruleset r) => pure r
      | other => throw (IO.userError s!"createRuleset: {repr other}")
    try
      match ← landlockRestrictSelf rs with
      | .error e => IO.println s!"STRACE_ERR={e}"
      | .ok () => throw (IO.userError "strace injection did not intercept landlock_restrict_self")
    finally
      closeFdChecked rs
  | "seccomp" =>
    match ← seccomp (.getActionAvail SECCOMP_RET_ALLOW) {} ByteArray.empty with
    | .error e => IO.println s!"STRACE_ERR={e}"
    | .ok _ => throw (IO.userError "strace injection did not intercept seccomp")
  | "prctl" =>
    match ← prctl .getNoNewPrivs with
    | .error e => IO.println s!"STRACE_ERR={e}"
    | .ok _ => throw (IO.userError "strace injection did not intercept prctl")
  | "setrlimit" =>
    for _ in List.range 6 do
      match ← setrlimit .core 0 0 with
      | .error e =>
        IO.println s!"STRACE_ERR={e}"
        return ()
      | .ok () => pure ()
    throw (IO.userError "strace injection did not intercept setrlimit")
  | "memfd_create" =>
    match ← memfdCreate "strace".toUTF8 {} with
    | .error e => IO.println s!"STRACE_ERR={e}"
    | .ok fd =>
      closeFdChecked fd
      throw (IO.userError "strace injection did not intercept memfd_create")
  | other =>
    throw (IO.userError s!"unknown strace worker mode: {other}")

private def straceInjectOnce (exe : String) (syscallName workerMode errnoName : String) (expectedErrno : Errno) : IO Unit := do
  let spec := if syscallName == "setrlimit" then
      s!"prlimit64:error={errnoName}:when=5+"
    else
      s!"{syscallName}:error={errnoName}:when=1"
  let out ← IO.Process.output {
    cmd := "strace"
    args := #["-f", "-o", "/dev/null", "-e", s!"inject={spec}", exe, "--sandbox-strace-worker", workerMode]
  }
  if out.exitCode != 0 then
    throw (IO.userError s!"strace {syscallName}({errnoName}) failed rc={out.exitCode} out={out.stdout} err={out.stderr}")
  let expectedLine := s!"STRACE_ERR={expectedErrno}"
  if !(out.stdout.contains expectedLine) then
    throw (IO.userError s!"strace {syscallName}({errnoName}) missing '{expectedLine}' in stdout={out.stdout}")

/-- Run `strace -f` fault injection checks across all 7 syscalls (`EINTR`, `ENOMEM`, `EMFILE`/`ENFILE`, `ENOSYS`). -/
def runStraceFaultCheck : IO Unit := do
  let exe := (← IO.appPath).toString
  let matrix : Array (String × String × Array (String × Errno)) := #[
    ("landlock_create_ruleset", "landlock_create_ruleset",
      #[("EINTR", Errno.EINTR), ("ENOMEM", Errno.ENOMEM), ("ENFILE", Errno.ENFILE), ("ENOSYS", Errno.ENOSYS)]),
    ("landlock_add_rule", "landlock_add_rule",
      #[("EINTR", Errno.EINTR), ("ENOMEM", Errno.ENOMEM), ("ENOSYS", Errno.ENOSYS)]),
    ("landlock_restrict_self", "landlock_restrict_self",
      #[("EINTR", Errno.EINTR), ("ENOMEM", Errno.ENOMEM), ("ENOSYS", Errno.ENOSYS)]),
    ("seccomp", "seccomp",
      #[("EINTR", Errno.EINTR), ("ENOMEM", Errno.ENOMEM), ("ENOSYS", Errno.ENOSYS)]),
    ("prctl", "prctl",
      #[("EINTR", Errno.EINTR), ("ENOMEM", Errno.ENOMEM), ("ENOSYS", Errno.ENOSYS)]),
    ("setrlimit", "setrlimit",
      #[("EINTR", Errno.EINTR), ("ENOMEM", Errno.ENOMEM), ("ENOSYS", Errno.ENOSYS)]),
    ("memfd_create", "memfd_create",
      #[("EINTR", Errno.EINTR), ("ENOMEM", Errno.ENOMEM), ("EMFILE", Errno.EMFILE), ("ENFILE", Errno.ENFILE), ("ENOSYS", Errno.ENOSYS)])
  ]
  for (scName, mode, cases) in matrix do
    for (errName, errCode) in cases do
      straceInjectOnce exe scName mode errName errCode

/-- Execute all runtime assumption tests and all error-coverage tests for `LeanSwe.LinuxSyscall.Sandbox`. -/
def runAll : IO Unit := do
  Core.runRegisteredAssumptions registeredAssumptions
  Core.runRegisteredErrorTests registeredErrorTests

end LeanSwe.LinuxSyscall.Sandbox.RuntimeTests
