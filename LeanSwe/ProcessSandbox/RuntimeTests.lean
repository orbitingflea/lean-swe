import Core.Assumptions
import LeanSwe.ProcessSandbox.Interface
import LeanSwe.ProcessSandbox.RuntimeTests.Probes
import LeanSwe.ProcessSandbox.Seccomp.Model
import LeanSwe.ProcessSandbox.Seccomp.Interface
import LeanSwe.ProcessSandbox.Raw.Interface
import LeanSwe.Process.Interface
import LeanSwe.Fs.Interface

namespace LeanSwe.ProcessSandbox.RuntimeTests

open LeanSwe.ProcessSandbox
open LeanSwe.ProcessSandbox.RuntimeTests.Probes

/-- Real error test: `validateSpec` rejects empty `program` with `.invalidInput`. -/
def err_psandbox_validateSpec_invalidInput : IO Unit :=
  assertErrKind (ProcessSandbox.validateSpec { program := "" }) .invalidInput
    "validateSpec empty program -> invalidInput"

/-- Real error test: `run` rejects empty `program` with `.invalidInput`. -/
def err_psandbox_run_invalidInput : IO Unit := do
  assertErrKind (← ProcessSandbox.run { program := "" }) .invalidInput
    "run empty program -> invalidInput"

/-- Mocked error test: `run` maps `preflight` failure to `.unavailable`. -/
def err_psandbox_run_unavailable : IO Unit := do
  let api := ProcessSandbox.Internal.mkApiM mockPreflightUnavailableOps
  assertErrKind (← api.run { program := "/bin/true" }) .unavailable
    "run preflight failure -> unavailable"

/-- Mocked error test: `run` propagates `.notFound` from `spawnBox`. -/
def err_psandbox_run_notFound : IO Unit := do
  let api := ProcessSandbox.Internal.mkApiM
    (mockSpawnFailOps { kind := .notFound, path := some "/missing", message := "mock notFound" })
  assertErrKind (← api.run { program := "/bin/true" }) .notFound
    "run spawnBox notFound -> notFound"

/-- Mocked error test: `run` propagates `.permissionDenied` from `spawnBox`. -/
def err_psandbox_run_permissionDenied : IO Unit := do
  let api := ProcessSandbox.Internal.mkApiM
    (mockSpawnFailOps { kind := .permissionDenied, path := some "/denied", message := "mock permissionDenied" })
  assertErrKind (← api.run { program := "/bin/true" }) .permissionDenied
    "run spawnBox permissionDenied -> permissionDenied"

/-- Mocked error test: `run` propagates `.ioError` from `spawnBox`. -/
def err_psandbox_run_ioError : IO Unit := do
  let api := ProcessSandbox.Internal.mkApiM
    (mockSpawnFailOps { kind := .ioError, errnoCode := some 24, message := "mock ioError" })
  assertErrKind (← api.run { program := "/bin/true" }) .ioError
    "run spawnBox ioError -> ioError"

/-- Registered runtime error-coverage probes matching `LeanSwe.ProcessSandbox.errorCoverage`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest := #[
  { testName := "LeanSwe.ProcessSandbox.RuntimeTests.err_psandbox_validateSpec_invalidInput", mode := .real, run := err_psandbox_validateSpec_invalidInput },
  { testName := "LeanSwe.ProcessSandbox.RuntimeTests.err_psandbox_run_invalidInput", mode := .real, run := err_psandbox_run_invalidInput },
  { testName := "LeanSwe.ProcessSandbox.RuntimeTests.err_psandbox_run_unavailable", mode := .mocked, run := err_psandbox_run_unavailable },
  { testName := "LeanSwe.ProcessSandbox.RuntimeTests.err_psandbox_run_notFound", mode := .mocked, run := err_psandbox_run_notFound },
  { testName := "LeanSwe.ProcessSandbox.RuntimeTests.err_psandbox_run_permissionDenied", mode := .mocked, run := err_psandbox_run_permissionDenied },
  { testName := "LeanSwe.ProcessSandbox.RuntimeTests.err_psandbox_run_ioError", mode := .mocked, run := err_psandbox_run_ioError }
]

/-- Execute end-to-end OS runtime verification tests for `LeanSwe.ProcessSandbox`, returning `some reason` if skipped. -/
def runAllOutcome : IO (Option String) := do
  Core.runRegisteredErrorTests registeredErrorTests
  let baseCounts ← ProcessSandbox.Raw.activeResourceCounts
  assertTrue (baseCounts == { openPlans := 0, activeBoxes := 0, activeForwarders := 0 })
    "initial ProcessSandbox activeResourceCounts == 0"

  assertErrKind (ProcessSandbox.validateSpec { program := "" }) .invalidInput "empty program"
  assertErrKind (ProcessSandbox.validateSpec { program := "a\x00b" }) .invalidInput "NUL program"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", args := #["x\x00y"] }) .invalidInput "NUL arg"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", cwd := some "rel/dir" }) .invalidInput "relative cwd"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", mounts := #[.scratch "/usr/bad"] }) .invalidInput "reserved /usr"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", mounts := #[.scratch "/"] }) .invalidInput "reserved /"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", mounts := #[.scratch "/work", .scratch "/work/"] }) .invalidInput "dup boxPath"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", portForwards := #[{ boxPort := 0, hostPort := 80 }] }) .invalidInput "port 0"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", limits := { timeoutMs := 0 } }) .invalidInput "timeoutMs 0"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", limits := { memoryMaxBytes := some 0 } }) .invalidInput "memoryMaxBytes 0"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", limits := { pidsMax := some 0 } }) .invalidInput "pidsMax 0"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", env := #[("A=B", "1")] }) .invalidInput "env key ="

  let avail ← ProcessSandbox.isAvailable
  if !avail then
    assertErrKind (← ProcessSandbox.run { program := "/bin/true" }) .unavailable
      "ProcessSandbox.run fails closed .unavailable when unavailable"
    assertTrue ((← ProcessSandbox.Raw.activeResourceCounts) == baseCounts)
      "unavailable run leaves zero leaked resources"
    let skipReason ← match ← ProcessSandbox.Raw.preflight { needMemoryCgroup := true, needPidsCgroup := true } with
      | .error e => pure s!"isAvailable = false: {e.message}"
      | .ok () => pure "isAvailable = false"
    return some skipReason

  let cgParent ← findDelegatedCgroupParentDir
  let cgBefore ← countLeftoverCgroups cgParent

  let tmpDir ← IO.FS.createTempDir
  try
    let probeSrc := tmpDir / "probe.c"
    let probeBin := tmpDir / "probe"
    IO.FS.writeFile probeSrc probeCCode
    let ccRes ← LeanSwe.Process.runCommandChecked "cc"
      #["-O2", "-Wall", "-Wextra", "-Werror", "-pthread", probeSrc.toString, "-o", probeBin.toString]
    let _ ← match ccRes with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"failed to compile sandbox test probe: {e.message}")

    let emptyRootRes ← assertOk (← ProcessSandbox.run {
      program := "/bin/sh"
      args := #["-c",
        "test ! -e /home || exit 11; pwd; cat /etc/hosts; ls / >/dev/null || exit 12; touch /etc/evil 2>/dev/null && exit 13; touch /tmp/ephem.txt && echo OK"]
    }) "empty root, ! -e /home, default /tmp, cwd=/tmp, RO /etc"
    assertTrue (emptyRootRes.outcome == .exited 0) "empty root script exited 0"
    let emptyOut := String.fromUTF8! emptyRootRes.stdout
    assertTrue (emptyOut == "/tmp\n127.0.0.1 localhost\n::1 localhost\nOK\n")
      s!"empty root output mismatch: {repr emptyOut}"

    let ephemCheck ← assertOk (← ProcessSandbox.run {
      program := "/bin/sh"
      args := #["-c", "test ! -e /tmp/ephem.txt && echo CLEAN"]
    }) "scratch /tmp ephemeral across runs"
    assertTrue (ephemCheck.outcome == .exited 0 && String.fromUTF8! ephemCheck.stdout == "CLEAN\n")
      "scratch /tmp does not persist across runs"

    match ← IO.getEnv "HOME" with
    | some h =>
      if isSystemRootPrefix h then
        if ← System.FilePath.isDir h then
          let maskRes ← assertOk (← ProcessSandbox.run {
            program := "/bin/sh"
            args := #["-c", "ls \"$1\" >/dev/null 2>&1; echo rc=$?", "sh", h]
          }) "masked system-nested HOME"
          assertTrue (maskRes.outcome == .exited 0 &&
            (String.fromUTF8! maskRes.stdout).trimAscii.toString != "rc=0")
            "masked nested $HOME denies opendir"
    | none => pure ()

    let customTmpHost := tmpDir / "custom_tmp"
    IO.FS.createDirAll customTmpHost
    let tmpOverrideRes ← assertOk (← ProcessSandbox.run {
      program := "/bin/sh"
      args := #["-c", "printf 'override' > /tmp/saved.txt"]
      mounts := #[.readWrite customTmpHost.toString "/tmp"]
    }) "custom /tmp override"
    assertTrue (tmpOverrideRes.outcome == .exited 0) "custom /tmp override exited 0"
    assertTrue ((← IO.FS.readFile (customTmpHost / "saved.txt")) == "override")
      "custom /tmp override persisted on host"

    let roDir := tmpDir / "ro"
    let rwDir := tmpDir / "rw"
    let nestedRo := rwDir / "ro_sub"
    IO.FS.createDirAll roDir
    IO.FS.createDirAll nestedRo
    IO.FS.writeFile (roDir / "hello.txt") "ro_val"
    IO.FS.writeFile (nestedRo / "locked.txt") "sub_val"
    let mountRes ← assertOk (← ProcessSandbox.run {
      program := "/bin/sh"
      args := #["-c",
        "cat /ro/hello.txt; touch /ro/fail 2>/dev/null && exit 21; cat /rw/ro_sub/locked.txt; touch /rw/ro_sub/fail 2>/dev/null && exit 22; printf 'rw_ok' > /rw/out.txt; printf 'scr_ok' > /scr/f.txt && cat /scr/f.txt"]
      mounts :=
        #[ .readOnly roDir.toString "/ro"
         , .readWrite rwDir.toString "/rw"
         , .readOnly nestedRo.toString "/rw/ro_sub"
         , .scratch "/scr" ]
    }) "readOnly vs readWrite vs scratch and nested mounts"
    assertTrue (mountRes.outcome == .exited 0 &&
      String.fromUTF8! mountRes.stdout == "ro_valsub_valscr_ok") "mount read/write semantics"
    assertTrue ((← IO.FS.readFile (rwDir / "out.txt")) == "rw_ok") "readWrite wrote host file"

    let singleFile := tmpDir / "single.txt"
    IO.FS.writeFile singleFile "single_file_content"
    let fileMountRes ← assertOk (← ProcessSandbox.run {
      program := "/bin/cat"
      args := #["/data/single.txt"]
      mounts := #[.readOnly singleFile.toString "/data/single.txt"]
    }) "single file Landlock !S_ISDIR mount"
    assertTrue (fileMountRes.outcome == .exited 0 &&
      String.fromUTF8! fileMountRes.stdout == "single_file_content") "single file mount readable"

    let x86Prog := Seccomp.compileSeccompBpf .x86_64
    let aarch64Prog := Seccomp.compileSeccompBpf .aarch64
    assertTrue (Model.isValidLinuxSeccompProg x86Prog && Model.isValidLinuxSeccompProg aarch64Prog)
      "Seccomp.compileSeccompBpf produces valid Linux seccomp filters"
    assertTrue ((Seccomp.encodeSeccompBpf x86Prog).size == 8 * x86Prog.size &&
      (Seccomp.encodeSeccompBpf aarch64Prog).size == 8 * aarch64Prog.size)
      "Seccomp.encodeSeccompBpf produces 8*n wire bytes"
    let seccompRes ← assertOk (← ProcessSandbox.run {
      program := "/box/probe"
      args := #["--seccomp"]
      mounts := #[.readOnly probeBin.toString "/box/probe"]
    }) "seccomp + clone3 ENOSYS + pthread_create + socketpair vs socket(AF_UNIX) + Landlock init mask"
    if seccompRes.outcome == .exited 23 then
      throw (IO.userError
        s!"ASSERTION FAILED: an ordinary process creation without namespace flags must succeed inside the box (got exited 23, err={String.fromUTF8! seccompRes.stderr})")
    assertTrue (seccompRes.outcome == .exited 0 &&
      String.fromUTF8! seccompRes.stdout == "SECCOMP_ALL_OK\n")
      s!"seccomp probe outcome: {repr seccompRes.outcome} err={String.fromUTF8! seccompRes.stderr}"

    let envDefaultRes ← assertOk (← ProcessSandbox.run { program := "/usr/bin/env" }) "clean env default PATH"
    assertTrue (envDefaultRes.outcome == .exited 0 &&
      (String.fromUTF8! envDefaultRes.stdout).trimAscii.toString == "PATH=/usr/bin:/bin")
      "clean env inherits zero host vars and injects default PATH"

    let envCustomRes ← assertOk (← ProcessSandbox.run {
      program := "/usr/bin/env"
      env := #[("K", "old"), ("K", "new"), ("PATH", "/bin:/usr/bin")]
    }) "clean env last-write-wins"
    let envCustomOut := String.fromUTF8! envCustomRes.stdout
    assertTrue (envCustomRes.outcome == .exited 0 &&
      (envCustomOut == "PATH=/bin:/usr/bin\nK=new\n" || envCustomOut == "K=new\nPATH=/bin:/usr/bin\n"))
      s!"custom env output: {repr envCustomOut}"

    let privProc ← IO.Process.spawn {
      cmd := "python3"
      args := #["-c", silentListenerPy]
      stdout := .piped
      stderr := .null
    }
    let privPort : UInt16 ← try
      let line ← privProc.stdout.getLine
      match line.trimAscii.toString.toNat? with
      | some n => pure (UInt16.ofNat n)
      | none => throw (IO.userError s!"invalid port line: {repr line}")
    catch err =>
      let _ ← privProc.kill
      let _ ← privProc.wait
      throw err
    try
      let blockedNetRes ← assertOk (← ProcessSandbox.run {
        program := "/box/probe"
        args := #["--tcp-connect", toString privPort.toNat]
        mounts := #[.readOnly probeBin.toString "/box/probe"]
        allowBoxLocalhost := false
      }) "allowBoxLocalhost=false blocks TCP connect to unforwarded host port"
      assertTrue (blockedNetRes.outcome == .exited 31 &&
        (String.fromUTF8! blockedNetRes.stdout).trimAscii.toString == "connect_errno=13")
        s!"Landlock blocks connect with EACCES: {String.fromUTF8! blockedNetRes.stdout}"

      let isoLoRes ← assertOk (← ProcessSandbox.run {
        program := "/box/probe"
        args := #["--tcp-connect", toString privPort.toNat]
        mounts := #[.readOnly probeBin.toString "/box/probe"]
        allowBoxLocalhost := true
      }) "allowBoxLocalhost=true cannot reach host 127.0.0.1"
      assertTrue (isoLoRes.outcome == .exited 31 &&
        (String.fromUTF8! isoLoRes.stdout).trimAscii.toString == "connect_errno=111")
        s!"isolated netns ECONNREFUSED on host loopback: {String.fromUTF8! isoLoRes.stdout}"
    finally
      let _ ← privProc.kill
      let _ ← privProc.wait

    let selfLoRes ← assertOk (← ProcessSandbox.run {
      program := "/box/probe"
      args := #["--tcp-loopback-self"]
      mounts := #[.readOnly probeBin.toString "/box/probe"]
      allowBoxLocalhost := true
    }) "allowBoxLocalhost=true permits bind and connect inside box 127.0.0.1"
    assertTrue (selfLoRes.outcome == .exited 0 &&
      String.fromUTF8! selfLoRes.stdout == "BOX_LO_OK\n") "box self loopback ok"

    let halfProc ← IO.Process.spawn {
      cmd := "python3"
      args := #["-c", halfCloseServerPy]
      stdout := .piped
      stderr := .piped
    }
    let halfHostPort : UInt16 ← try
      let line ← halfProc.stdout.getLine
      match line.trimAscii.toString.toNat? with
      | some n => pure (UInt16.ofNat n)
      | none => throw (IO.userError s!"invalid half-close port: {repr line}")
    catch err =>
      let _ ← halfProc.kill
      let _ ← halfProc.wait
      throw err
    try
      let fwdRes ← assertOk (← ProcessSandbox.run {
        program := "/box/probe"
        args := #["--tcp-connect", "19201", "--half-close"]
        mounts := #[.readOnly probeBin.toString "/box/probe"]
        allowBoxLocalhost := false
        portForwards := #[{ boxPort := 19201, hostPort := halfHostPort }]
      }) "portForwards directional SHUT_WR half-close roundtrip"
      assertTrue (fwdRes.outcome == .exited 0 &&
        String.fromUTF8! fwdRes.stdout == "HALF_CLOSE_OK\n")
        s!"portForwards half-close failed: {repr fwdRes.outcome} out={String.fromUTF8! fwdRes.stdout} err={String.fromUTF8! fwdRes.stderr}"
    catch err =>
      let _ ← halfProc.kill
      let _ ← halfProc.wait
      throw err
    let _ ← halfProc.wait

    let echoProc ← IO.Process.spawn {
      cmd := "python3"
      args := #["-c", echoHalfCloseServerPy]
      stdout := .piped
      stderr := .null
    }
    let echoHostPort : UInt16 ← try
      let line ← echoProc.stdout.getLine
      match line.trimAscii.toString.toNat? with
      | some n => pure (UInt16.ofNat n)
      | none => throw (IO.userError s!"invalid echo port: {repr line}")
    catch err =>
      let _ ← echoProc.kill
      let _ ← echoProc.wait
      throw err
    try
      let ringRes ← assertOk (← ProcessSandbox.run {
        program := "/box/probe"
        args := #["--tcp-ring", "19202"]
        mounts := #[.readOnly probeBin.toString "/box/probe"]
        portForwards := #[{ boxPort := 19202, hostPort := echoHostPort }]
      }) "64 KiB ring buffer half-close roundtrip"
      assertTrue (ringRes.outcome == .exited 0 &&
        String.fromUTF8! ringRes.stdout == "RING_64K_OK\n")
        s!"64 KiB ring test failed: {repr ringRes.outcome}"

      let burstRes ← assertOk (← ProcessSandbox.run {
        program := "/box/probe"
        args := #["--tcp-burst", "19203"]
        mounts := #[.readOnly probeBin.toString "/box/probe"]
        portForwards := #[{ boxPort := 19203, hostPort := echoHostPort }]
      }) "140-connection burst over MAX_RELAY_SLOTS = 128"
      assertTrue (burstRes.outcome == .exited 0 &&
        String.fromUTF8! burstRes.stdout == "BURST_140_OK\n")
        s!"burst test failed: {repr burstRes.outcome}"

      let rstRes ← assertOk (← ProcessSandbox.run {
        program := "/box/probe"
        args := #["--tcp-half-rst", "19204"]
        mounts := #[.readOnly probeBin.toString "/box/probe"]
        portForwards := #[{ boxPort := 19204, hostPort := echoHostPort }]
      }) "half-close followed by RST while peer holds open"
      assertTrue (rstRes.outcome == .exited 0 &&
        String.fromUTF8! rstRes.stdout == "HALF_RST_OK\n")
        s!"half-close RST test failed: {repr rstRes.outcome}"

      let fwdTasks ← (List.range 4).mapM fun idx => IO.asTask do
        ProcessSandbox.run {
          program := "/box/probe"
          args := #["--tcp-ring", toString (19210 + idx)]
          mounts := #[.readOnly probeBin.toString "/box/probe"]
          portForwards := #[{ boxPort := UInt16.ofNat (19210 + idx), hostPort := echoHostPort }]
          limits := { timeoutMs := 15_000 }
        }
      for (idx, t) in (List.range 4).zip fwdTasks do
        let tr := t.get
        match tr with
        | .error ioErr => throw (IO.userError s!"concurrent fwd task {idx} threw IO error: {ioErr}")
        | .ok r =>
          let okR ← assertOk r s!"concurrent fwd task {idx}"
          assertTrue (okR.outcome == .exited 0 && String.fromUTF8! okR.stdout == "RING_64K_OK\n")
            s!"concurrent fwd task {idx} failed"
    finally
      let _ ← echoProc.kill
      let _ ← echoProc.wait

    let pids1Res ← assertOk (← ProcessSandbox.run {
      program := "/box/probe"
      args := #["--pids1"]
      mounts := #[.readOnly probeBin.toString "/box/probe"]
      limits := { timeoutMs := 10_000, pidsMax := some 1 }
    }) "pidsMax = some 1 runs 1 guest task and blocks 2nd fork"
    assertTrue (pids1Res.outcome == .exited 0)
      s!"pidsMax=1 outcome: {repr pids1Res.outcome} out={String.fromUTF8! pids1Res.stdout}"

    let oomRes ← assertOk (← ProcessSandbox.run {
      program := "/box/probe"
      args := #["--mem2"]
      mounts := #[.readOnly probeBin.toString "/box/probe"]
      limits := { timeoutMs := 15_000, memoryMaxBytes := some (20 * 1024 * 1024), pidsMax := some 8 }
    }) "whole-box multi-child cgroup v2 memory.max enforcement"
    assertTrue (oomRes.outcome == .signaled 9)
      s!"expected cgroup OOM SIGKILL (signaled 9), got {repr oomRes.outcome}"

    let oomChildRes ← assertOk (← ProcessSandbox.run {
      program := "/box/probe"
      args := #["--mem-child"]
      mounts := #[.readOnly probeBin.toString "/box/probe"]
      limits := { timeoutMs := 15_000, memoryMaxBytes := some (20 * 1024 * 1024), pidsMax := some 8 }
    }) "child OOM kills whole box atomically via cgroup memory.oom.group"
    assertTrue (oomChildRes.outcome == .signaled 9)
      s!"expected atomic whole-box OOM SIGKILL (signaled 9), got {repr oomChildRes.outcome}"

    let fsizeRes ← assertOk (← ProcessSandbox.run {
      program := "/bin/sh"
      args := #["-c", "dd if=/dev/zero of=/tmp/big bs=1024 count=64 2>/dev/null; echo rc=$?"]
      limits := { timeoutMs := 10_000, fileSizeMaxBytes := some 4096 }
    }) "RLIMIT_FSIZE enforces fileSizeMaxBytes"
    assertTrue (fsizeRes.outcome != .exited 0 ||
      (String.fromUTF8! fsizeRes.stdout).trimAscii.toString != "rc=0")
      s!"fileSizeMaxBytes did not block 64 KiB write: {repr fsizeRes.outcome} out={String.fromUTF8! fsizeRes.stdout}"

    let tasks ← (List.range 4).mapM fun idx => IO.asTask do
      ProcessSandbox.run {
        program := "/bin/cat"
        stdin := s!"task-{idx}".toUTF8
        limits := { timeoutMs := 15_000 }
      }
    for (idx, t) in (List.range 4).zip tasks do
      let tr := t.get
      match tr with
      | .error ioErr => throw (IO.userError s!"concurrent task {idx} threw IO error: {ioErr}")
      | .ok r =>
        let okR ← assertOk r s!"concurrent task {idx}"
        assertTrue (okR.outcome == .exited 0 && String.fromUTF8! okR.stdout == s!"task-{idx}")
          s!"concurrent task {idx} stdout mismatch"

    for code in ([97, 98, 125, 126, 127, 255] : List Int) do
      let codeRes ← assertOk (← ProcessSandbox.run {
        program := "/box/probe"
        args := #["--exit", toString code]
        mounts := #[.readOnly probeBin.toString "/box/probe"]
      }) s!"magic exit code {code} verbatim"
      assertTrue (codeRes.outcome == .exited code) s!"expected exited {code}, got {repr codeRes.outcome}"

    assertErrKind (← ProcessSandbox.run { program := "/no/such/binary_999" }) .notFound "missing program"
    assertErrKind (← ProcessSandbox.run { program := "/bin/true", cwd := some "/no/such/cwd" }) .notFound
      "missing cwd"
    let noExec := tmpDir / "noexec_script"
    IO.FS.writeFile noExec "#!/bin/sh\necho nope\n"
    let _ ← assertOk (← LeanSwe.Fs.chmod noExec.toString 0o644) "chmod 0644"
    assertErrKind (← ProcessSandbox.run {
      program := "/box/noexec"
      mounts := #[.readOnly noExec.toString "/box/noexec"]
    }) .permissionDenied "non-executable program"

    let toRes ← assertOk (← ProcessSandbox.run {
      program := "/bin/sleep"
      args := #["10"]
      limits := { timeoutMs := 150 }
    }) "timeoutMs"
    assertTrue (toRes.outcome == .timedOut) s!"expected timedOut, got {repr toRes.outcome}"

    let zeroCapOk ← assertOk (← ProcessSandbox.run {
      program := "/bin/true"
      limits := { timeoutMs := 10_000, maxOutputBytes := some 0 }
    }) "maxOutputBytes = some 0 allows 0 emitted bytes"
    assertTrue (zeroCapOk.outcome == .exited 0) "maxOutputBytes=0 with silent command exited 0"

    let overOut ← assertOk (← ProcessSandbox.run {
      program := "/usr/bin/printf"
      args := #["1234567890"]
      limits := { timeoutMs := 10_000, maxOutputBytes := some 4 }
    }) "maxOutputBytes = some 4"
    assertTrue (overOut.outcome == .outputLimitExceeded &&
      overOut.stdout.size + overOut.stderr.size <= 4)
      s!"outputLimitExceeded mismatch: {repr overOut.outcome}"

    let flockDir := tmpDir / "flock_rw"
    IO.FS.createDirAll flockDir
    let flockFile := flockDir / "grandchild.lock"
    let dfRes ← assertOk (← ProcessSandbox.run {
      program := "/box/probe"
      args := #["--double-fork-flock", "/flock/grandchild.lock"]
      mounts := #[.readOnly probeBin.toString "/box/probe", .readWrite flockDir.toString "/flock"]
      limits := { timeoutMs := 10_000 }
    }) "double-forked grandchild killed and reaped"
    assertTrue (dfRes.outcome == .exited 0 &&
      String.fromUTF8! dfRes.stdout == "PARENT_EXITED\n") "parent exited cleanly"
    match ← LeanSwe.Fs.tryWithFileLock flockFile.toString .exclusive true (pure (.ok ())) with
    | .ok (some ()) => pure ()
    | .ok none => throw (IO.userError "double-forked grandchild still holds flock")
    | .error e => throw (IO.userError s!"double-forked grandchild flock check failed: {e.message}")

    assertTrue ((← ProcessSandbox.Raw.activeResourceCounts) == baseCounts)
      "final ProcessSandbox activeResourceCounts == 0"
    let cgAfter ← countLeftoverCgroups cgParent
    assertTrue (cgAfter <= cgBefore) "zero leftover cgroup v2 directories"
  finally
    IO.FS.removeDirAll tmpDir
  IO.println "PASS: LeanSwe.ProcessSandbox runtime tests"
  return none

/-- Execute end-to-end OS runtime verification tests for `LeanSwe.ProcessSandbox`. -/
def runAll : IO Unit := do
  let _ ← runAllOutcome

end LeanSwe.ProcessSandbox.RuntimeTests
