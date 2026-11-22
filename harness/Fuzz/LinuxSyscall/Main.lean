import Fuzz.Common.Suite
import LeanSwe.Fs.Raw.Interface
import LeanSwe.LinuxSyscall.Files.SpecTests
import Fuzz.LinuxSyscall.Env
import Fuzz.LinuxSyscall.Files.Fuzz
import Fuzz.LinuxSyscall.Files.Strace
import Fuzz.LinuxSyscall.Sandbox.Fuzz
import Fuzz.LinuxSyscall.Sandbox.Strace
import Fuzz.LinuxSyscall.TimeRand.Fuzz
import Fuzz.LinuxSyscall.TimeRand.Strace
import Fuzz.LinuxSyscall.Poll.Fuzz
import Fuzz.LinuxSyscall.Poll.Strace
import Fuzz.LinuxSyscall.Net.Fuzz
import Fuzz.LinuxSyscall.Net.Strace
import Fuzz.LinuxSyscall.ProcessEnv
import Fuzz.LinuxSyscall.Process.Fuzz
import Fuzz.LinuxSyscall.Process.Strace

namespace Fuzz.LinuxSyscall.Main

open Fuzz.Common
open Fuzz.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open Fuzz.LinuxSyscall.FilesFuzz

/-- LinuxSyscall-specific CLI options shared across the world-model suites and isolated workers. -/
structure WorldOptions where
  /-- Require `vm.memfd_noexec=2` strict assertions in the `sandbox` suite. -/
  requireMemfdStrict : Bool := false
  /-- Allow skipping `CLONE_NEWTIME` (`timens`) sub-episodes when unshare is unavailable. -/
  allowNoTimens : Bool := false
  /-- Require unprivileged namespaces (`CLONE_NEWUSER`/`CLONE_NEWPID`/`CLONE_NEWNET`/`CLONE_NEWNS`) in suites that use them. -/
  requireNs : Bool := false
  /-- Optional child-environment mode (`seccomp` or `timens`) used internally for forked `timerand` sub-episodes. -/
  envChild? : Option String := none
  /-- Optional `errno` value (`1..4095`) for seccomp workers. -/
  seccompErrno : UInt32 := 1
  /-- Syscall bitmask (`bit0=clock_gettime`, `bit1=clock_nanosleep`, `bit2=getrandom`) for `--env-child seccomp`. -/
  seccompMask : UInt32 := 7
  /-- Optional un-filtered warmup steps before installing `seccomp` in `--env-child seccomp`. -/
  seccompDelaySteps : Nat := 0
  /-- Worker mode for `CLONE_NEWUSER | CLONE_NEWNET` `lo`-down probe. -/
  netUsernsWorker : Bool := false
  /-- Worker mode for outer `SECCOMP_RET_ERRNO` test on `Poll`. -/
  pollSeccompWorker : Bool := false
  /-- Worker mode for outer `SECCOMP_RET_ERRNO` test on `Net`. -/
  netSeccompWorker : Bool := false
  /-- Internal child flag: entered new user+net namespace, bring `lo` up and drop `CAP_NET_ADMIN`. -/
  initNetnsDropCaps : Bool := false
  /-- Internal child flag: running inside netns with `CAP_NET_ADMIN` dropped. -/
  inNetns : Bool := false
  /-- Scratch directory root for `files` fuzzer episodes (`--dir` / `--fs-root`). -/
  dir : String := "/dev/shm"
  /-- Whether `--dir` or `--fs-root` was explicitly provided on the CLI. -/
  explicitDir : Bool := false
  /-- Optional isolated worker submode invoked under `unshare` or `chroot`. -/
  workerMode? : Option String := none
  /-- Optional cross-filesystem directory path for `EXDEV` fuzzing. -/
  crossDir? : Option String := none
  /-- Optional root directory path used when entering a `chroot` worker. -/
  chrootDir? : Option String := none
  /-- Whether host-protected sticky/FIFO/regular `sysctl`s are enabled. -/
  hostProtected : Bool := false
  /-- Optional `(lowerDir, count)` pair for pre-seeded overlayfs lower tree. -/
  seedOverlayLower? : Option (String × Nat) := none
  /-- Optional read-only tree path for seeding read-only mount fuzzing. -/
  seedRoTree? : Option String := none
  /-- Assert that pre-seeded overlayfs lower directories are actively mounted and used. -/
  preseededEps : Bool := false
  /-- Enforce coverage assertions on standalone `--worker-mode` invocations. -/
  assertWorkerHits : Bool := false
  /-- Optional soft `RLIMIT_NOFILE` override inside `--worker-mode` episodes. -/
  rlimitNofile? : Option UInt64 := none
  /-- Close raw FD `0` inside `--worker-mode` after runtime initialization. -/
  closeFd0 : Bool := false
  deriving Repr

/-- Return `true` when any isolated worker or fixture-seeding submode flag is set. -/
def WorldOptions.hasSpecialMode (opts : WorldOptions) : Bool :=
  opts.seedOverlayLower?.isSome ||
  opts.seedRoTree?.isSome ||
  opts.netUsernsWorker ||
  opts.pollSeccompWorker ||
  opts.netSeccompWorker ||
  opts.workerMode?.isSome ||
  opts.envChild?.isSome ||
  opts.initNetnsDropCaps ||
  opts.inNetns

private def requiredExtraErrorHits : Array (String × String) := #[
  ("write", "stateConflict"),
  ("write", "permissionDenied"),
  ("fchmod", "stateConflict"),
  ("fchmod", "permissionDenied"),
  ("fsync", "invalidArg")
]

private def outPrintln (stdoutOpen : Bool) (msg : String) : IO Unit :=
  if stdoutOpen then IO.println msg else pure ()

private def errPrintln (stderrOpen : Bool) (msg : String) : IO Unit :=
  if stderrOpen then IO.eprintln msg else pure ()

private def printAndAssertFilesHits (stdoutOpen : Bool) (stats : HitStats) (steps : Nat)
    (isRoSeeded : Bool := false) (allowExtraMatrix : Bool := true)
    (realStats : HitStats := stats) : IO Unit := do
  let entries := stats.counts.toList.mergeSort (fun a b => a.1 < b.1)
  outPrintln stdoutOpen "SYSCALL_OUTCOME_HITS:"
  for (bucket, count) in entries do
    outPrintln stdoutOpen s!"  {bucket} = {count}"
  outPrintln stdoutOpen "SYSCALL_ERROR_KIND_MATRIX:"
  for sname in allSyscallNames do
    let okHits := stats.kindCounts.getD s!"{sname}:ok" 0
    let nfHits := stats.kindCounts.getD s!"{sname}:notFound" 0
    let bfHits := stats.kindCounts.getD s!"{sname}:badFd" 0
    let iaHits := stats.kindCounts.getD s!"{sname}:invalidArg" 0
    let scHits := stats.kindCounts.getD s!"{sname}:stateConflict" 0
    let pdHits := stats.kindCounts.getD s!"{sname}:permissionDenied" 0
    let trHits := stats.kindCounts.getD s!"{sname}:transientOrResource" 0
    outPrintln stdoutOpen s!"  {sname}: ok={okHits} notFound={nfHits} badFd={bfHits} invalidArg={iaHits} stateConflict={scHits} permissionDenied={pdHits} transientOrResource={trHits}"
  if steps >= 1000 then
    for sname in allSyscallNames do
      let prefixStr := sname ++ ":"
      let totalForSyscall := entries.foldl (fun acc (k, v) =>
        if k.startsWith prefixStr then acc + v else acc) 0
      if totalForSyscall == 0 then
        throw (IO.userError s!"fuzzer coverage assertion failed: syscall '{sname}' had 0 hits")
    let okCount := entries.foldl (fun acc (k, v) =>
      if k.endsWith ":ok" then acc + v else acc) 0
    let errCount := entries.foldl (fun acc (k, v) =>
      if (k.splitOn ":err(").length > 1 then acc + v else acc) 0
    if okCount == 0 || errCount == 0 then
      throw (IO.userError s!"fuzzer coverage assertion failed: ok={okCount} err={errCount}")
    if isRoSeeded then
      let pdTotal := allSyscallNames.foldl (fun acc sname =>
        acc + stats.kindCounts.getD s!"{sname}:permissionDenied" 0) 0
      if pdTotal == 0 then
        throw (IO.userError "fuzzer ro_bind assertion failed: 0 permissionDenied (EROFS) hits")
  if steps >= 50000 && allowExtraMatrix then
    let mut missing : Array String := #[]
    for sname in allSyscallNames do
      if realStats.kindCounts.getD s!"{sname}:ok" 0 == 0 then
        missing := missing.push s!"{sname}:ok"
    for ob in LeanSwe.LinuxSyscall.Files.errorCoverage do
      match ob.justification with
      | .tested _ .real =>
        let sname := ob.request.splitOn "." |>.getLast!
        let kname := filesErrorKindName ob.errorKind
        if realStats.kindCounts.getD s!"{sname}:{kname}" 0 == 0 then
          missing := missing.push s!"{sname}:{kname}"
      | _ => pure ()
    for (sname, kname) in requiredExtraErrorHits do
      if realStats.kindCounts.getD s!"{sname}:{kname}" 0 == 0 then
        missing := missing.push s!"{sname}:{kname}"
    if !missing.isEmpty then
      throw (IO.userError s!"fuzzer errorCoverage matrix failed with 0 hits on: {missing.toList}")

private def printAndAssertHits (suiteName : String) (expectedNames : Array String)
    (counts : Std.HashMap String Nat) (minStepsForCoverage : Bool)
    (requiredErrs : Array UInt32 := #[]) (checkAccept4Ok : Bool := false) : IO Unit := do
  let entries := counts.toList.mergeSort (fun a b => a.1 < b.1)
  IO.println s!"SYSCALL_OUTCOME_HITS ({suiteName}):"
  for (bucket, count) in entries do
    IO.println s!"  {bucket} = {count}"
  if minStepsForCoverage then
    for sname in expectedNames do
      let okHits := counts.getD s!"{sname}:ok" 0
      let prefixErr := sname ++ ":err("
      let errHits := entries.foldl (fun acc (k, v) =>
        if k.startsWith prefixErr then acc + v else acc) 0
      if okHits == 0 || errHits == 0 then
        throw (IO.userError s!"{suiteName} fuzzer coverage assertion failed: syscall '{sname}' had ok={okHits} err={errHits}")
    if checkAccept4Ok then
      let accOk := counts.getD "accept4:ok" 0
      if accOk == 0 then
        throw (IO.userError s!"{suiteName} fuzzer coverage assertion failed: accept4:ok had 0 hits")
    for requiredErr in requiredErrs do
      let suffix := s!":err({requiredErr})"
      let hits := entries.foldl (fun acc (k, v) =>
        if k.endsWith suffix then acc + v else acc) 0
      if hits == 0 then
        throw (IO.userError s!"{suiteName} fuzzer coverage assertion failed: required errno {requiredErr} had 0 hits")

private def countSelfFds : IO Nat := do
  match ← LeanSwe.Fs.Raw.defaultOps.readDir "/proc/self/fd" with
  | .ok names => return names.size
  | .error _ => return 0

private def runFilesSuiteImpl (stdoutOpen : Bool) (opts : WorldOptions) (steps : Nat)
    (effectiveSeed : UInt64) : IO Unit := do
  Env.pinClosedStdio
  let report ← runFilesFuzz steps effectiveSeed false opts.dir opts.explicitDir opts.requireNs
  if !report.shrinkSelfTestDetail.isEmpty then
    outPrintln stdoutOpen s!"SELF_TEST_SHRINK: {report.shrinkSelfTestDetail}"
  printAndAssertFilesHits stdoutOpen report.stats steps false (!opts.explicitDir) report.realStats
  outPrintln stdoutOpen s!"FUZZ_SUMMARY suite=files dir={opts.dir} steps={report.totalSteps} episodes={report.totalEpisodes} elapsed_ms={report.elapsedMs} syscalls_per_sec={report.syscallsPerSec}"

private def runPollSuiteImpl (steps : Nat) (effectiveSeed : UInt64) : IO Unit := do
  let fdsBefore ← countSelfFds
  let report ← PollFuzz.runPollFuzz steps effectiveSeed false
  let fdsAfter ← countSelfFds
  if fdsBefore > 0 && fdsAfter > fdsBefore then
    throw (IO.userError s!"poll fuzzer leaked FDs: before={fdsBefore} after={fdsAfter}")
  if !report.shrinkSelfTestDetail.isEmpty then
    IO.println s!"SELF_TEST_SHRINK (poll): {report.shrinkSelfTestDetail}"
  printAndAssertHits "poll" PollFuzz.allSyscallNames report.stats.counts (steps >= 1000) #[4, 9, 22, 24]
  IO.println s!"FUZZ_SUMMARY suite=poll steps={report.totalSteps} episodes={report.totalEpisodes} elapsed_ms={report.elapsedMs} syscalls_per_sec={report.syscallsPerSec}"

private def runNetSuiteImpl (opts : WorldOptions) (steps : Nat) (effectiveSeed : UInt64)
    (outClosed errClosed : Bool) : IO Unit := do
  let childStdout : IO.Process.Stdio := if outClosed then .null else .inherit
  let childStderr : IO.Process.Stdio := if errClosed then .null else .inherit
  if !opts.inNetns && !opts.initNetnsDropCaps then
    let probe ← IO.Process.output { cmd := "unshare", args := #["-Urn", "--", "true"] }
    if probe.exitCode == 0 then
      let exe ← IO.appPath
      let childArgs :=
        #[ "-Urn", "--", exe.toString
         , "--suite", "net"
         , "--steps", toString steps
         , "--seed", toString effectiveSeed
         , "--init-netns-drop-caps"
         ] ++ (if opts.requireNs then #["--require-ns"] else #[])
      let child ← IO.Process.spawn {
        cmd := "unshare"
        args := childArgs
        stdin := .null
        stdout := childStdout
        stderr := childStderr
      }
      let rc ← child.wait
      if rc != 0 then
        throw (IO.userError s!"net fuzz unshare child failed (exit={rc})")
      return ()
    else if opts.requireNs then
      throw (IO.userError s!"net fuzz unshare -Urn unavailable under --require-ns (exit={probe.exitCode}): {probe.stderr.trimAscii.toString}")
  else if opts.initNetnsDropCaps then
    NetFuzz.bringLoopbackUp
    let capProbe ← IO.Process.output {
      cmd := "setpriv"
      args := #["--inh-caps=-net_admin", "--bounding-set=-net_admin", "--", "true"]
    }
    if capProbe.exitCode == 0 then
      let exe ← IO.appPath
      let childArgs :=
        #[ "--inh-caps=-net_admin", "--bounding-set=-net_admin", "--", exe.toString
         , "--suite", "net"
         , "--steps", toString steps
         , "--seed", toString effectiveSeed
         , "--in-netns"
         ] ++ (if opts.requireNs then #["--require-ns"] else #[])
      let child ← IO.Process.spawn {
        cmd := "setpriv"
        args := childArgs
        stdin := .null
        stdout := childStdout
        stderr := childStderr
      }
      let rc ← child.wait
      if rc != 0 then
        throw (IO.userError s!"net fuzz setpriv child failed (exit={rc})")
      return ()
    else
      throw (IO.userError s!"net fuzz setpriv failed under --init-netns-drop-caps (exit={capProbe.exitCode}): {capProbe.stderr.trimAscii.toString}")
  let fdsBefore ← countSelfFds
  let report ← NetFuzz.runNetFuzz steps effectiveSeed false opts.requireNs
  let fdsAfter ← countSelfFds
  if fdsBefore > 0 && fdsAfter > fdsBefore then
    throw (IO.userError s!"net fuzzer leaked FDs: before={fdsBefore} after={fdsAfter}")
  if !report.shrinkSelfTestDetail.isEmpty then
    IO.println s!"SELF_TEST_SHRINK (net): {report.shrinkSelfTestDetail}"
  if !report.usernsDetail.isEmpty then
    IO.println s!"USERNS_PROBE (net): {report.usernsDetail}"
  let reqNetErrs : Array UInt32 := #[4, 9, 22, 24, 32, 90, 93, 94, 95, 98, 101, 104, 111]
  printAndAssertHits "net" NetFuzz.allSyscallNames report.stats.counts (steps >= 5000) reqNetErrs (steps >= 5000)
  IO.println s!"FUZZ_SUMMARY suite=net steps={report.totalSteps} episodes={report.totalEpisodes} elapsed_ms={report.elapsedMs} syscalls_per_sec={report.syscallsPerSec}"

private def runSandboxSuiteImpl (opts : WorldOptions) (steps : Nat) (effectiveSeed : UInt64) : IO Unit := do
  let rc ← SandboxFuzz.runFuzz {
    seed := effectiveSeed
    steps := steps
    selfTestShrink := false
    requireMemfdStrict := opts.requireMemfdStrict
  }
  if rc != 0 then
    throw (IO.userError s!"sandbox fuzz failed (exit={rc})")

private def runProcessSuiteImpl (opts : WorldOptions) (steps : Nat) (effectiveSeed : UInt64) : IO Unit := do
  ProcessEnv.ensureStdio
  let rc ← ProcessFuzz.runFuzz steps effectiveSeed false opts.requireNs
  if rc != 0 then
    throw (IO.userError s!"process fuzz failed (exit={rc})")

private def runFilesShrinkSelfTest (dir : String) (stdoutOpen : Bool) : IO Unit := do
  Env.pinClosedStdio
  let nanos ← IO.monoNanosNow
  let baseDir : System.FilePath := dir
  let rootBase := if (← baseDir.pathExists) then baseDir else System.FilePath.mk "/tmp"
  let tmpDir := rootBase / s!"leanswe-fuzz-files-shrink-{nanos}"
  IO.FS.createDirAll tmpDir
  try
    let detail ← FilesFuzz.runShrinkSelfTest tmpDir
    outPrintln stdoutOpen s!"SELF_TEST_SHRINK: {detail}"
  finally
    if ← tmpDir.pathExists then
      IO.FS.removeDirAll tmpDir

private def runNetShrinkSelfTest : IO Unit := do
  let nanos ← IO.monoNanosNow
  let tmpDir : System.FilePath := s!"/tmp/lswf-net-sh-{nanos % 100000000}"
  IO.FS.createDirAll tmpDir
  try
    let detail ← NetFuzz.runShrinkSelfTest tmpDir
    IO.println s!"SELF_TEST_SHRINK (net): {detail}"
  finally
    if ← tmpDir.pathExists then
      IO.FS.removeDirAll tmpDir

/-- Dispatch internal worker and strace fault-check invocations that bypass standard CLI option parsing. -/
def tryDispatchEarlyWorker (args : List String) : IO (Option UInt32) := do
  match args with
  | "--suite" :: "process" :: "--ns-worker" :: mode :: arg :: rest =>
    ProcessEnv.ensureStdio
    return some (← ProcessFuzz.nsWorkerMain mode arg rest)
  | "--ns-worker" :: mode :: arg :: rest =>
    ProcessEnv.ensureStdio
    return some (← ProcessFuzz.nsWorkerMain mode arg rest)
  | "--sandbox-strace-worker" :: mode :: [] =>
    Fuzz.LinuxSyscall.Sandbox.Strace.runStraceWorker mode
    return some 0
  | "--sandbox-strace-fault-check" :: [] =>
    Fuzz.LinuxSyscall.Sandbox.Strace.runStraceFaultCheck
    IO.println "SANDBOX_STRACE_FAULT_CHECK_OK"
    return some 0
  | "--timerand-strace-fault-check" :: rest =>
    return some (← Fuzz.LinuxSyscall.TimeRand.Strace.probeMain rest)
  | "--poll-strace-fault-check" :: rest =>
    return some (← Fuzz.LinuxSyscall.Poll.Strace.probeMain rest)
  | "--poll-strace-worker" :: rest =>
    return some (← Fuzz.LinuxSyscall.Poll.Strace.probeMain ("--worker" :: rest))
  | "--poll-strace-efd-worker" :: rest =>
    return some (← Fuzz.LinuxSyscall.Poll.Strace.probeMain ("--efd-worker" :: rest))
  | "--net-strace-fault-check" :: rest =>
    return some (← Fuzz.LinuxSyscall.Net.Strace.probeMain rest)
  | "--net-strace-worker" :: rest =>
    return some (← Fuzz.LinuxSyscall.Net.Strace.probeMain ("--worker" :: rest))
  | "--process-strace-fault-check" :: rest =>
    return some (← Fuzz.LinuxSyscall.Process.Strace.probeMain rest)
  | "--process-strace-worker" :: opName :: errName :: _ =>
    return some (← Fuzz.LinuxSyscall.Process.Strace.probeMain ["--worker", opName, errName])
  | "--files-strace-fault-check" :: rest =>
    return some (← Fuzz.LinuxSyscall.Files.Strace.probeMain rest)
  | "--files-strace-worker" :: rest =>
    return some (← Fuzz.LinuxSyscall.Files.Strace.probeMain ("--worker" :: rest))
  | _ => return none

/-- Execute isolated LinuxSyscall worker or fixture-seeding submodes (`--worker-mode`, `--seed-*`, `--env-child`, `--net-userns-worker`, `--poll-seccomp-worker`, `--net-seccomp-worker`, `--init-netns-drop-caps`, `--in-netns`). -/
def runSpecialMode (opts : WorldOptions) (requestedSuites : List String) (steps : Nat)
    (effectiveSeed : UInt64) (hasRandomSeed : Bool) (outClosed errClosed : Bool) : IO UInt32 := do
  let stdoutOpen := !outClosed
  let stderrOpen := !errClosed
  if opts.workerMode?.isSome then
    Env.pinClosedStdio
  if let some (d, k) := opts.seedOverlayLower? then
    seedOverlayLowerDirs d k
    return 0
  if let some d := opts.seedRoTree? then
    seedReadOnlyTree d
    return 0
  if opts.netUsernsWorker then
    if requestedSuites != ["net"] then
      errPrintln stderrOpen "--net-userns-worker requires --suite net"
      return 2
    NetFuzz.runUsernsLoDownProbe steps effectiveSeed
    return 0
  if opts.pollSeccompWorker then
    if requestedSuites != ["poll"] then
      errPrintln stderrOpen "--poll-seccomp-worker requires --suite poll"
      return 2
    PollFuzz.runSeccompWorker opts.seccompErrno
    return 0
  if opts.netSeccompWorker then
    if requestedSuites != ["net"] then
      errPrintln stderrOpen "--net-seccomp-worker requires --suite net"
      return 2
    NetFuzz.runSeccompWorker opts.seccompErrno
    return 0
  if opts.initNetnsDropCaps || opts.inNetns then
    if requestedSuites != ["net"] then
      errPrintln stderrOpen "--init-netns-drop-caps / --in-netns requires --suite net"
      return 2
    runNetSuiteImpl opts steps effectiveSeed outClosed errClosed
    return 0
  if let some envChild := opts.envChild? then
    if requestedSuites != ["timerand"] then
      errPrintln stderrOpen "--env-child is only supported for --suite timerand"
      return 2
    if hasRandomSeed then
      outPrintln stdoutOpen s!"SEED={effectiveSeed}"
    match envChild with
    | "seccomp" =>
      let _ ← fuzzTimeRandSeccompChild steps effectiveSeed opts.seccompErrno opts.seccompMask opts.seccompDelaySteps
      return 0
    | "timens" =>
      let _ ← fuzzTimeRand steps effectiveSeed (runEnvSubEpisodes := false) (allowNoTimens := opts.allowNoTimens)
      return 0
    | other =>
      errPrintln stderrOpen s!"UNKNOWN_ENV_CHILD: {other}"
      return 2
  if let some wm := opts.workerMode? then
    if !["rw", "ro_bind", "chroot", "seccomp", "unlinked_cwd"].contains wm then
      errPrintln stderrOpen s!"unsupported --worker-mode '{wm}', expected 'rw', 'ro_bind', 'chroot', 'seccomp', or 'unlinked_cwd'"
      return 2
    let crossP := opts.crossDir?.map System.FilePath.mk
    let chrootP := opts.chrootDir?.map System.FilePath.mk
    let isRo := wm == "ro_bind"
    let isSeccomp := wm == "seccomp"
    let isUnlinkedCwd := wm == "unlinked_cwd"
    let allowAutoCross := opts.crossDir?.isNone && wm != "chroot"
    if opts.closeFd0 && (← Env.fdKind 0) != 6 then
      let _ ← Env.closeRawFd 0
    let rep ← runFilesFuzzOnDir steps effectiveSeed false opts.dir crossP isRo chrootP
      opts.hostProtected allowAutoCross isSeccomp isUnlinkedCwd opts.preseededEps opts.rlimitNofile?
    outPrintln stdoutOpen (formatWorkerStats rep)
    if opts.assertWorkerHits then
      if let some lim := opts.rlimitNofile? then
        if lim <= 3 then
          if rep.stats.counts.getD "dupStdio:err(22)" 0 == 0 ||
              rep.stats.counts.getD "openat:err(24)" 0 == 0 then
            throw (IO.userError s!"rlimit_nofile<=3 worker missing EINVAL/EMFILE hits (dupStdio:err(22)={rep.stats.counts.getD "dupStdio:err(22)" 0}, openat:err(24)={rep.stats.counts.getD "openat:err(24)" 0})")
        else if lim == 4 then
          if rep.stats.counts.getD "openat:err(24)" 0 == 0 ||
              rep.stats.counts.getD "dupStdio:err(24)" 0 == 0 ||
              rep.stats.counts.getD "reopenReadOnly:err(24)" 0 == 0 then
            throw (IO.userError s!"rlimit_nofile=4 worker missing EMFILE hits (openat:err(24)={rep.stats.counts.getD "openat:err(24)" 0}, dupStdio:err(24)={rep.stats.counts.getD "dupStdio:err(24)" 0}, reopenReadOnly:err(24)={rep.stats.counts.getD "reopenReadOnly:err(24)" 0})")
        else
          printAndAssertFilesHits stdoutOpen rep.stats steps isRo (opts.preseededEps && !isUnlinkedCwd && !isSeccomp) rep.realStats
      else
        printAndAssertFilesHits stdoutOpen rep.stats steps isRo (opts.preseededEps && !isUnlinkedCwd && !isSeccomp) rep.realStats
    return 0
  return 2

/-- Construct the six unified `LinuxSyscall` world-model `FuzzSuite` descriptors (`sandbox`, `timerand`, `files`, `process`, `poll`, `net`). -/
def suites (opts : WorldOptions) (outClosed errClosed : Bool) : List FuzzSuite :=
  let stdoutOpen := !outClosed
  [ { name := "sandbox"
      description := "LinuxSyscall.Sandbox world-model differential fuzzer (Landlock, seccomp, prctl, setrlimit, memfd)"
      runSmoke := fun cfg => do
        Fuzz.LinuxSyscall.Sandbox.Strace.runChecks
        runSandboxSuiteImpl opts (min cfg.steps 2000) cfg.seed
      runFuzz := fun cfg => runSandboxSuiteImpl opts cfg.steps cfg.seed
      selfTestShrink := fun seed => SandboxFuzz.runShrinkSelfTest seed }
  , { name := "timerand"
      description := "LinuxSyscall.TimeRand world-model differential fuzzer (clock_gettime, clock_nanosleep, getrandom)"
      runSmoke := fun cfg => do
        Fuzz.LinuxSyscall.TimeRand.Strace.runChecks
        let allowNoTm := opts.allowNoTimens || !opts.requireNs
        let _ ← fuzzTimeRand (min cfg.steps 1000) cfg.seed (runEnvSubEpisodes := true) (allowNoTimens := allowNoTm)
      runFuzz := fun cfg => do
        let _ ← fuzzTimeRand cfg.steps cfg.seed (runEnvSubEpisodes := true) (allowNoTimens := opts.allowNoTimens)
      selfTestShrink := fun seed => selfTestShrink seed }
  , { name := "files"
      description := "LinuxSyscall.Files world-model differential fuzzer (23 POSIX file syscalls across FS/mount/seccomp worlds)"
      runSmoke := fun cfg => do
        Fuzz.LinuxSyscall.Files.Strace.runChecks
        let smokeSteps := if opts.requireNs then 2000 else min cfg.steps 1500
        runFilesSuiteImpl stdoutOpen opts smokeSteps cfg.seed
      runFuzz := fun cfg => runFilesSuiteImpl stdoutOpen opts cfg.steps cfg.seed
      selfTestShrink := fun _ => runFilesShrinkSelfTest opts.dir stdoutOpen }
  , { name := "process"
      description := "LinuxSyscall.Process world-model differential fuzzer (pipe2, waitpid, kill, pidfd_open, pidfd_send_signal)"
      runSmoke := fun cfg => do
        ProcessEnv.ensureStdio
        Fuzz.LinuxSyscall.Process.Strace.runChecks
        runProcessSuiteImpl opts (min cfg.steps 1500) cfg.seed
      runFuzz := fun cfg => runProcessSuiteImpl opts cfg.steps cfg.seed
      selfTestShrink := fun _ => ProcessFuzz.runShrinkSelfTest }
  , { name := "poll"
      description := "LinuxSyscall.Poll world-model differential fuzzer (ppoll, eventfd2)"
      runSmoke := fun cfg => do
        Fuzz.LinuxSyscall.Poll.Strace.runChecks
        runPollSuiteImpl (min cfg.steps 4000) cfg.seed
      runFuzz := fun cfg => runPollSuiteImpl cfg.steps cfg.seed
      selfTestShrink := fun _ => do
        let detail ← PollFuzz.runShrinkSelfTest
        IO.println s!"SELF_TEST_SHRINK (poll): {detail}" }
  , { name := "net"
      description := "LinuxSyscall.Net world-model differential fuzzer (15 Linux socket/SCM_RIGHTS/ioctl syscalls)"
      runSmoke := fun cfg => do
        Fuzz.LinuxSyscall.Net.Strace.runChecks
        runNetSuiteImpl opts (min cfg.steps 2000) cfg.seed outClosed errClosed
      runFuzz := fun cfg => runNetSuiteImpl opts cfg.steps cfg.seed outClosed errClosed
      selfTestShrink := fun _ => runNetShrinkSelfTest }
  ]

end Fuzz.LinuxSyscall.Main
