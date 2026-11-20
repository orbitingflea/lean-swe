import LeanSwe.Fs.Raw.Interface
import LeanSwe.LinuxSyscall.Fuzz.SandboxFuzz
import LeanSwe.LinuxSyscall.Fuzz.TimeRandFuzz
import LeanSwe.LinuxSyscall.Fuzz.PollFuzz
import LeanSwe.LinuxSyscall.Fuzz.NetFuzz

namespace LeanSwe.LinuxSyscall.Fuzz.Main

open LeanSwe.LinuxSyscall.Fuzz

/-- CLI options for `leanswe-world-fuzz`. -/
structure FuzzCliOpts where
  /-- Selected fuzz suite (`sandbox`, `timerand`, `poll`, `net`, or `all`). -/
  suite : String := "sandbox"
  /-- Number of syscall steps to execute. -/
  steps : Nat := 1000000
  /-- Initial 64-bit SplitMix64 seed. -/
  seed : UInt64 := 0x517cc1b727220a95
  /-- Draw initial seed from OS entropy (`TimeRand.getrandom`) and print `SEED=<u64>`. -/
  randomSeed : Bool := false
  /-- Whether to run the delta-shrinker self-test before fuzzing. -/
  selfTestShrink : Bool := false
  /-- Require `vm.memfd_noexec=2` strict assertions in the `sandbox` suite. -/
  requireMemfdStrict : Bool := false
  /-- Allow skipping `CLONE_NEWTIME` (`timens`) sub-episodes when unshare is unavailable. -/
  allowNoTimens : Bool := false
  /-- Optional child-environment mode (`seccomp` or `timens`) used internally for forked sub-episodes. -/
  envChild? : Option String := none
  /-- Optional `errno` value (`1..4095`) for `--env-child seccomp`. -/
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
  /-- Require unprivileged user+net namespace probes to run instead of skipping. -/
  requireNs : Bool := false
  deriving Repr

private def parsePositiveNatArg (flag val : String) : Except String Nat :=
  match val.toNat? with
  | some n =>
    if n > 0 then .ok n else .error s!"INVALID_{flag}: expected >= 1, got '{val}'"
  | none => .error s!"INVALID_{flag}: expected Nat, got '{val}'"

private def parseNatArg (flag val : String) : Except String Nat :=
  match val.toNat? with
  | some n => .ok n
  | none => .error s!"INVALID_{flag}: expected Nat, got '{val}'"

private def parseUInt64Arg (flag val : String) : Except String UInt64 :=
  match val.toNat? with
  | some n =>
    if n < UInt64.size then
      .ok (UInt64.ofNat n)
    else
      .error s!"INVALID_{flag}: out of UInt64 range, got '{val}'"
  | none => .error s!"INVALID_{flag}: expected UInt64, got '{val}'"

private def parseCliArgs : List String → (opts : FuzzCliOpts := {}) → Except String FuzzCliOpts
  | [], opts => .ok opts
  | ["--suite"], _ => .error "missing value for --suite"
  | "--suite" :: s :: rest, opts =>
    parseCliArgs rest { opts with suite := s }
  | ["--steps"], _ => .error "missing value for --steps"
  | "--steps" :: s :: rest, opts => do
    let n ← parsePositiveNatArg "STEPS" s
    parseCliArgs rest { opts with steps := n }
  | ["--seed"], _ => .error "missing value for --seed"
  | "--seed" :: s :: rest, opts => do
    let sd ← parseUInt64Arg "SEED" s
    parseCliArgs rest { opts with seed := sd, randomSeed := false }
  | "--random-seed" :: rest, opts =>
    parseCliArgs rest { opts with randomSeed := true }
  | "--self-test-shrink" :: rest, opts =>
    parseCliArgs rest { opts with selfTestShrink := true }
  | "--require-memfd-strict" :: rest, opts =>
    parseCliArgs rest { opts with requireMemfdStrict := true }
  | "--allow-no-timens" :: rest, opts =>
    parseCliArgs rest { opts with allowNoTimens := true }
  | "--net-userns-worker" :: rest, opts =>
    parseCliArgs rest { opts with netUsernsWorker := true }
  | "--poll-seccomp-worker" :: rest, opts =>
    parseCliArgs rest { opts with pollSeccompWorker := true }
  | "--net-seccomp-worker" :: rest, opts =>
    parseCliArgs rest { opts with netSeccompWorker := true }
  | "--init-netns-drop-caps" :: rest, opts =>
    parseCliArgs rest { opts with initNetnsDropCaps := true }
  | "--in-netns" :: rest, opts =>
    parseCliArgs rest { opts with inNetns := true }
  | "--require-ns" :: rest, opts =>
    parseCliArgs rest { opts with requireNs := true }
  | ["--env-child"], _ => .error "missing value for --env-child"
  | "--env-child" :: mode :: rest, opts =>
    parseCliArgs rest { opts with envChild? := some mode }
  | ["--seccomp-errno"], _ => .error "missing value for --seccomp-errno"
  | "--seccomp-errno" :: s :: rest, opts => do
    let n ← parseNatArg "SECCOMP_ERRNO" s
    if n == 0 || n > 4095 then
      .error s!"INVALID_SECCOMP_ERRNO: expected 1..4095, got '{s}'"
    else
      parseCliArgs rest { opts with seccompErrno := UInt32.ofNat n }
  | ["--seccomp-mask"], _ => .error "missing value for --seccomp-mask"
  | "--seccomp-mask" :: s :: rest, opts => do
    let n ← parseNatArg "SECCOMP_MASK" s
    if n == 0 || n > 7 then
      .error s!"INVALID_SECCOMP_MASK: expected 1..7, got '{s}'"
    else
      parseCliArgs rest { opts with seccompMask := UInt32.ofNat n }
  | ["--seccomp-delay-steps"], _ => .error "missing value for --seccomp-delay-steps"
  | "--seccomp-delay-steps" :: s :: rest, opts => do
    let n ← parseNatArg "SECCOMP_DELAY_STEPS" s
    parseCliArgs rest { opts with seccompDelaySteps := n }
  | flag :: _, _ => .error s!"UNKNOWN_FLAG: {flag}"

private def drawOsEntropySeed : IO UInt64 := do
  let mut acc : Array UInt8 := #[]
  for _ in List.range 16 do
    if acc.size ≥ 8 then
      break
    match ← LeanSwe.LinuxSyscall.TimeRand.getrandom (UInt32.ofNat (8 - acc.size)) {} with
    | .ok bs =>
      for b in bs.data do
        acc := acc.push b
    | .error e =>
      if e != LeanSwe.LinuxSyscall.Errno.EINTR then
        throw (IO.userError s!"drawOsEntropySeed getrandom failed: {e}")
  if acc.size < 8 then
    throw (IO.userError s!"drawOsEntropySeed short read: got {acc.size} bytes")
  let mut v : UInt64 := 0
  for i in List.range 8 do
    v := v ||| (UInt64.ofNat acc[i]!.toNat <<< UInt64.ofNat (8 * i))
  return v

private def runTimerandSuite (opts : FuzzCliOpts) (effectiveSeed : UInt64) : IO UInt32 := do
  if opts.selfTestShrink then
    selfTestShrink effectiveSeed
  match opts.envChild? with
  | some "seccomp" =>
    let _ ← fuzzTimeRandSeccompChild opts.steps effectiveSeed opts.seccompErrno opts.seccompMask opts.seccompDelaySteps
    return 0
  | some "timens" =>
    let _ ← fuzzTimeRand opts.steps effectiveSeed (runEnvSubEpisodes := false) (allowNoTimens := opts.allowNoTimens)
    return 0
  | some other =>
    IO.eprintln s!"UNKNOWN_ENV_CHILD: {other}"
    return 2
  | none =>
    let _ ← fuzzTimeRand opts.steps effectiveSeed (runEnvSubEpisodes := true) (allowNoTimens := opts.allowNoTimens)
    return 0

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

private def runPollSuite (opts : FuzzCliOpts) (effectiveSeed : UInt64) : IO Unit := do
  let fdsBefore ← countSelfFds
  let report ← PollFuzz.runPollFuzz opts.steps effectiveSeed opts.selfTestShrink
  let fdsAfter ← countSelfFds
  if fdsBefore > 0 && fdsAfter > fdsBefore then
    throw (IO.userError s!"poll fuzzer leaked FDs: before={fdsBefore} after={fdsAfter}")
  if !report.shrinkSelfTestDetail.isEmpty then
    IO.println s!"SELF_TEST_SHRINK (poll): {report.shrinkSelfTestDetail}"
  printAndAssertHits "poll" PollFuzz.allSyscallNames report.stats.counts (opts.steps >= 1000) #[4, 9, 22, 24]
  IO.println s!"FUZZ_SUMMARY suite=poll steps={report.totalSteps} episodes={report.totalEpisodes} elapsed_ms={report.elapsedMs} syscalls_per_sec={report.syscallsPerSec}"

private def nullOutStream : IO.FS.Stream where
  flush := pure ()
  read _ := pure ByteArray.empty
  write _ := pure ()
  getLine := pure ""
  putStr _ := pure ()
  isTty := pure false

private def isStdioFdClosedOrUv (fd : Nat) : IO Bool := do
  match ← LeanSwe.Fs.Raw.defaultOps.readLink s!"/proc/self/fd/{fd}" with
  | .error _ => return true
  | .ok tgt =>
    return tgt.startsWith "anon_inode:[event" || tgt.startsWith "anon_inode:[io_uring"

private def sanitizeClosedStdio : IO (Bool × Bool) := do
  let outClosed ← isStdioFdClosedOrUv 1
  let errClosed ← isStdioFdClosedOrUv 2
  if outClosed then
    let _ ← IO.setStdout nullOutStream
  if errClosed then
    let _ ← IO.setStderr nullOutStream
  return (outClosed, errClosed)

private def runNetSuite (opts : FuzzCliOpts) (effectiveSeed : UInt64)
    (outClosed : Bool := false) (errClosed : Bool := false) : IO Unit := do
  let childStdout : IO.Process.Stdio := if outClosed then .null else .inherit
  let childStderr : IO.Process.Stdio := if errClosed then .null else .inherit
  if !opts.inNetns && !opts.initNetnsDropCaps then
    let probe ← IO.Process.output { cmd := "unshare", args := #["-Urn", "--", "true"] }
    if probe.exitCode == 0 then
      let exe ← IO.appPath
      let childArgs :=
        #[ "-Urn", "--", exe.toString
         , "--suite", "net"
         , "--steps", toString opts.steps
         , "--seed", toString effectiveSeed
         , "--init-netns-drop-caps"
         ] ++ (if opts.selfTestShrink then #["--self-test-shrink"] else #[])
           ++ (if opts.requireNs then #["--require-ns"] else #[])
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
         , "--steps", toString opts.steps
         , "--seed", toString effectiveSeed
         , "--in-netns"
         ] ++ (if opts.selfTestShrink then #["--self-test-shrink"] else #[])
           ++ (if opts.requireNs then #["--require-ns"] else #[])
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
  let report ← NetFuzz.runNetFuzz opts.steps effectiveSeed opts.selfTestShrink opts.requireNs
  let fdsAfter ← countSelfFds
  if fdsBefore > 0 && fdsAfter > fdsBefore then
    throw (IO.userError s!"net fuzzer leaked FDs: before={fdsBefore} after={fdsAfter}")
  if !report.shrinkSelfTestDetail.isEmpty then
    IO.println s!"SELF_TEST_SHRINK (net): {report.shrinkSelfTestDetail}"
  if !report.usernsDetail.isEmpty then
    IO.println s!"USERNS_PROBE (net): {report.usernsDetail}"
  let reqNetErrs : Array UInt32 := #[4, 9, 22, 24, 32, 90, 93, 94, 95, 98, 101, 104, 111]
  printAndAssertHits "net" NetFuzz.allSyscallNames report.stats.counts (opts.steps >= 5000) reqNetErrs (opts.steps >= 5000)
  IO.println s!"FUZZ_SUMMARY suite=net steps={report.totalSteps} episodes={report.totalEpisodes} elapsed_ms={report.elapsedMs} syscalls_per_sec={report.syscallsPerSec}"

/-- CLI entrypoint for `leanswe-world-fuzz`. -/
def main (args : List String) : IO UInt32 := do
  let (outClosed, errClosed) ← sanitizeClosedStdio
  let opts ← match parseCliArgs args with
    | .ok o => pure o
    | .error msg =>
      IO.eprintln msg
      return 2
  if opts.suite != "sandbox" && opts.suite != "timerand" && opts.suite != "poll" && opts.suite != "net" && opts.suite != "all" then
    IO.eprintln s!"UNKNOWN_SUITE: {opts.suite} (expected sandbox, timerand, poll, net, or all)"
    return 2
  let effectiveSeed ←
    if opts.randomSeed then drawOsEntropySeed else pure opts.seed
  if opts.netUsernsWorker then
    if opts.suite != "net" then
      IO.eprintln "--net-userns-worker requires --suite net"
      return 2
    NetFuzz.runUsernsLoDownProbe opts.steps effectiveSeed
    return 0
  if opts.pollSeccompWorker then
    if opts.suite != "poll" then
      IO.eprintln "--poll-seccomp-worker requires --suite poll"
      return 2
    PollFuzz.runSeccompWorker opts.seccompErrno
    return 0
  if opts.netSeccompWorker then
    if opts.suite != "net" then
      IO.eprintln "--net-seccomp-worker requires --suite net"
      return 2
    NetFuzz.runSeccompWorker opts.seccompErrno
    return 0
  if (opts.envChild?.isNone || opts.randomSeed) && !opts.inNetns && !opts.initNetnsDropCaps then
    IO.println s!"SEED={effectiveSeed}"
  match opts.suite with
  | "sandbox" =>
    if opts.envChild?.isSome then
      IO.eprintln "--env-child is only supported for --suite timerand"
      return 2
    SandboxFuzz.runFuzz {
      seed := effectiveSeed
      steps := opts.steps
      selfTestShrink := opts.selfTestShrink
      requireMemfdStrict := opts.requireMemfdStrict
    }
  | "timerand" =>
    runTimerandSuite opts effectiveSeed
  | "poll" =>
    if opts.envChild?.isSome then
      IO.eprintln "--env-child is only supported for --suite timerand"
      return 2
    runPollSuite opts effectiveSeed
    return 0
  | "net" =>
    if opts.envChild?.isSome then
      IO.eprintln "--env-child is only supported for --suite timerand"
      return 2
    runNetSuite opts effectiveSeed outClosed errClosed
    return 0
  | _ =>
    if opts.envChild?.isSome then
      IO.eprintln "--env-child is only supported for --suite timerand"
      return 2
    let rc ← SandboxFuzz.runFuzz {
      seed := effectiveSeed
      steps := opts.steps
      selfTestShrink := opts.selfTestShrink
      requireMemfdStrict := opts.requireMemfdStrict
    }
    if rc != 0 then
      return rc
    let rc2 ← runTimerandSuite opts effectiveSeed
    if rc2 != 0 then
      return rc2
    runPollSuite opts effectiveSeed
    runNetSuite opts effectiveSeed outClosed errClosed
    return 0

end LeanSwe.LinuxSyscall.Fuzz.Main
