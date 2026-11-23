import Aeneas

open Aeneas Aeneas.Std Result

namespace LeanSwe.ProcessSandbox.Init.World

/-- Raw byte sequence representing CLI tokens, plan payloads, or status frames. -/
abbrev Bytes := List Std.U8

/-- One oracle outcome for a `read(fd, buf, 1)` (`init_sys.read1`) call. -/
inductive Read1Outcome where
  /-- End-of-file (`Ok 0`). -/
  | eof
  /-- Single byte read (`Ok 1`, copying `value` into `buf[0]`). -/
  | byte (value : Std.U8)
  /-- Syscall failure returning positive Linux `errno` (`1..4095`). -/
  | err (errno : Std.I32)
  deriving DecidableEq, Repr, Inhabited

/-- One oracle outcome for an `fstat`-based `init_sys.fd_is_dir` call. -/
inductive FdIsDirOutcome where
  /-- Descriptor refers to a directory (`S_ISDIR`). -/
  | dir
  /-- Descriptor refers to a non-directory (regular file or device node). -/
  | regular
  /-- `fstat` failure returning positive Linux `errno` (`1..4095`). -/
  | err (errno : Std.I32)
  deriving DecidableEq, Repr, Inhabited

/-- One oracle outcome for an `SCM_RIGHTS` `init_sys.sendmsg_scm_batch` call. -/
inductive ScmSendOutcome where
  /-- Successful `sendmsg` returning `sent` bytes (`0` triggers `EIO`). -/
  | ok (sent : Std.Usize)
  /-- Failed `sendmsg` returning positive Linux `errno` (`1..4095`). -/
  | err (errno : Std.I32)
  deriving DecidableEq, Repr, Inhabited

/-- Oracle outcome for a `fork()` (`init_sys.fork_proc`) call. -/
inductive ForkOutcome where
  /-- Child side of `fork()` returning `0`. -/
  | child
  /-- Parent side returning positive child PID (clamped to `2` if `<= 0`). -/
  | parent (childPid : Std.I32)
  /-- Failed `fork()` returning positive Linux `errno` (`1..4095`). -/
  | err (errno : Std.I32)
  deriving DecidableEq, Repr, Inhabited

/-- One oracle outcome for a blocking `waitpid` (`init_sys.waitpid_blocking`) call. -/
inductive WaitpidOutcome where
  /-- Reaped `pid` with raw Linux wait status word `wstatus`. -/
  | reaped (pid wstatus : Std.I32)
  /-- Failed `waitpid` returning positive Linux `errno` (`1..4095`). -/
  | err (errno : Std.I32)
  deriving DecidableEq, Repr, Inhabited

/-- Syscall path that successfully installed a classic BPF seccomp filter. -/
inductive SeccompBackend where
  /-- Installed directly via `syscall(SYS_seccomp, SECCOMP_SET_MODE_FILTER, ...)`. -/
  | syscall
  /-- Installed via `prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, ...)` fallback. -/
  | prctl
  deriving DecidableEq, Repr, Inhabited

/-- Pure state of an owned `PlanBuf` buffer in `psandbox_init::init_sys`. -/
structure PlanBufState where
  /-- Current accumulated plan bytes. -/
  bytes : Bytes := []
  /-- Current allocated byte capacity. -/
  cap : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Pure state of a pre-fork `ExecTable` table in `psandbox_init::init_sys`. -/
structure ExecTableState where
  /-- Expected `argc` count (`argv[1..=argc]`). -/
  argc : Std.U32 := 0#u32
  /-- Expected `envc` count (`envp[0..envc]`). -/
  envc : Std.U32 := 0#u32
  /-- Stored guest `program` (`argv[0]`). -/
  program : Bytes := []
  /-- Stored guest working directory `cwd`. -/
  cwd : Bytes := []
  /-- Stored guest argument entries `(idx, bytes)`. -/
  args : List (Std.U32 × Bytes) := []
  /-- Stored guest environment entries `(idx, key, val)`. -/
  env : List (Std.U32 × Bytes × Bytes) := []
  deriving DecidableEq, Repr, Inhabited

/-- Pure single-process state modeled across `psandbox_init::init_sys` calls. -/
structure InitState where
  /-- Command-line argument vector `argv[0..argc]`. -/
  cliArgs : List Bytes := []
  /-- Remaining unread bytes on `plan_fd`. -/
  planStream : Bytes := []
  /-- Current loopback interface flags (`SIOCGIFFLAGS`). -/
  loFlags : Std.I16 := 0#i16
  /-- Kernel Landlock ABI version (`>= 4` on supported hosts). -/
  landlockAbi : Std.I32 := 4#i32
  /-- Finite oracle queue for `bind_loopback_v4` (`none` = ok, `some e` = errno). -/
  bindOracle : List (Option Std.I32) := []
  /-- Finite oracle queue for `listen_socket` (`none` = ok, `some e` = errno). -/
  listenOracle : List (Option Std.I32) := []
  /-- Ports accepted by succeeding `bind_loopback_v4` calls (including `0`). -/
  boundPorts : List Std.U16 := []
  /-- Finite oracle queue for `read1` (`[]` defaults to EOF `0`). -/
  read1Oracle : List Read1Outcome := []
  /-- Finite oracle queue for `fd_is_dir` (`[]` defaults to `.dir`). -/
  fdIsDirOracle : List FdIsDirOutcome := []
  /-- Recorded `(rulesetFd, parentFd, access)` rules added via Landlock. -/
  landlockPathRules : List (Std.I32 × Std.I32 × Std.U64) := []
  /-- Finite oracle queue for `sendmsg_scm_batch` (`[]` defaults to `Ok 1`). -/
  scmSendOracle : List ScmSendOutcome := []
  /-- Recorded `(ctrlFd, start, batch)` chunks sent via `sendmsg_scm_batch`. -/
  scmSentBatches : List (Std.I32 × Std.Usize × Std.Usize) := []
  /-- Optional forced `errno` returned by `seccomp_set_mode_filter`. -/
  seccompErr? : Option Std.I32 := none
  /-- Optional forced `errno` returned by `prctl_set_seccomp_filter`. -/
  prctlSeccompErr? : Option Std.I32 := none
  /-- Recorded `(backend, insnCount)` seccomp filter installations. -/
  seccompInstalled : List (SeccompBackend × Std.U32) := []
  /-- Outcome returned by `fork_proc` (`child`, `parent pid`, or `err`). -/
  forkOutcome : ForkOutcome := .parent 2#i32
  /-- Finite oracle queue for `waitpid_blocking`. -/
  waitpidOracle : List WaitpidOutcome := []
  /-- Recorded `(pid, wstatus)` pairs reaped via `waitpid_blocking`. -/
  reapedPids : List (Std.I32 × Std.I32) := []
  /-- Recorded `(fd, bytes)` writes issued via `write_fd`. -/
  writes : List (Std.I32 × Bytes) := []
  /-- Recorded descriptors closed via `close_fd`. -/
  closedFds : List Std.I32 := []
  /-- Optional terminal `_exit` code if `exit_now` was invoked. -/
  exitCode? : Option Std.I32 := none
  deriving DecidableEq, Repr, Inhabited

end LeanSwe.ProcessSandbox.Init.World

/-- `psandbox_init::init_sys::Sys`: container `psandbox-init` OS state. -/
abbrev init_sys.Sys : Type := LeanSwe.ProcessSandbox.Init.World.InitState

/-- `psandbox_init::init_sys::PlanBuf`: owned `LSWP0002` byte buffer. -/
abbrev init_sys.PlanBuf : Type := LeanSwe.ProcessSandbox.Init.World.PlanBufState

/-- `psandbox_init::init_sys::ExecTable`: pre-fork guest `argv`/`envp` table. -/
abbrev init_sys.ExecTable : Type := LeanSwe.ProcessSandbox.Init.World.ExecTableState
