import Aeneas
import LeanSwe.ProcessSandbox.Init.Aeneas.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open psandbox_init
open LeanSwe.ProcessSandbox.Init.World

namespace LeanSwe.ProcessSandbox.Init.World

/-- Linux `EINTR` (`4`). -/
def EINTR : Std.I32 := 4#i32

/-- Linux `EIO` (`5`). -/
def EIO : Std.I32 := 5#i32

/-- Linux `EBADF` (`9`). -/
def EBADF : Std.I32 := 9#i32

/-- Linux `ECHILD` (`10`). -/
def ECHILD : Std.I32 := 10#i32

/-- Linux `EAGAIN` (`11`). -/
def EAGAIN : Std.I32 := 11#i32

/-- Linux `EINVAL` (`22`). -/
def EINVAL : Std.I32 := 22#i32

/-- Linux `EPIPE` (`32`). -/
def EPIPE : Std.I32 := 32#i32

/-- Linux `ENOSYS` (`38`). -/
def ENOSYS : Std.I32 := 38#i32

/-- Linux `EADDRINUSE` (`98`). -/
def EADDRINUSE : Std.I32 := 98#i32

/-- Clamp an oracle-supplied `errno` into Linux's kernel error range `1..4095`. -/
def sanitizeErrno (e : Std.I32) : Std.I32 :=
  if 1#i32 ≤ e && e ≤ 4095#i32 then e else EIO

/-- Construct a `Std.Usize` from `n` modulo `2^numBits`. -/
def mkUsize (n : Nat) : Std.Usize := ⟨BitVec.ofNat UScalarTy.Usize.numBits n⟩

/-- Pad or truncate `bs` to exact length `n` with trailing `0#u8` bytes. -/
def padBytesTo (n : Nat) (bs : Bytes) : Bytes :=
  let pre := bs.take n
  pre ++ List.replicate (n - pre.length) 0#u8

end LeanSwe.ProcessSandbox.Init.World

/-- Copy `s.cliArgs[idx]?` into `buf` when `len <= 64`, returning `len`, `0` if
missing, or sentinel `65` when `len > 64`. -/
def init_sys.read_cli_arg (s : init_sys.Sys) (idx : Std.Usize)
    (buf : Array Std.U8 64#usize) :
    Result (Std.Usize × init_sys.Sys × Array Std.U8 64#usize) :=
  match s.cliArgs[idx.val]? with
  | none => ok (0#usize, s, buf)
  | some arg =>
    if arg.length <= 64 then
      let padded := padBytesTo 64 arg
      have hVal64 : (64#usize).val = 64 := by decide
      have hLen : padded.length = (64#usize).val := by
        rw [hVal64]
        simp only [padded, padBytesTo, List.length_append,
          List.length_replicate, List.length_take]
        omega
      let arr : Array Std.U8 64#usize := Array.from padded hLen
      ok (mkUsize arg.length, s, arr)
    else
      ok (65#usize, s, buf)

/-- `fcntl(fd, F_GETFD, 0)` model. -/
def init_sys.fcntl_getfd (s : init_sys.Sys) (fd : Std.I32) :
    Result (core.result.Result Std.I32 Std.I32 × init_sys.Sys) :=
  if fd.val < 0 then ok (.Err EBADF, s) else ok (.Ok 0#i32, s)

/-- `fcntl(fd, F_SETFD, flags)` model. -/
def init_sys.fcntl_setfd (s : init_sys.Sys) (fd _flags : Std.I32) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  if fd.val < 0 then ok (.Err EBADF, s) else ok (.Ok (), s)

/-- `close(fd)` model. -/
def init_sys.close_fd (s : init_sys.Sys) (fd : Std.I32) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  if fd.val < 0 then
    ok (.Err EBADF, s)
  else
    ok (.Ok (), { s with closedFds := s.closedFds ++ [fd] })

/-- `read(fd, buf, 1)` model parameterized by `s.read1Oracle` (`[]` defaults to EOF). -/
def init_sys.read1 (s : init_sys.Sys) (fd : Std.I32)
    (buf : Array Std.U8 1#usize) :
    Result (core.result.Result Std.Usize Std.I32 × init_sys.Sys ×
      Array Std.U8 1#usize) :=
  if fd.val < 0 then
    ok (.Err EBADF, s, buf)
  else
    match s.read1Oracle with
    | [] => ok (.Ok 0#usize, s, buf)
    | .eof :: rest => ok (.Ok 0#usize, { s with read1Oracle := rest }, buf)
    | .byte b :: rest =>
      ok (.Ok 1#usize, { s with read1Oracle := rest }, Array.make 1#usize [b])
    | .err e :: rest =>
      ok (.Err (sanitizeErrno e), { s with read1Oracle := rest }, buf)

/-- `read(fd, &mut buf[off..8])` model returning `EOF` (`0`). -/
def init_sys.read_status_tail (s : init_sys.Sys) (fd : Std.I32)
    (buf : Array Std.U8 8#usize) (_off : Std.Usize) :
    Result (core.result.Result Std.Usize Std.I32 × init_sys.Sys ×
      Array Std.U8 8#usize) :=
  if fd.val < 0 then ok (.Err EBADF, s, buf) else ok (.Ok 0#usize, s, buf)

/-- `write(fd, buf, buf.len())` model appending `buf.val` to `s.writes`. -/
def init_sys.write_fd (s : init_sys.Sys) (fd : Std.I32) (buf : Slice Std.U8) :
    Result (core.result.Result Std.Usize Std.I32 × init_sys.Sys) :=
  if fd.val < 0 then
    ok (.Err EBADF, s)
  else
    ok (.Ok buf.len, { s with writes := s.writes ++ [(fd, buf.val)] })

/-- Allocate a `PlanBuf` with initial capacity `cap`. -/
def init_sys.plan_buf_new (s : init_sys.Sys) (cap : Std.Usize) :
    Result (core.result.Result init_sys.PlanBuf Std.I32 × init_sys.Sys) :=
  ok (.Ok { bytes := [], cap := Nat.max 1 cap.val }, s)

/-- Grow `buf.cap` to `newCap`. -/
def init_sys.plan_buf_reserve (s : init_sys.Sys) (buf : init_sys.PlanBuf)
    (newCap : Std.Usize) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys × init_sys.PlanBuf) :=
  ok (.Ok (), s, { buf with cap := Nat.max buf.cap newCap.val })

/-- Read up to `buf.cap - buf.bytes.length` bytes from `s.planStream` into `buf`. -/
def init_sys.plan_buf_read_once (s : init_sys.Sys) (fd : Std.I32)
    (buf : init_sys.PlanBuf) :
    Result (core.result.Result Std.Usize Std.I32 × init_sys.Sys × init_sys.PlanBuf) :=
  if fd.val < 0 then
    ok (.Err EBADF, s, buf)
  else
    let space := buf.cap - buf.bytes.length
    let chunk := s.planStream.take space
    let rest := s.planStream.drop space
    let buf' : PlanBufState := { buf with bytes := buf.bytes ++ chunk }
    ok (.Ok (mkUsize chunk.length), { s with planStream := rest }, buf')

/-- Current length of `buf` when `< UScalar.max .Usize`. -/
def init_sys.plan_buf_len (buf : init_sys.PlanBuf) : Result Std.Usize :=
  ok (mkUsize buf.bytes.length)

/-- Current capacity of `buf`. -/
def init_sys.plan_buf_cap (buf : init_sys.PlanBuf) : Result Std.Usize :=
  ok (mkUsize buf.cap)

/-- Borrow `buf.bytes` as a `Slice Std.U8` when within `Usize` bounds. -/
def init_sys.plan_buf_slice (buf : init_sys.PlanBuf) : Result (Slice Std.U8) :=
  if h : buf.bytes.length ≤ Usize.max then
    ok (Slice.from buf.bytes h)
  else
    fail .panic

/-- Release `buf`. -/
def init_sys.plan_buf_free (s : init_sys.Sys) (_buf : init_sys.PlanBuf) :
    Result init_sys.Sys :=
  ok s

/-- `prctl(PR_SET_PDEATHSIG, SIGKILL)` model. -/
def init_sys.prctl_pdeathsig_kill (s : init_sys.Sys) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  ok (.Ok (), s)

/-- `prctl(PR_SET_CHILD_SUBREAPER, 1)` model. -/
def init_sys.prctl_subreaper (s : init_sys.Sys) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  ok (.Ok (), s)

/-- `prctl(PR_SET_NO_NEW_PRIVS, 1)` model. -/
def init_sys.prctl_no_new_privs (s : init_sys.Sys) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  ok (.Ok (), s)

/-- `setrlimit(RLIMIT_CORE, {0, 0})` model. -/
def init_sys.setrlimit_core_zero (s : init_sys.Sys) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  ok (.Ok (), s)

/-- `setrlimit(RLIMIT_FSIZE, ...)` model. -/
def init_sys.setrlimit_fsize (s : init_sys.Sys) (_maxBytes : Std.U64) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  ok (.Ok (), s)

/-- `socket(AF_INET, SOCK_DGRAM | SOCK_CLOEXEC, 0)` model. -/
def init_sys.socket_udp_cloexec (s : init_sys.Sys) :
    Result (core.result.Result Std.I32 Std.I32 × init_sys.Sys) :=
  ok (.Ok 3#i32, s)

/-- `ioctl(sock_fd, SIOCGIFFLAGS, "lo")` model. -/
def init_sys.ioctl_get_lo_flags (s : init_sys.Sys) (sockFd : Std.I32) :
    Result (core.result.Result Std.I16 Std.I32 × init_sys.Sys) :=
  if sockFd.val < 0 then ok (.Err EBADF, s) else ok (.Ok s.loFlags, s)

/-- `ioctl(sock_fd, SIOCSIFFLAGS, "lo", flags)` model. -/
def init_sys.ioctl_set_lo_flags (s : init_sys.Sys) (sockFd : Std.I32)
    (flags : Std.I16) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  if sockFd.val < 0 then
    ok (.Err EBADF, s)
  else
    ok (.Ok (), { s with loFlags := flags })

/-- `socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0)` model. -/
def init_sys.socket_tcp_nonblock_cloexec (s : init_sys.Sys) :
    Result (core.result.Result Std.I32 Std.I32 × init_sys.Sys) :=
  ok (.Ok 10#i32, s)

/-- `setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, 1)` model. -/
def init_sys.setsockopt_reuseaddr (s : init_sys.Sys) (fd : Std.I32) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  if fd.val < 0 then ok (.Err EBADF, s) else ok (.Ok (), s)

/-- `bind(fd, 127.0.0.1:port)` model parameterized by `s.bindOracle` (accepts port `0`). -/
def init_sys.bind_loopback_v4 (s : init_sys.Sys) (fd : Std.I32)
    (port : Std.U16) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  if fd.val < 0 then
    ok (.Err EBADF, s)
  else
    match s.bindOracle with
    | some e :: rest =>
      ok (.Err (sanitizeErrno e), { s with bindOracle := rest })
    | none :: rest =>
      let s' := { s with bindOracle := rest, boundPorts := s.boundPorts ++ [port] }
      ok (.Ok (), s')
    | [] =>
      ok (.Ok (), { s with boundPorts := s.boundPorts ++ [port] })

/-- `listen(fd, backlog)` model parameterized by `s.listenOracle`. -/
def init_sys.listen_socket (s : init_sys.Sys) (fd _backlog : Std.I32) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  if fd.val < 0 then
    ok (.Err EBADF, s)
  else
    match s.listenOracle with
    | some e :: rest =>
      ok (.Err (sanitizeErrno e), { s with listenOracle := rest })
    | none :: rest =>
      ok (.Ok (), { s with listenOracle := rest })
    | [] => ok (.Ok (), s)

/-- `sendmsg_scm_batch` model checking `1 <= batch <= 32` and `start + batch <= 1024`,
parameterized by `s.scmSendOracle`. -/
def init_sys.sendmsg_scm_batch (s : init_sys.Sys) (ctrlFd : Std.I32)
    (_fds : Array Std.I32 1024#usize) (start batch : Std.Usize) :
    Result (core.result.Result Std.Usize Std.I32 × init_sys.Sys) :=
  if ctrlFd.val < 0 then
    ok (.Err EBADF, s)
  else if batch.val == 0 || batch.val > 32 || start.val + batch.val > 1024 then
    ok (.Err EINVAL, s)
  else
    match s.scmSendOracle with
    | .ok n :: rest =>
      let batches :=
        if n.val > 0 then s.scmSentBatches ++ [(ctrlFd, start, batch)]
        else s.scmSentBatches
      ok (.Ok n, { s with scmSendOracle := rest, scmSentBatches := batches })
    | .err e :: rest =>
      ok (.Err (sanitizeErrno e), { s with scmSendOracle := rest })
    | [] =>
      let batches := s.scmSentBatches ++ [(ctrlFd, start, batch)]
      ok (.Ok 1#usize, { s with scmSentBatches := batches })

/-- Query kernel Landlock ABI version (`s.landlockAbi`). -/
def init_sys.landlock_abi_version (s : init_sys.Sys) :
    Result (core.result.Result Std.I32 Std.I32 × init_sys.Sys) :=
  ok (.Ok s.landlockAbi, s)

/-- Create Landlock ruleset descriptor. -/
def init_sys.landlock_create_ruleset (s : init_sys.Sys)
    (_handledFs _handledNet : Std.U64) :
    Result (core.result.Result Std.I32 Std.I32 × init_sys.Sys) :=
  ok (.Ok 11#i32, s)

/-- Open `path` with `O_PATH | O_CLOEXEC`. -/
def init_sys.open_path_cloexec (s : init_sys.Sys) (path : Slice Std.U8) :
    Result (core.result.Result Std.I32 Std.I32 × init_sys.Sys) :=
  if path.val.length >= 4096 then ok (.Err 36#i32, s) else ok (.Ok 12#i32, s)

/-- Query whether `fd` refers to a directory (`s.fdIsDirOracle`, `[]` -> `true`). -/
def init_sys.fd_is_dir (s : init_sys.Sys) (fd : Std.I32) :
    Result (core.result.Result Bool Std.I32 × init_sys.Sys) :=
  if fd.val < 0 then
    ok (.Err EBADF, s)
  else
    match s.fdIsDirOracle with
    | .dir :: rest => ok (.Ok true, { s with fdIsDirOracle := rest })
    | .regular :: rest => ok (.Ok false, { s with fdIsDirOracle := rest })
    | .err e :: rest =>
      ok (.Err (sanitizeErrno e), { s with fdIsDirOracle := rest })
    | [] => ok (.Ok true, s)

/-- Add a Landlock `PATH_BENEATH` rule, logging `(rs, parentFd, access)`. -/
def init_sys.landlock_add_path_rule (s : init_sys.Sys)
    (rs parentFd : Std.I32) (access : Std.U64) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  if rs.val < 0 || parentFd.val < 0 then
    ok (.Err EBADF, s)
  else
    let rules := s.landlockPathRules ++ [(rs, parentFd, access)]
    ok (.Ok (), { s with landlockPathRules := rules })

/-- Add a Landlock `NET_PORT` rule. -/
def init_sys.landlock_add_net_port_rule (s : init_sys.Sys) (rs : Std.I32)
    (_port : Std.U16) (_access : Std.U64) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  if rs.val < 0 then ok (.Err EBADF, s) else ok (.Ok (), s)

/-- Enforce `landlock_restrict_self(rs, 0)`. -/
def init_sys.landlock_restrict_self (s : init_sys.Sys) (rs : Std.I32) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  if rs.val < 0 then ok (.Err EBADF, s) else ok (.Ok (), s)

/-- `syscall(SYS_seccomp, SECCOMP_SET_MODE_FILTER, 0, &prog)` model. -/
def init_sys.seccomp_set_mode_filter (s : init_sys.Sys)
    (filterBytes : Slice Std.U8) (insnCount : Std.U32) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  if insnCount.val == 0 || insnCount.val > 160 ||
      filterBytes.val.length != insnCount.val * 8 then
    ok (.Err EINVAL, s)
  else
    match s.seccompErr? with
    | some e => ok (.Err (sanitizeErrno e), s)
    | none =>
      let installed := s.seccompInstalled ++ [(.syscall, insnCount)]
      ok (.Ok (), { s with seccompInstalled := installed })

/-- `prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &prog, 0, 0)` model. -/
def init_sys.prctl_set_seccomp_filter (s : init_sys.Sys)
    (filterBytes : Slice Std.U8) (insnCount : Std.U32) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  if insnCount.val == 0 || insnCount.val > 160 ||
      filterBytes.val.length != insnCount.val * 8 then
    ok (.Err EINVAL, s)
  else
    match s.prctlSeccompErr? with
    | some e => ok (.Err (sanitizeErrno e), s)
    | none =>
      let installed := s.seccompInstalled ++ [(.prctl, insnCount)]
      ok (.Ok (), { s with seccompInstalled := installed })

/-- Allocate a pre-fork `ExecTable`. -/
def init_sys.exec_table_new (s : init_sys.Sys) (argc envc : Std.U32)
    (_strCap : Std.Usize) :
    Result (core.result.Result init_sys.ExecTable Std.I32 × init_sys.Sys) :=
  ok (.Ok { argc := argc, envc := envc }, s)

/-- Set `tbl.program`. -/
def init_sys.exec_table_set_program (s : init_sys.Sys) (tbl : init_sys.ExecTable)
    (prog : Slice Std.U8) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys × init_sys.ExecTable) :=
  ok (.Ok (), s, { tbl with program := prog.val })

/-- Set `tbl.cwd`. -/
def init_sys.exec_table_set_cwd (s : init_sys.Sys) (tbl : init_sys.ExecTable)
    (cwd : Slice Std.U8) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys × init_sys.ExecTable) :=
  ok (.Ok (), s, { tbl with cwd := cwd.val })

/-- Record `argv[idx + 1]` in `tbl`. -/
def init_sys.exec_table_set_arg (s : init_sys.Sys) (tbl : init_sys.ExecTable)
    (idx : Std.U32) (arg : Slice Std.U8) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys × init_sys.ExecTable) :=
  if idx.val >= tbl.argc.val then
    ok (.Err EINVAL, s, tbl)
  else
    ok (.Ok (), s, { tbl with args := tbl.args ++ [(idx, arg.val)] })

/-- Record `envp[idx] = "key=val"` in `tbl`. -/
def init_sys.exec_table_set_env (s : init_sys.Sys) (tbl : init_sys.ExecTable)
    (idx : Std.U32) (key val : Slice Std.U8) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys × init_sys.ExecTable) :=
  if idx.val >= tbl.envc.val then
    ok (.Err EINVAL, s, tbl)
  else
    ok (.Ok (), s, { tbl with env := tbl.env ++ [(idx, key.val, val.val)] })

/-- `pipe2(O_CLOEXEC)` model. -/
def init_sys.pipe2_cloexec (s : init_sys.Sys) :
    Result (core.result.Result (Std.I32 × Std.I32) Std.I32 × init_sys.Sys) :=
  ok (.Ok (14#i32, 15#i32), s)

/-- `fork()` model parameterized by `s.forkOutcome`. -/
def init_sys.fork_proc (s : init_sys.Sys) :
    Result (core.result.Result Std.I32 Std.I32 × init_sys.Sys) :=
  match s.forkOutcome with
  | .child => ok (.Ok 0#i32, s)
  | .parent pid =>
    let rpid := if pid.val > 0 then pid else 2#i32
    ok (.Ok rpid, s)
  | .err e => ok (.Err (sanitizeErrno e), s)

/-- `close_range(first, last, 0)` model. -/
def init_sys.close_range (s : init_sys.Sys) (first last : Std.U32) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  if first.val > last.val then ok (.Err EINVAL, s) else ok (.Ok (), s)

/-- `open("/proc/self/fd", O_RDONLY | O_CLOEXEC)` model. -/
def init_sys.open_proc_self_fd (s : init_sys.Sys) :
    Result (core.result.Result Std.I32 Std.I32 × init_sys.Sys) :=
  ok (.Ok 16#i32, s)

/-- `getdents64` model returning `EOF` (`0`). -/
def init_sys.getdents64_chunk (s : init_sys.Sys) (dirfd : Std.I32)
    (buf : Array Std.U8 256#usize) :
    Result (core.result.Result Std.Usize Std.I32 × init_sys.Sys ×
      Array Std.U8 256#usize) :=
  if dirfd.val < 0 then ok (.Err EBADF, s, buf) else ok (.Ok 0#usize, s, buf)

/-- `signal(SIGPIPE, SIG_DFL)` model. -/
def init_sys.reset_sigpipe_dfl (s : init_sys.Sys) : Result init_sys.Sys :=
  ok s

/-- `clearenv()` model. -/
def init_sys.clearenv_guest (s : init_sys.Sys) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  ok (.Ok (), s)

/-- `putenv(tbl.envp[idx])` model. -/
def init_sys.putenv_guest_entry (s : init_sys.Sys) (tbl : init_sys.ExecTable)
    (idx : Std.U32) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  if idx.val >= tbl.envc.val then ok (.Err EINVAL, s) else ok (.Ok (), s)

/-- `chdir(tbl.cwd)` model. -/
def init_sys.chdir_guest (s : init_sys.Sys) (tbl : init_sys.ExecTable) :
    Result (core.result.Result Unit Std.I32 × init_sys.Sys) :=
  if tbl.cwd.isEmpty then ok (.Err 2#i32, s) else ok (.Ok (), s)

/-- `execvp(tbl.program, tbl.argv)` failure errno model (`ENOENT = 2`). -/
def init_sys.execvp_guest (s : init_sys.Sys) (_tbl : init_sys.ExecTable) :
    Result (Std.I32 × init_sys.Sys) :=
  ok (2#i32, s)

/-- Blocking `waitpid` model parameterized by `s.waitpidOracle`. -/
def init_sys.waitpid_blocking (s : init_sys.Sys) (pid : Std.I32) :
    Result (core.result.Result (Std.I32 × Std.I32) Std.I32 × init_sys.Sys) :=
  match s.waitpidOracle with
  | .reaped rpid wst :: rest =>
    let s' := { s with
      waitpidOracle := rest
      reapedPids := s.reapedPids ++ [(rpid, wst)] }
    ok (.Ok (rpid, wst), s')
  | .err e :: rest =>
    ok (.Err (sanitizeErrno e), { s with waitpidOracle := rest })
  | [] =>
    if pid.val <= 0 then
      ok (.Err ECHILD, s)
    else
      let s' := { s with reapedPids := s.reapedPids ++ [(pid, 0#i32)] }
      ok (.Ok (pid, 0#i32), s')

/-- `kill(-1, SIGKILL)` model. -/
def init_sys.kill_all_sigkill (s : init_sys.Sys) : Result init_sys.Sys :=
  ok s

/-- `_exit(code)` model recording `exitCode?`. -/
def init_sys.exit_now (s : init_sys.Sys) (code : Std.I32) :
    Result init_sys.Sys :=
  ok { s with exitCode? := some code }
