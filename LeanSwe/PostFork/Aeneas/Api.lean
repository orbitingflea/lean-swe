import LeanSwe.PostFork.Aeneas.Funs
import LeanSwe.PostFork.Aeneas.Model

open _root_.Aeneas _root_.Aeneas.Std Result

namespace LeanSwe.PostFork.Aeneas

open LeanSwe.PostFork.World

/-- Private Aeneas capability bundle wrapping the Charon/Aeneas-translated `#![no_std]` Rust `postfork` functions. -/
structure PostForkAeneasApi where
  /-- Encode the uniform 8-byte failure wire `[0x50, 0x01, stage, 0x00, err_le32]`. -/
  encodeFailureReport : Std.U8 → Std.I32 → Result (Array Std.U8 8#usize)
  /-- Validate flags, descriptor signs, and descriptor-set disjointness (`postfork.child.validate_child_args`). -/
  validateChildArgs :
    Std.U32 → Std.I32 → Std.I32 → Std.I32 → Std.I32 → Std.I32 →
      Slice Std.I32 → Slice Std.I32 → Result (core.result.Result Unit Std.I32)
  /-- Clear `FD_CLOEXEC` via `F_GETFD` + `F_SETFD(flags & ~FD_CLOEXEC)`, preserving extra flags. -/
  clearCloexec : ChildState → Std.I32 → Result (core.result.Result Unit Std.I32 × ChildState)
  /-- Set `FD_CLOEXEC` via `F_GETFD` + `F_SETFD(flags | FD_CLOEXEC)`, preserving extra flags. -/
  setCloexec : ChildState → Std.I32 → Result (core.result.Result Unit Std.I32 × ChildState)
  /-- Relocate `rep_w` in `0..2` to `>= 3` via `F_DUPFD_CLOEXEC` + `close`, or set `FD_CLOEXEC` when `rep_w >= 3`. -/
  relocateRepAbove2 : ChildState → Std.I32 → Result (core.result.Result Std.I32 Std.I32 × ChildState)
  /-- Route `(stdin_fd, stdout_fd, stderr_fd)` onto `(0, 1, 2)` without clobbering cycles and clear `FD_CLOEXEC`. -/
  setupStdio : ChildState → Std.I32 → Std.I32 → Std.I32 → Bool → Result (core.result.Result Unit Std.I32 × ChildState)
  /-- Close all open descriptors `> 2` except `extra_keep_fd` and `keep_fds` via `close_range` or `/proc/self/fd`. -/
  closeFdsAbove2Except : ChildState → Std.I32 → Slice Std.I32 → Result (core.result.Result Unit Std.I32 × ChildState)
  /-- Parse a `/proc/self/fd` `linux_dirent64` `d_name` slice (`>= 0` canonical fd, `-1` other, `-2` malformed). -/
  parseDirentName : Array Std.U8 256#usize → Std.Usize → Std.Usize → Result Std.I32
  /-- Read 1 sync-barrier byte with `EINTR` retry and unconditionally close `sync_r`. -/
  readSyncByte : ChildState → Std.I32 → Result (Bool × ChildState)
  /-- Write the entire slice to `fd`, retrying `EINTR` and reassembling partial writes. -/
  writeAll : ChildState → Std.I32 → Slice Std.U8 → Result (core.result.Result Unit Std.I32 × ChildState)
  /-- Execute unified post-`fork` child setup (`postfork.child.run_child`). -/
  runChild :
    ChildState → Std.U32 → Std.I32 → Std.I32 → Std.I32 → Std.I32 → Std.I32 →
      Slice Std.I32 → Slice Std.I32 → Option sys.CStr → sys.CStr → sys.CStrArray → sys.CStrArray →
      Result ChildState

/-- Default `PostForkAeneasApi` backed by Charon/Aeneas-translated `postfork` functions. -/
noncomputable def rustAeneasApi : PostForkAeneasApi where
  encodeFailureReport := postfork.child.encode_failure_report
  validateChildArgs := postfork.child.validate_child_args
  clearCloexec := postfork.fd_ops.clear_cloexec
  setCloexec := postfork.fd_ops.set_cloexec
  relocateRepAbove2 := postfork.fd_ops.relocate_rep_above2
  setupStdio := postfork.fd_ops.setup_stdio
  closeFdsAbove2Except := postfork.fd_ops.close_fds_above2_except
  parseDirentName := postfork.fd_ops.parse_dirent_name
  readSyncByte := postfork.child.read_sync_byte
  writeAll := postfork.child.write_all
  runChild := postfork.child.run_child

end LeanSwe.PostFork.Aeneas
