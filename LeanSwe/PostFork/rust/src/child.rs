//! Proved caller-agnostic post-`fork` child setup entrypoint (`run_child`) with uniform
//! 8-byte failure wire protocol (`[0x50, 0x01, stage, 0x00, err_le32]`).
#![forbid(unsafe_code)]

use crate::fd_ops::{
    clear_cloexec_slice, close_fds_above2_except, close_unused_slice, probe_open_slice,
    probe_stdio_open, relocate_rep_above2, set_cloexec, setup_stdio, slice_contains_nonneg,
    slice_has_stdio_slot, slices_overlap_nonneg, EBADF, EINTR, EINVAL, EIO,
};
use crate::sys::{self, CStr, CStrArray, Sys};

/// Linux `SIGPIPE` signal number (`13` on both `x86_64` and `aarch64`).
pub const SIGPIPE: i32 = 13;
/// Linux `ENOENT` error number (`2` on both `x86_64` and `aarch64`).
pub const ENOENT: i32 = 2;
/// Exit status used when a cgroup/parent sync barrier closes or fails before `execve`.
pub const EXIT_SYNC_ABORT: i32 = 125;
/// Exit status used when post-`fork` validation, setup, `chdir`, or `execve` fails.
pub const EXIT_EXEC_FAILED: i32 = 127;

/// Failure-wire magic byte (`'P'`, `0x50`).
pub const WIRE_MAGIC: u8 = 0x50;
/// Failure-wire protocol version byte (`0x01`).
pub const WIRE_VERSION: u8 = 0x01;

/// Failure stage tag: pre-execution flag or descriptor validation failed.
pub const STAGE_VALIDATE: u8 = 1;
/// Failure stage tag: `setpgid(0, 0)` failed.
pub const STAGE_PROCESS_GROUP: u8 = 2;
/// Failure stage tag: `SIGPIPE` reset/unblock failed.
pub const STAGE_SIGNAL_RESET: u8 = 3;
/// Failure stage tag: descriptor probing, relocation, `setup_stdio`, or `FD_CLOEXEC` update failed.
pub const STAGE_FD_SETUP: u8 = 4;
/// Failure stage tag: `close_fds_above2_except` failed.
pub const STAGE_CLOSE_UNKEPT: u8 = 5;
/// Failure stage tag: `chdir(cwd)` failed.
pub const STAGE_CHDIR: u8 = 6;
/// Failure stage tag: `execve(path, argv, envp)` failed.
pub const STAGE_EXECVE: u8 = 7;

/// Child flag bit `0`: call `setpgid(0, 0)` before barrier/stdio setup.
pub const FLAG_SET_PGID: u32 = 1;
/// Child flag bit `1`: reset `SIGPIPE` to `SIG_DFL` and unblock `SIGPIPE` before `execve`.
pub const FLAG_RESET_SIGPIPE: u32 = 2;
/// Child flag bit `2`: wait for a 1-byte token on `sync_r` (`_exit(125)` on EOF/error).
pub const FLAG_HAS_SYNC_BARRIER: u32 = 4;
/// Child flag bit `3`: route `(stdin_fd, stdout_fd, stderr_fd)` onto `(0, 1, 2)` and relocate `rep_w`.
pub const FLAG_REDIRECT_STDIO: u32 = 8;
/// Child flag bit `4`: close all unkept descriptors `> 2` via `close_range` or `/proc/self/fd`.
pub const FLAG_CLOSE_UNKEPT_ABOVE2: u32 = 16;
/// Child flag bit `5`: close redirected stdio source descriptors `> 2` inside `setup_stdio`.
pub const FLAG_CLOSE_STDIO_SOURCES: u32 = 32;
/// Union of all defined child setup flag bits (`0..5`).
pub const ALL_FLAGS: u32 = 63;

/// Guarantee a strictly positive reported `errno`, substituting `fallback` when `err <= 0`.
pub fn normalize_errno(err: i32, fallback: i32) -> i32 {
    if err > 0 {
        err
    } else {
        fallback
    }
}

/// Encode `v` as 4 little-endian bytes.
pub fn encode_i32_le(v: i32) -> [u8; 4] {
    let u = v as u32;
    [
        (u & 0xff) as u8,
        ((u >> 8) & 0xff) as u8,
        ((u >> 16) & 0xff) as u8,
        ((u >> 24) & 0xff) as u8,
    ]
}

/// Encode `[0x50, 0x01, stage, 0x00, err_le32]` as the uniform 8-byte failure wire report.
pub fn encode_failure_report(stage: u8, errnum: i32) -> [u8; 8] {
    let e = errnum as u32;
    [
        WIRE_MAGIC,
        WIRE_VERSION,
        stage,
        0,
        (e & 0xff) as u8,
        ((e >> 8) & 0xff) as u8,
        ((e >> 16) & 0xff) as u8,
        ((e >> 24) & 0xff) as u8,
    ]
}

/// Write all of `buf` to `fd`, retrying on `EINTR` and advancing across partial writes.
pub fn write_all(s: &mut Sys, fd: i32, buf: &[u8]) -> Result<(), i32> {
    if fd < 0 {
        return Err(EBADF);
    }
    let len = buf.len();
    if len == 0 {
        let mut zero_err: i32 = 0;
        let mut zero_failed: bool = false;
        loop {
            match sys::write(s, fd, buf) {
                Ok(_) => {
                    break;
                }
                Err(e) => {
                    if e != EINTR {
                        zero_err = e;
                        zero_failed = true;
                        break;
                    }
                }
            }
        }
        if zero_failed {
            return Err(zero_err);
        }
        return Ok(());
    }
    let mut off: usize = 0;
    let mut err: i32 = 0;
    let mut failed: bool = false;
    while off < len {
        match sys::write(s, fd, &buf[off..len]) {
            Ok(0) => {
                err = EIO;
                failed = true;
                break;
            }
            Ok(n) => {
                if n <= len - off {
                    off += n;
                } else {
                    off = len;
                }
            }
            Err(e) => {
                if e != EINTR {
                    err = e;
                    failed = true;
                    break;
                }
            }
        }
    }
    if failed {
        Err(err)
    } else {
        Ok(())
    }
}

/// Ignore `SIGPIPE`, best-effort write `bytes` to `rep_w` when `SIG_IGN` is active, and terminate via `_exit(127)`.
pub fn report_bytes_and_exit(s: &mut Sys, rep_w: i32, bytes: &[u8]) {
    if rep_w >= 0 {
        if let Ok(()) = sys::sig_ign(s, SIGPIPE) {
            let _ = write_all(s, rep_w, bytes);
        }
    }
    sys::exit(s, EXIT_EXEC_FAILED);
}

/// Report a uniform 8-byte `(stage, normalize_errno(errnum, fallback))` frame to `rep_w` and `_exit(127)`.
pub fn report_and_exit(s: &mut Sys, rep_w: i32, stage: u8, errnum: i32, fallback: i32) {
    let msg = encode_failure_report(stage, normalize_errno(errnum, fallback));
    report_bytes_and_exit(s, rep_w, &msg);
}

/// Read 1 sync-barrier byte from `sync_r` retrying on `EINTR`, then close `sync_r`.
pub fn read_sync_byte(s: &mut Sys, sync_r: i32) -> bool {
    if sync_r < 0 {
        return false;
    }
    let mut got_one: bool = false;
    loop {
        let mut byte_buf: [u8; 1] = [0u8; 1];
        match sys::read1(s, sync_r, &mut byte_buf) {
            Ok(1) => {
                got_one = true;
                break;
            }
            Ok(_) => {
                break;
            }
            Err(e) => {
                if e != EINTR {
                    break;
                }
            }
        }
    }
    let _ = sys::close(s, sync_r);
    got_one
}

/// Validate flag bits (`0..5`) and `CLOSE_STDIO_SOURCES` compatibility.
pub fn validate_flags(flags: u32) -> Result<(), i32> {
    if (flags & !ALL_FLAGS) != 0 {
        return Err(EINVAL);
    }
    let redir_stdio = (flags & FLAG_REDIRECT_STDIO) != 0;
    let close_unkept = (flags & FLAG_CLOSE_UNKEPT_ABOVE2) != 0;
    let close_stdio_srcs = (flags & FLAG_CLOSE_STDIO_SOURCES) != 0;
    if close_stdio_srcs && (!redir_stdio || close_unkept) {
        return Err(EINVAL);
    }
    Ok(())
}

/// Validate required descriptor signs for `sync_r` and redirected stdio slots.
pub fn validate_signs(flags: u32, sync_r: i32, stdin_fd: i32, stdout_fd: i32, stderr_fd: i32) -> Result<(), i32> {
    if (flags & FLAG_HAS_SYNC_BARRIER) != 0 && sync_r < 0 {
        return Err(EBADF);
    }
    if (flags & FLAG_REDIRECT_STDIO) != 0 && (stdin_fd < 0 || stdout_fd < 0 || stderr_fd < 0) {
        return Err(EBADF);
    }
    Ok(())
}

/// Check if `fd` equals any of the three stdio source descriptors.
pub fn fd_in_stdio(fd: i32, stdin_fd: i32, stdout_fd: i32, stderr_fd: i32) -> bool {
    fd == stdin_fd || fd == stdout_fd || fd == stderr_fd
}

/// Check if any of the three stdio source descriptors appears in `fds`.
pub fn stdio_in_slice(fds: &[i32], stdin_fd: i32, stdout_fd: i32, stderr_fd: i32) -> bool {
    if slice_contains_nonneg(fds, stdin_fd) {
        return true;
    }
    if slice_contains_nonneg(fds, stdout_fd) {
        return true;
    }
    slice_contains_nonneg(fds, stderr_fd)
}

/// Validate `sync_r` disjointness when `FLAG_HAS_SYNC_BARRIER` is set.
pub fn validate_sync_overlaps(
    flags: u32,
    sync_r: i32,
    rep_w: i32,
    close_fds: &[i32],
    keep_fds: &[i32],
) -> Result<(), i32> {
    if (flags & FLAG_HAS_SYNC_BARRIER) == 0 {
        return Ok(());
    }
    if sync_r == rep_w || slice_contains_nonneg(close_fds, sync_r) || slice_contains_nonneg(keep_fds, sync_r) {
        return Err(EINVAL);
    }
    Ok(())
}

/// Scalar descriptor and flag bundle passed across post-`fork` child-setup stages.
#[derive(Clone, Copy)]
pub struct ChildFds {
    pub flags: u32,
    pub sync_r: i32,
    pub stdin_fd: i32,
    pub stdout_fd: i32,
    pub stderr_fd: i32,
    pub rep_w: i32,
}

/// Validate redirected stdio descriptor disjointness when `FLAG_REDIRECT_STDIO` is set.
pub fn validate_stdio_overlaps(fds: ChildFds, close_fds: &[i32], keep_fds: &[i32]) -> Result<(), i32> {
    if (fds.flags & FLAG_REDIRECT_STDIO) == 0 {
        return Ok(());
    }
    if slice_has_stdio_slot(keep_fds)
        || fd_in_stdio(fds.rep_w, fds.stdin_fd, fds.stdout_fd, fds.stderr_fd)
    {
        return Err(EINVAL);
    }
    if stdio_in_slice(close_fds, fds.stdin_fd, fds.stdout_fd, fds.stderr_fd) {
        return Err(EINVAL);
    }
    if (fds.flags & FLAG_HAS_SYNC_BARRIER) != 0
        && fd_in_stdio(fds.sync_r, fds.stdin_fd, fds.stdout_fd, fds.stderr_fd)
    {
        return Err(EINVAL);
    }
    if (fds.flags & FLAG_CLOSE_STDIO_SOURCES) != 0 {
        if (fds.stdin_fd > 2 && slice_contains_nonneg(keep_fds, fds.stdin_fd))
            || (fds.stdout_fd > 2 && slice_contains_nonneg(keep_fds, fds.stdout_fd))
            || (fds.stderr_fd > 2 && slice_contains_nonneg(keep_fds, fds.stderr_fd))
        {
            return Err(EINVAL);
        }
    }
    Ok(())
}

/// Validate all flags, descriptor signs, and descriptor-set disjointness prior to any state mutation.
pub fn validate_child_args(fds: ChildFds, close_fds: &[i32], keep_fds: &[i32]) -> Result<(), i32> {
    if let Err(e) = validate_flags(fds.flags) {
        return Err(e);
    }
    if let Err(e) = validate_signs(fds.flags, fds.sync_r, fds.stdin_fd, fds.stdout_fd, fds.stderr_fd) {
        return Err(e);
    }
    if slice_contains_nonneg(close_fds, fds.rep_w)
        || slice_contains_nonneg(keep_fds, fds.rep_w)
        || slices_overlap_nonneg(close_fds, keep_fds)
    {
        return Err(EINVAL);
    }
    if let Err(e) = validate_sync_overlaps(fds.flags, fds.sync_r, fds.rep_w, close_fds, keep_fds) {
        return Err(e);
    }
    validate_stdio_overlaps(fds, close_fds, keep_fds)
}

/// Conditionally call `setpgid(0, 0)` when `FLAG_SET_PGID` is set.
pub fn apply_set_pgid(s: &mut Sys, flags: u32) -> Result<(), i32> {
    if (flags & FLAG_SET_PGID) != 0 {
        sys::setpgid_self(s)
    } else {
        Ok(())
    }
}

/// Conditionally reset and unblock `SIGPIPE` when `FLAG_RESET_SIGPIPE` is set.
pub fn apply_reset_sigpipe(s: &mut Sys, flags: u32) -> Result<(), i32> {
    if (flags & FLAG_RESET_SIGPIPE) != 0 {
        if let Err(e) = sys::sig_dfl(s, SIGPIPE) {
            return Err(e);
        }
        sys::sig_unblock(s, SIGPIPE)
    } else {
        Ok(())
    }
}

/// Conditionally probe `sync_r` via `F_GETFD` when `FLAG_HAS_SYNC_BARRIER` is set.
pub fn probe_sync_fd(s: &mut Sys, flags: u32, sync_r: i32) -> Result<(), i32> {
    if (flags & FLAG_HAS_SYNC_BARRIER) != 0 {
        match sys::fcntl_getfd(s, sync_r) {
            Ok(_) => Ok(()),
            Err(e) => Err(e),
        }
    } else {
        Ok(())
    }
}

/// Conditionally probe `(stdin_fd, stdout_fd, stderr_fd)` when `FLAG_REDIRECT_STDIO` is set.
pub fn probe_redir_stdio(
    s: &mut Sys,
    flags: u32,
    stdin_fd: i32,
    stdout_fd: i32,
    stderr_fd: i32,
) -> Result<(), i32> {
    if (flags & FLAG_REDIRECT_STDIO) != 0 {
        probe_stdio_open(s, stdin_fd, stdout_fd, stderr_fd)
    } else {
        Ok(())
    }
}

/// Wait on `sync_r` if `FLAG_HAS_SYNC_BARRIER` is set, exiting with `125` on abort/EOF.
pub fn await_sync_barrier(s: &mut Sys, flags: u32, sync_r: i32) -> bool {
    if (flags & FLAG_HAS_SYNC_BARRIER) != 0 {
        if !read_sync_byte(s, sync_r) {
            sys::exit(s, EXIT_SYNC_ABORT);
            return false;
        }
    }
    true
}

/// Pre-barrier validation, process-group/SIGPIPE setup, descriptor probing, and sync wait.
pub fn run_child_pre_sync(s: &mut Sys, fds: ChildFds, close_fds: &[i32], keep_fds: &[i32]) -> bool {
    if fds.rep_w < 0 {
        sys::exit(s, EXIT_EXEC_FAILED);
        return false;
    }
    if let Err(e) = validate_child_args(fds, close_fds, keep_fds) {
        report_and_exit(s, fds.rep_w, STAGE_VALIDATE, e, EINVAL);
        return false;
    }
    if let Err(e) = apply_set_pgid(s, fds.flags) {
        report_and_exit(s, fds.rep_w, STAGE_PROCESS_GROUP, e, EIO);
        return false;
    }
    if let Err(e) = apply_reset_sigpipe(s, fds.flags) {
        report_and_exit(s, fds.rep_w, STAGE_SIGNAL_RESET, e, EIO);
        return false;
    }
    close_unused_slice(s, close_fds);
    if let Err(e) = probe_sync_fd(s, fds.flags, fds.sync_r) {
        report_and_exit(s, fds.rep_w, STAGE_FD_SETUP, e, EBADF);
        return false;
    }
    if let Err(e) = probe_redir_stdio(s, fds.flags, fds.stdin_fd, fds.stdout_fd, fds.stderr_fd) {
        report_and_exit(s, fds.rep_w, STAGE_FD_SETUP, e, EBADF);
        return false;
    }
    if let Err(e) = probe_open_slice(s, keep_fds) {
        report_and_exit(s, fds.rep_w, STAGE_FD_SETUP, e, EBADF);
        return false;
    }
    await_sync_barrier(s, fds.flags, fds.sync_r)
}

/// Protect `rep_w` (`FD_CLOEXEC`), relocating out of `0..2` when `redir_stdio` is true.
pub fn prepare_rep_w(s: &mut Sys, redir_stdio: bool, rep_w: i32) -> Result<i32, i32> {
    if redir_stdio {
        relocate_rep_above2(s, rep_w)
    } else {
        match set_cloexec(s, rep_w) {
            Ok(()) => Ok(rep_w),
            Err(e) => Err(e),
        }
    }
}

/// Apply stdio routing onto `0..2` when `redir_stdio` is true.
pub fn apply_redir_stdio(
    s: &mut Sys,
    redir_stdio: bool,
    stdin_fd: i32,
    stdout_fd: i32,
    stderr_fd: i32,
    close_stdio_srcs: bool,
) -> Result<(), i32> {
    if redir_stdio {
        setup_stdio(s, stdin_fd, stdout_fd, stderr_fd, close_stdio_srcs)
    } else {
        Ok(())
    }
}

/// Close unkept descriptors `> 2` when `close_unkept` is true.
pub fn apply_close_unkept(
    s: &mut Sys,
    close_unkept: bool,
    safe_rep_w: i32,
    keep_fds: &[i32],
) -> Result<(), i32> {
    if close_unkept {
        close_fds_above2_except(s, safe_rep_w, keep_fds)
    } else {
        Ok(())
    }
}

/// Post-barrier descriptor relocation, stdio routing, kept-FD flags, sweep, `chdir`, and `execve`.
pub fn run_child_post_sync(
    s: &mut Sys,
    fds: ChildFds,
    keep_fds: &[i32],
    cwd: Option<&CStr>,
    path: &CStr,
    argv: &CStrArray,
    envp: &CStrArray,
) {
    let redir_stdio = (fds.flags & FLAG_REDIRECT_STDIO) != 0;
    let close_unkept = (fds.flags & FLAG_CLOSE_UNKEPT_ABOVE2) != 0;
    let close_stdio_srcs = (fds.flags & FLAG_CLOSE_STDIO_SOURCES) != 0;
    let safe_rep_w = match prepare_rep_w(s, redir_stdio, fds.rep_w) {
        Ok(fd) => fd,
        Err(e) => {
            report_and_exit(s, fds.rep_w, STAGE_FD_SETUP, e, EIO);
            return;
        }
    };
    if let Err(e) = apply_redir_stdio(s, redir_stdio, fds.stdin_fd, fds.stdout_fd, fds.stderr_fd, close_stdio_srcs) {
        report_and_exit(s, safe_rep_w, STAGE_FD_SETUP, e, EIO);
        return;
    }
    if let Err(e) = clear_cloexec_slice(s, keep_fds) {
        report_and_exit(s, safe_rep_w, STAGE_FD_SETUP, e, EIO);
        return;
    }
    if let Err(e) = apply_close_unkept(s, close_unkept, safe_rep_w, keep_fds) {
        report_and_exit(s, safe_rep_w, STAGE_CLOSE_UNKEPT, e, EIO);
        return;
    }
    if let Some(dir) = cwd {
        if let Err(e) = sys::chdir(s, dir) {
            report_and_exit(s, safe_rep_w, STAGE_CHDIR, e, EIO);
            return;
        }
    }
    let e = sys::execve(s, path, argv, envp);
    report_and_exit(s, safe_rep_w, STAGE_EXECVE, e, ENOENT);
}

/// Caller-agnostic post-`fork` child setup pipeline executing the 14-step verified setup sequence.
#[allow(clippy::too_many_arguments)]
pub fn run_child(
    s: &mut Sys,
    fds: ChildFds,
    close_fds: &[i32],
    keep_fds: &[i32],
    cwd: Option<&CStr>,
    path: &CStr,
    argv: &CStrArray,
    envp: &CStrArray,
) {
    if !run_child_pre_sync(s, fds, close_fds, keep_fds) {
        return;
    }
    run_child_post_sync(s, fds, keep_fds, cwd, path, argv, envp);
}
