//! Proved CLI flag and descriptor parser for `psandbox-init`.
#![forbid(unsafe_code)]

use crate::init_sys::{self, Sys};

/// Linux `EINVAL` error number (`22`).
pub const EINVAL: i32 = 22;

/// Upper bound (`1,048,576`) on CLI-passed descriptor numbers (`parse_int_arg` parity).
pub const MAX_CLI_FD: i32 = 1_048_576;

/// Parsed descriptor numbers supplied via `--plan-fd`, `--status-fd`, `--go-fd`, and `--ctrl-fd`.
#[derive(Clone, Copy)]
pub struct CliFds {
    pub plan_fd: i32,
    pub status_fd: i32,
    pub go_fd: i32,
    pub ctrl_fd: i32,
}

/// Top-level CLI invocation mode (`--probe` vs container init run).
#[derive(Clone, Copy)]
pub enum CliMode {
    Probe,
    Run(CliFds),
}

/// Compare two byte slices for exact byte-for-byte equality.
pub fn slice_eq(a: &[u8], b: &[u8]) -> bool {
    let n = a.len();
    if n != b.len() {
        return false;
    }
    let mut i: usize = 0;
    let mut same: bool = true;
    while i < n {
        if a[i] != b[i] {
            same = false;
            break;
        }
        i += 1;
    }
    same
}

/// Parse an ASCII decimal descriptor argument in `0..=1_048_576`, returning `-1` otherwise.
pub fn parse_fd_arg(s: &[u8]) -> i32 {
    let n = s.len();
    if n == 0 {
        return -1;
    }
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    let mut ok: bool = true;
    while i < n {
        let b = s[i];
        if b < b'0' || b > b'9' {
            ok = false;
            break;
        }
        acc = acc * 10 + ((b - b'0') as u64);
        if acc > (MAX_CLI_FD as u64) {
            ok = false;
            break;
        }
        i += 1;
    }
    if ok {
        acc as i32
    } else {
        -1
    }
}

/// Update `fds` with one `(flag, value)` CLI argument pair.
pub fn apply_cli_pair(fds: CliFds, flag: &[u8], val: &[u8]) -> CliFds {
    if slice_eq(flag, b"--plan-fd") {
        CliFds {
            plan_fd: parse_fd_arg(val),
            ..fds
        }
    } else if slice_eq(flag, b"--status-fd") {
        CliFds {
            status_fd: parse_fd_arg(val),
            ..fds
        }
    } else if slice_eq(flag, b"--go-fd") {
        CliFds {
            go_fd: parse_fd_arg(val),
            ..fds
        }
    } else if slice_eq(flag, b"--ctrl-fd") {
        CliFds {
            ctrl_fd: parse_fd_arg(val),
            ..fds
        }
    } else {
        fds
    }
}

/// Verify that all three mandatory descriptors (`plan_fd`, `status_fd`, `go_fd`) are non-negative.
pub fn validate_cli_fds(fds: CliFds) -> Result<CliFds, i32> {
    if fds.plan_fd < 0 || fds.status_fd < 0 || fds.go_fd < 0 {
        Err(EINVAL)
    } else {
        Ok(fds)
    }
}

/// Parse `argv[0..argc]` via `init_sys::read_cli_arg` into `CliMode`.
pub fn parse_cli(s: &mut Sys, argc: usize) -> CliMode {
    if argc == 2 {
        let mut arg1: [u8; 64] = [0u8; 64];
        let n1 = init_sys::read_cli_arg(s, 1, &mut arg1);
        if n1 == 7 && slice_eq(&arg1[0..7], b"--probe") {
            return CliMode::Probe;
        }
    }
    let mut fds = CliFds {
        plan_fd: -1,
        status_fd: -1,
        go_fd: -1,
        ctrl_fd: -1,
    };
    let mut i: usize = 1;
    while i < argc && argc - i >= 2 {
        let mut flag_buf: [u8; 64] = [0u8; 64];
        let mut val_buf: [u8; 64] = [0u8; 64];
        let fn_len = init_sys::read_cli_arg(s, i, &mut flag_buf);
        let vn_len = init_sys::read_cli_arg(s, i + 1, &mut val_buf);
        if fn_len <= 64 {
            if vn_len <= 64 {
                fds = apply_cli_pair(fds, &flag_buf[0..fn_len], &val_buf[0..vn_len]);
            } else {
                fds = apply_cli_pair(fds, &flag_buf[0..fn_len], b"");
            }
        }
        i += 2;
    }
    CliMode::Run(fds)
}
