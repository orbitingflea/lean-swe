//! Proved container-init state logic and syscall orchestration (`psandbox-init`).
#![forbid(unsafe_code)]

use crate::cli::{parse_cli, validate_cli_fds, CliMode};
use crate::plan::{
    parse_plan, read_mount_entry, read_port_forward_at, read_str_span, read_sys_entry,
    span_end_ok, PlanView, PS_INIT_MAX_PLAN_BYTES,
};
use crate::init_sys::{self, ExecTable, PlanBuf, Sys};

/// Linux `EINTR` (`4`).
pub const EINTR: i32 = 4;
/// Linux `EIO` (`5`).
pub const EIO: i32 = 5;
/// Linux `E2BIG` (`7`).
pub const E2BIG: i32 = 7;
/// Linux `EBADF` (`9`).
pub const EBADF: i32 = 9;
/// Linux `ECHILD` (`10`).
pub const ECHILD: i32 = 10;
/// Linux `EINVAL` (`22`).
pub const EINVAL: i32 = 22;
/// Linux `ENOSYS` (`38`).
pub const ENOSYS: i32 = 38;

/// Descriptor flag bit `FD_CLOEXEC` (`1`).
pub const FD_CLOEXEC: i32 = 1;

/// `InitStatusMsg` tag: pre-`execvp` setup succeeded; waiting on `go_fd`.
pub const PS_STATUS_READY: u8 = 1;
/// `InitStatusMsg` tag: pre-`execvp` setup failed (`value = errno`).
pub const PS_STATUS_INIT_ERR: u8 = 2;
/// `InitStatusMsg` tag: guest `chdir` (`flag = 1`) or `execvp` (`flag = 0`) failed.
pub const PS_STATUS_EXEC_ERR: u8 = 3;
/// `InitStatusMsg` tag: guest exited normally (`value = exitCode`).
pub const PS_STATUS_EXITED: u8 = 4;
/// `InitStatusMsg` tag: guest was terminated by signal (`value = signal`).
pub const PS_STATUS_SIGNALED: u8 = 5;

/// Landlock `LANDLOCK_ACCESS_FS_EXECUTE` (`1 << 0`).
pub const PS_LL_FS_EXECUTE: u64 = 1 << 0;
/// Landlock `LANDLOCK_ACCESS_FS_WRITE_FILE` (`1 << 1`).
pub const PS_LL_FS_WRITE_FILE: u64 = 1 << 1;
/// Landlock `LANDLOCK_ACCESS_FS_READ_FILE` (`1 << 2`).
pub const PS_LL_FS_READ_FILE: u64 = 1 << 2;
/// Landlock `LANDLOCK_ACCESS_FS_READ_DIR` (`1 << 3`).
pub const PS_LL_FS_READ_DIR: u64 = 1 << 3;
/// Landlock `LANDLOCK_ACCESS_FS_TRUNCATE` (`1 << 14`).
pub const PS_LL_FS_TRUNCATE: u64 = 1 << 14;
/// Landlock ABI v4 full filesystem access mask (`(1 << 15) - 1`).
pub const PS_LL_FS_V4_ALL: u64 = (1 << 15) - 1;
/// Landlock regular-file-compatible access mask (stripping directory-only bits).
pub const PS_LL_FS_FILE_ONLY: u64 =
    PS_LL_FS_EXECUTE | PS_LL_FS_WRITE_FILE | PS_LL_FS_READ_FILE | PS_LL_FS_TRUNCATE;
/// Landlock read-only preset directory access mask (`READ_FILE | READ_DIR | EXECUTE`).
pub const PS_LL_FS_RO_EXEC: u64 = PS_LL_FS_READ_FILE | PS_LL_FS_READ_DIR | PS_LL_FS_EXECUTE;
/// Landlock safe `/dev/*` device access mask (`READ_FILE | WRITE_FILE | TRUNCATE | READ_DIR`).
pub const PS_LL_FS_SAFE_DEV: u64 =
    PS_LL_FS_READ_FILE | PS_LL_FS_WRITE_FILE | PS_LL_FS_TRUNCATE | PS_LL_FS_READ_DIR;
/// Landlock `LANDLOCK_ACCESS_NET_BIND_TCP` (`1 << 0`).
pub const PS_LL_NET_BIND_TCP: u64 = 1 << 0;
/// Landlock `LANDLOCK_ACCESS_NET_CONNECT_TCP` (`1 << 1`).
pub const PS_LL_NET_CONNECT_TCP: u64 = 1 << 1;

/// Network interface flag `IFF_UP` (`0x1`).
pub const IFF_UP: i16 = 0x1;
/// Network interface flag `IFF_RUNNING` (`0x40`).
pub const IFF_RUNNING: i16 = 0x40;

/// Maximum descriptors transmitted in one `SCM_RIGHTS` `sendmsg` batch (`32`).
pub const MAX_SCM_BATCH: u32 = 32;

/// Encode `(kind, flag, value)` into the 8-byte `InitStatusMsg` wire frame `[kind, flag, 0, 0, val_le32]`.
pub fn encode_status_msg(kind: u8, flag: u8, value: i32) -> [u8; 8] {
    let u = value as u32;
    [
        kind,
        flag,
        0,
        0,
        (u & 0xff) as u8,
        ((u >> 8) & 0xff) as u8,
        ((u >> 16) & 0xff) as u8,
        ((u >> 24) & 0xff) as u8,
    ]
}

/// Decode an 8-byte `InitStatusMsg` wire frame into `(kind, flag, value)`.
pub fn decode_status_msg(bytes: &[u8; 8]) -> (u8, u8, i32) {
    let b4 = bytes[4] as u32;
    let b5 = (bytes[5] as u32) << 8;
    let b6 = (bytes[6] as u32) << 16;
    let b7 = (bytes[7] as u32) << 24;
    let v = (b4 | b5 | b6 | b7) as i32;
    (bytes[0], bytes[1], v)
}

/// Compute `handled_access_net` for Landlock ruleset creation.
pub fn landlock_net_handled_mask(allow_box_localhost: bool) -> u64 {
    if allow_box_localhost {
        0
    } else {
        PS_LL_NET_BIND_TCP | PS_LL_NET_CONNECT_TCP
    }
}

/// Compute effective Landlock filesystem access bits after stripping directory bits on non-directories.
pub fn landlock_effective_fs_access(requested: u64, is_dir: bool) -> u64 {
    if is_dir {
        requested
    } else {
        requested & PS_LL_FS_FILE_ONLY
    }
}

/// Compute Landlock filesystem access bits for a user mount (`tag == 0` read-only vs writable).
pub fn landlock_mount_access(tag: u8) -> u64 {
    if tag == 0 {
        PS_LL_FS_RO_EXEC
    } else {
        PS_LL_FS_V4_ALL
    }
}

/// Compute the next `SCM_RIGHTS` batch size (`1..=32`) for `remaining` descriptors.
pub fn scm_batch_len(remaining: u32) -> u32 {
    if remaining > MAX_SCM_BATCH {
        MAX_SCM_BATCH
    } else {
        remaining
    }
}

/// Compute updated loopback interface flags if `IFF_UP` is currently unset.
pub fn loopback_updated_flags(cur_flags: i16) -> Option<i16> {
    if (cur_flags & IFF_UP) == 0 {
        Some(cur_flags | IFF_UP | IFF_RUNNING)
    } else {
        None
    }
}

/// Classify a raw Linux `waitpid` status word into `(kind, flag, exit_or_sig)`.
pub fn classify_wait_status(st: i32) -> (u8, u8, i32) {
    let low = st & 0x7f;
    if low == 0 {
        (PS_STATUS_EXITED, 0, (st >> 8) & 0xff)
    } else if low != 0x7f {
        (PS_STATUS_SIGNALED, 0, low)
    } else {
        (PS_STATUS_EXITED, 0, 1)
    }
}

/// Set `FD_CLOEXEC` on `fd` if `fd >= 0`.
pub fn set_cloexec_if_valid(s: &mut Sys, fd: i32) {
    if fd >= 0 {
        if let Ok(flags) = init_sys::fcntl_getfd(s, fd) {
            let _ = init_sys::fcntl_setfd(s, fd, flags | FD_CLOEXEC);
        }
    }
}

/// Write all of `buf` to `fd`, retrying `EINTR` and advancing across partial writes.
pub fn write_all(s: &mut Sys, fd: i32, buf: &[u8]) -> Result<(), i32> {
    if fd < 0 {
        return Err(EBADF);
    }
    let len = buf.len();
    let mut off: usize = 0;
    let mut err: i32 = EIO;
    let mut failed: bool = false;
    while off < len {
        match init_sys::write_fd(s, fd, &buf[off..len]) {
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

/// Best-effort write of an 8-byte `InitStatusMsg` to `fd` when `fd >= 0`.
pub fn send_status(s: &mut Sys, fd: i32, kind: u8, flag: u8, value: i32) {
    if fd >= 0 {
        let msg = encode_status_msg(kind, flag, value);
        let _ = write_all(s, fd, &msg);
    }
}

/// Read `plan_fd` to EOF (up to `16 MiB`, retrying `EINTR`, rejecting `>= 16 MiB` overflow with `E2BIG`).
pub fn read_plan_fd(s: &mut Sys, plan_fd: i32) -> Result<PlanBuf, i32> {
    let mut buf = init_sys::plan_buf_new(s, 4096)?;
    let mut err: i32 = 0;
    let mut failed: bool = false;
    loop {
        let cur_len = init_sys::plan_buf_len(&buf);
        let cur_cap = init_sys::plan_buf_cap(&buf);
        if cur_len == cur_cap {
            if cur_cap >= PS_INIT_MAX_PLAN_BYTES {
                err = E2BIG;
                failed = true;
                break;
            }
            let next_cap = if cur_cap > PS_INIT_MAX_PLAN_BYTES / 2 {
                PS_INIT_MAX_PLAN_BYTES
            } else {
                cur_cap * 2
            };
            if let Err(e) = init_sys::plan_buf_reserve(s, &mut buf, next_cap) {
                err = e;
                failed = true;
                break;
            }
        }
        match init_sys::plan_buf_read_once(s, plan_fd, &mut buf) {
            Ok(0) => break,
            Ok(_) => {}
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
        init_sys::plan_buf_free(s, buf);
        Err(err)
    } else {
        Ok(buf)
    }
}

/// Bring up the private network namespace `lo` interface (`IFF_UP | IFF_RUNNING`).
pub fn ensure_loopback_up(s: &mut Sys) -> Result<(), i32> {
    let sock = init_sys::socket_udp_cloexec(s)?;
    let res = match init_sys::ioctl_get_lo_flags(s, sock) {
        Ok(cur) => match loopback_updated_flags(cur) {
            Some(next_flags) => init_sys::ioctl_set_lo_flags(s, sock, next_flags),
            None => Ok(()),
        },
        Err(e) => Err(e),
    };
    let _ = init_sys::close_fd(s, sock);
    res
}

/// Send `count` listener descriptors over `ctrl_fd` in `<= 32`-FD `SCM_RIGHTS` batches.
pub fn send_fds_scm(
    s: &mut Sys,
    ctrl_fd: i32,
    fds: &[i32; 1024],
    count: u32,
) -> Result<(), i32> {
    let mut off: u32 = 0;
    let mut err: i32 = EIO;
    let mut failed: bool = false;
    while off < count {
        let batch = scm_batch_len(count - off);
        let mut sent_ok: bool = false;
        loop {
            match init_sys::sendmsg_scm_batch(s, ctrl_fd, fds, off as usize, batch as usize) {
                Ok(n) => {
                    if n > 0 {
                        sent_ok = true;
                    } else {
                        err = EIO;
                    }
                    break;
                }
                Err(e) => {
                    if e != EINTR {
                        err = e;
                        break;
                    }
                }
            }
        }
        if !sent_ok {
            failed = true;
            break;
        }
        off += batch;
    }
    if failed {
        Err(err)
    } else {
        Ok(())
    }
}

/// Close all non-negative descriptors in `fds[0..limit]`.
pub fn close_listener_prefix(s: &mut Sys, fds: &[i32; 1024], limit: u32) {
    let mut i: usize = 0;
    let n = if limit <= 1024 { limit as usize } else { 1024 };
    while i < n {
        let fd = fds[i];
        if fd >= 0 {
            let _ = init_sys::close_fd(s, fd);
        }
        i += 1;
    }
}

/// Open, configure `SO_REUSEADDR`, `bind(127.0.0.1:port)`, and `listen(128)` a loopback TCP socket, closing `fd` on error.
pub fn open_loopback_listener(s: &mut Sys, port: u16) -> Result<i32, i32> {
    let fd = init_sys::socket_tcp_nonblock_cloexec(s)?;
    let _ = init_sys::setsockopt_reuseaddr(s, fd);
    if let Err(e) = init_sys::bind_loopback_v4(s, fd, port) {
        let _ = init_sys::close_fd(s, fd);
        return Err(e);
    }
    if let Err(e) = init_sys::listen_socket(s, fd, 128) {
        let _ = init_sys::close_fd(s, fd);
        return Err(e);
    }
    Ok(fd)
}

/// Bind `127.0.0.1:box_port` listeners inside the box and hand them off via `SCM_RIGHTS`.
pub fn setup_port_forwards(
    s: &mut Sys,
    ctrl_fd: i32,
    data: &[u8],
    view: &PlanView,
) -> Result<(), i32> {
    if view.n_fwds == 0 {
        return Ok(());
    }
    if ctrl_fd < 0 || view.n_fwds > 1024 {
        return Err(EIO);
    }
    let mut lfds: [i32; 1024] = [-1i32; 1024];
    let mut i: u32 = 0;
    let mut err: i32 = EIO;
    let mut failed: bool = false;
    while i < view.n_fwds {
        match read_port_forward_at(data, view.fwds_pos, i) {
            Ok((box_port, _host_port)) => match open_loopback_listener(s, box_port) {
                Ok(fd) => {
                    lfds[i as usize] = fd;
                    i += 1;
                }
                Err(e) => {
                    err = e;
                    failed = true;
                    break;
                }
            },
            Err(e) => {
                err = e;
                failed = true;
                break;
            }
        }
    }
    if !failed {
        if let Err(e) = send_fds_scm(s, ctrl_fd, &lfds, view.n_fwds) {
            err = e;
            failed = true;
        }
    }
    close_listener_prefix(s, &lfds, i);
    if failed {
        Err(err)
    } else {
        Ok(())
    }
}

/// Open `path` with `O_PATH | O_CLOEXEC`, strip directory bits on regular files, and add to `rs`.
pub fn add_ll_path(s: &mut Sys, rs: i32, path: &[u8], access: u64) -> Result<(), i32> {
    let fd = init_sys::open_path_cloexec(s, path)?;
    let is_dir = match init_sys::fd_is_dir(s, fd) {
        Ok(d) => d,
        Err(e) => {
            let _ = init_sys::close_fd(s, fd);
            return Err(e);
        }
    };
    let eff = landlock_effective_fs_access(access, is_dir);
    if eff != 0 {
        if let Err(e) = init_sys::landlock_add_path_rule(s, rs, fd, eff) {
            let _ = init_sys::close_fd(s, fd);
            return Err(e);
        }
    }
    let _ = init_sys::close_fd(s, fd);
    Ok(())
}

/// Add the fixed root, `/proc`, `/etc/hosts`, and safe `/dev/*` Landlock path rules to `rs`.
pub fn add_ll_fixed_paths(s: &mut Sys, rs: i32) -> Result<(), i32> {
    add_ll_path(s, rs, b"/", PS_LL_FS_READ_DIR)?;
    add_ll_path(s, rs, b"/proc", PS_LL_FS_READ_FILE | PS_LL_FS_READ_DIR)?;
    add_ll_path(s, rs, b"/etc/hosts", PS_LL_FS_READ_FILE)?;
    add_ll_path(s, rs, b"/dev", PS_LL_FS_READ_DIR)?;
    add_ll_path(s, rs, b"/dev/null", PS_LL_FS_SAFE_DEV)?;
    add_ll_path(s, rs, b"/dev/zero", PS_LL_FS_SAFE_DEV)?;
    add_ll_path(s, rs, b"/dev/urandom", PS_LL_FS_SAFE_DEV)?;
    add_ll_path(s, rs, b"/dev/tty", PS_LL_FS_SAFE_DEV)?;
    add_ll_path(s, rs, b"/dev/ptmx", PS_LL_FS_SAFE_DEV)?;
    add_ll_path(s, rs, b"/dev/pts", PS_LL_FS_SAFE_DEV)
}

/// Add Landlock read+exec rules for all `tag == 0` system preset directories.
pub fn add_ll_sys_paths(s: &mut Sys, rs: i32, data: &[u8], view: &PlanView) -> Result<(), i32> {
    let mut cur: usize = view.sys_pos;
    let mut i: u32 = 0;
    let mut err: i32 = EINVAL;
    let mut failed: bool = false;
    while i < view.n_sys {
        match read_sys_entry(data, cur) {
            Ok((tag, sp, next_pos)) => {
                cur = next_pos;
                if tag == 0 && span_end_ok(sp, data.len()) {
                    if let Err(e) =
                        add_ll_path(s, rs, &data[sp.start..sp.start + sp.len], PS_LL_FS_RO_EXEC)
                    {
                        err = e;
                        failed = true;
                        break;
                    }
                }
                i += 1;
            }
            Err(e) => {
                err = e;
                failed = true;
                break;
            }
        }
    }
    if failed {
        Err(err)
    } else {
        Ok(())
    }
}

/// Add Landlock read+exec rules for all `/etc` preset paths.
pub fn add_ll_etc_paths(s: &mut Sys, rs: i32, data: &[u8], view: &PlanView) -> Result<(), i32> {
    let mut cur: usize = view.etc_pos;
    let mut i: u32 = 0;
    let mut err: i32 = EINVAL;
    let mut failed: bool = false;
    while i < view.n_etc {
        match read_str_span(data, cur) {
            Ok((sp, next_pos)) => {
                cur = next_pos;
                if span_end_ok(sp, data.len()) {
                    if let Err(e) =
                        add_ll_path(s, rs, &data[sp.start..sp.start + sp.len], PS_LL_FS_RO_EXEC)
                    {
                        err = e;
                        failed = true;
                        break;
                    }
                }
                i += 1;
            }
            Err(e) => {
                err = e;
                failed = true;
                break;
            }
        }
    }
    if failed {
        Err(err)
    } else {
        Ok(())
    }
}

/// Add Landlock rules for all user mounts (`RO_EXEC` for `tag == 0`, `V4_ALL` otherwise).
pub fn add_ll_mount_paths(s: &mut Sys, rs: i32, data: &[u8], view: &PlanView) -> Result<(), i32> {
    let mut cur: usize = view.mounts_pos;
    let mut i: u32 = 0;
    let mut err: i32 = EINVAL;
    let mut failed: bool = false;
    while i < view.n_mounts {
        match read_mount_entry(data, cur) {
            Ok((tag, sp, next_pos)) => {
                cur = next_pos;
                if span_end_ok(sp, data.len()) {
                    let acc = landlock_mount_access(tag);
                    if let Err(e) = add_ll_path(s, rs, &data[sp.start..sp.start + sp.len], acc) {
                        err = e;
                        failed = true;
                        break;
                    }
                }
                i += 1;
            }
            Err(e) => {
                err = e;
                failed = true;
                break;
            }
        }
    }
    if failed {
        Err(err)
    } else {
        Ok(())
    }
}

/// Add Landlock `CONNECT_TCP` port rules for forwarded ports when `!allow_box_localhost`.
pub fn add_ll_net_ports(s: &mut Sys, rs: i32, data: &[u8], view: &PlanView) -> Result<(), i32> {
    if view.header.allow_box_localhost {
        return Ok(());
    }
    let mut i: u32 = 0;
    let mut err: i32 = EINVAL;
    let mut failed: bool = false;
    while i < view.n_fwds {
        match read_port_forward_at(data, view.fwds_pos, i) {
            Ok((box_port, _host_port)) => {
                if let Err(e) = init_sys::landlock_add_net_port_rule(s, rs, box_port, PS_LL_NET_CONNECT_TCP)
                {
                    err = e;
                    failed = true;
                    break;
                }
                i += 1;
            }
            Err(e) => {
                err = e;
                failed = true;
                break;
            }
        }
    }
    if failed {
        Err(err)
    } else {
        Ok(())
    }
}

/// Populate all Landlock rules onto `rs` and call `landlock_restrict_self`.
pub fn populate_and_restrict_landlock(
    s: &mut Sys,
    rs: i32,
    data: &[u8],
    view: &PlanView,
) -> Result<(), i32> {
    add_ll_fixed_paths(s, rs)?;
    add_ll_sys_paths(s, rs, data, view)?;
    add_ll_etc_paths(s, rs, data, view)?;
    add_ll_mount_paths(s, rs, data, view)?;
    add_ll_net_ports(s, rs, data, view)?;
    init_sys::landlock_restrict_self(s, rs)
}

/// Verify Landlock ABI >= 4 (`min_abi`), build the ruleset, and enforce `landlock_restrict_self`.
pub fn install_landlock(s: &mut Sys, data: &[u8], view: &PlanView) -> Result<(), i32> {
    let abi = init_sys::landlock_abi_version(s)?;
    if abi < 4 || (abi as u32) < view.header.landlock_min_abi {
        return Err(ENOSYS);
    }
    let net_mask = landlock_net_handled_mask(view.header.allow_box_localhost);
    let rs = init_sys::landlock_create_ruleset(s, PS_LL_FS_V4_ALL, net_mask)?;
    let res = populate_and_restrict_landlock(s, rs, data, view);
    let _ = init_sys::close_fd(s, rs);
    res
}

/// Install the validated `seccomp` classic BPF filter from `data` (`SYS_seccomp` with `ENOSYS` fallback to `prctl`).
pub fn install_seccomp(s: &mut Sys, data: &[u8], view: &PlanView) -> Result<(), i32> {
    let byte_len = (view.seccomp_n as usize) * 8;
    if view.seccomp_pos > data.len() || byte_len > data.len() - view.seccomp_pos {
        return Err(EINVAL);
    }
    let slice = &data[view.seccomp_pos..view.seccomp_pos + byte_len];
    match init_sys::seccomp_set_mode_filter(s, slice, view.seccomp_n) {
        Ok(()) => Ok(()),
        Err(e) => {
            if e == ENOSYS {
                init_sys::prctl_set_seccomp_filter(s, slice, view.seccomp_n)
            } else {
                Err(e)
            }
        }
    }
}

/// Populate `argv[1..=argc]` in `tbl` from `data`.
pub fn populate_exec_args(
    s: &mut Sys,
    tbl: &mut ExecTable,
    data: &[u8],
    view: &PlanView,
) -> Result<(), i32> {
    let mut cur: usize = view.args_pos;
    let mut i: u32 = 0;
    let mut err: i32 = EINVAL;
    let mut failed: bool = false;
    while i < view.argc {
        match read_str_span(data, cur) {
            Ok((sp, next_pos)) => {
                cur = next_pos;
                if !span_end_ok(sp, data.len()) {
                    failed = true;
                    break;
                }
                if let Err(e) = init_sys::exec_table_set_arg(s, tbl, i, &data[sp.start..sp.start + sp.len])
                {
                    err = e;
                    failed = true;
                    break;
                }
                i += 1;
            }
            Err(e) => {
                err = e;
                failed = true;
                break;
            }
        }
    }
    if failed {
        Err(err)
    } else {
        Ok(())
    }
}

/// Populate `envp[0..envc]` in `tbl` from `data`.
pub fn populate_exec_env(
    s: &mut Sys,
    tbl: &mut ExecTable,
    data: &[u8],
    view: &PlanView,
) -> Result<(), i32> {
    let mut cur: usize = view.env_pos;
    let mut i: u32 = 0;
    let mut err: i32 = EINVAL;
    let mut failed: bool = false;
    while i < view.envc {
        match read_str_span(data, cur) {
            Ok((ksp, p1)) => match read_str_span(data, p1) {
                Ok((vsp, p2)) => {
                    cur = p2;
                    if !span_end_ok(ksp, data.len()) || !span_end_ok(vsp, data.len()) {
                        failed = true;
                        break;
                    }
                    let ks = &data[ksp.start..ksp.start + ksp.len];
                    let vs = &data[vsp.start..vsp.start + vsp.len];
                    if let Err(e) = init_sys::exec_table_set_env(s, tbl, i, ks, vs) {
                        err = e;
                        failed = true;
                        break;
                    }
                    i += 1;
                }
                Err(e) => {
                    err = e;
                    failed = true;
                    break;
                }
            },
            Err(e) => {
                err = e;
                failed = true;
                break;
            }
        }
    }
    if failed {
        Err(err)
    } else {
        Ok(())
    }
}

/// Build the complete pre-fork `ExecTable` (`program`, `cwd`, `argv`, `envp`).
pub fn build_exec_table(s: &mut Sys, data: &[u8], view: &PlanView) -> Result<ExecTable, i32> {
    if !span_end_ok(view.program, data.len()) || !span_end_ok(view.cwd, data.len()) {
        return Err(EINVAL);
    }
    let mut tbl = init_sys::exec_table_new(s, view.argc, view.envc, data.len())?;
    let prog = &data[view.program.start..view.program.start + view.program.len];
    let cwd = &data[view.cwd.start..view.cwd.start + view.cwd.len];
    init_sys::exec_table_set_program(s, &mut tbl, prog)?;
    init_sys::exec_table_set_cwd(s, &mut tbl, cwd)?;
    populate_exec_args(s, &mut tbl, data, view)?;
    populate_exec_env(s, &mut tbl, data, view)?;
    Ok(tbl)
}

/// Wait for the 1-byte `go_fd` release token, retrying `EINTR` and closing `go_fd`.
pub fn wait_for_go_byte(s: &mut Sys, go_fd: i32) -> bool {
    let mut got: bool = false;
    loop {
        let mut b: [u8; 1] = [0u8; 1];
        match init_sys::read1(s, go_fd, &mut b) {
            Ok(1) => {
                got = true;
                break;
            }
            Ok(_) => break,
            Err(e) => {
                if e != EINTR {
                    break;
                }
            }
        }
    }
    let _ = init_sys::close_fd(s, go_fd);
    got
}

/// Sentinel returned by `parse_dirent_name` on non-numeric entries (`"."`, `".."`, etc.).
pub const DIRENT_OTHER: i32 = -1;
/// Sentinel returned by `parse_dirent_name` on missing NUL or empty entry names.
pub const DIRENT_MALFORMED: i32 = -2;

/// Parse a NUL-terminated `d_name` slice `buf[start..end]` from `getdents64`, mirroring `postfork::fd_ops::parse_dirent_name`.
pub fn parse_dirent_name(buf: &[u8; 256], start: usize, end: usize) -> i32 {
    if end > 256 || start >= end || start >= 256 {
        return DIRENT_MALFORMED;
    }
    let mut nul: usize = start;
    while nul < end && nul < 256 {
        if buf[nul] == 0 {
            break;
        }
        nul += 1;
    }
    if nul >= end || nul == start {
        return DIRENT_MALFORMED;
    }
    if nul - start > 1 && buf[start] == b'0' {
        return DIRENT_OTHER;
    }
    let mut acc: u64 = 0;
    let mut j: usize = start;
    let mut digits_ok: bool = true;
    while j < nul && j < 256 {
        let b = buf[j];
        if b < b'0' || b > b'9' {
            digits_ok = false;
            break;
        }
        acc = acc * 10 + ((b - b'0') as u64);
        if acc > (i32::MAX as u64) {
            digits_ok = false;
            break;
        }
        j += 1;
    }
    if digits_ok {
        acc as i32
    } else {
        DIRENT_OTHER
    }
}

/// Scan one `getdents64` buffer `buf[0..n]` and close all non-kept descriptors `> 2`, mirroring `postfork::fd_ops::close_dirent_batch`.
pub fn close_dirent_batch(
    s: &mut Sys,
    buf: &[u8; 256],
    n: usize,
    dirfd: i32,
    keep_fd: i32,
) -> Result<(), i32> {
    if n > 256 {
        return Err(EIO);
    }
    let mut pos: usize = 0;
    let mut err: i32 = EIO;
    let mut bad: bool = false;
    while pos < n {
        if n - pos < 20 || pos > 236 {
            bad = true;
            break;
        }
        let lo = buf[pos + 16] as usize;
        let hi = buf[pos + 17] as usize;
        let reclen = lo | (hi << 8);
        if reclen < 20 || reclen > n - pos {
            bad = true;
            break;
        }
        let parsed = parse_dirent_name(buf, pos + 19, pos + reclen);
        if parsed == DIRENT_MALFORMED {
            bad = true;
            break;
        }
        if parsed > 2 && parsed != dirfd && parsed != keep_fd {
            if let Err(e) = init_sys::close_fd(s, parsed) {
                err = e;
                bad = true;
                break;
            }
        }
        pos += reclen;
    }
    if bad {
        Err(err)
    } else {
        Ok(())
    }
}

/// Fallback descriptor closer scanning `/proc/self/fd` via `getdents64` with `EINTR` retry.
pub fn close_via_proc_self_fd(s: &mut Sys, keep_fd: i32) -> Result<(), i32> {
    let dirfd = init_sys::open_proc_self_fd(s)?;
    let mut err: i32 = 0;
    let mut failed: bool = false;
    loop {
        let mut buf: [u8; 256] = [0u8; 256];
        match init_sys::getdents64_chunk(s, dirfd, &mut buf) {
            Ok(0) => break,
            Ok(n) => {
                if let Err(e) = close_dirent_batch(s, &buf, n, dirfd, keep_fd) {
                    err = e;
                    failed = true;
                    break;
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
    if let Err(ce) = init_sys::close_fd(s, dirfd) {
        if !failed {
            err = ce;
            failed = true;
        }
    }
    if failed {
        Err(err)
    } else {
        Ok(())
    }
}

/// Close all descriptors `>= 3` except `keep_fd` (`close_range` -> `/proc/self/fd` -> `3..65536`).
pub fn close_guest_extra_fds(s: &mut Sys, keep_fd: i32) {
    if keep_fd <= 2 {
        if init_sys::close_range(s, 3, u32::MAX).is_ok() {
            return;
        }
    } else {
        let k = keep_fd as u32;
        let ok1 = if k > 3 {
            init_sys::close_range(s, 3, k - 1).is_ok()
        } else {
            true
        };
        let ok2 = init_sys::close_range(s, k + 1, u32::MAX).is_ok();
        if ok1 && ok2 {
            return;
        }
    }
    if close_via_proc_self_fd(s, keep_fd).is_ok() {
        return;
    }
    let mut fd: i32 = 3;
    while fd < 65536 {
        if fd != keep_fd {
            let _ = init_sys::close_fd(s, fd);
        }
        fd += 1;
    }
}

/// Clear inherited environment (`clearenv`) and install `0..envc` pre-built `"key=val"` entries via `putenv`.
pub fn install_guest_env(s: &mut Sys, tbl: &ExecTable, envc: u32) -> Result<(), i32> {
    init_sys::clearenv_guest(s)?;
    let mut i: u32 = 0;
    let mut err: i32 = EIO;
    let mut failed: bool = false;
    while i < envc {
        if let Err(e) = init_sys::putenv_guest_entry(s, tbl, i) {
            err = e;
            failed = true;
            break;
        }
        i += 1;
    }
    if failed {
        Err(err)
    } else {
        Ok(())
    }
}

/// Execute the forked guest child setup (`close_guest_extra_fds`, `install_guest_env`, `chdir`, `execvp`).
pub fn run_guest_child(
    s: &mut Sys,
    err_r: i32,
    err_w: i32,
    status_fd: i32,
    tbl: &ExecTable,
    envc: u32,
) {
    let _ = init_sys::close_fd(s, err_r);
    let _ = init_sys::close_fd(s, status_fd);
    close_guest_extra_fds(s, err_w);
    init_sys::reset_sigpipe_dfl(s);
    if let Err(e) = install_guest_env(s, tbl, envc) {
        send_status(s, err_w, PS_STATUS_EXEC_ERR, 0, e);
        init_sys::exit_now(s, 127);
        return;
    }
    if let Err(e) = init_sys::chdir_guest(s, tbl) {
        send_status(s, err_w, PS_STATUS_EXEC_ERR, 1, e);
        init_sys::exit_now(s, 127);
        return;
    }
    let exec_err = init_sys::execvp_guest(s, tbl);
    send_status(s, err_w, PS_STATUS_EXEC_ERR, 0, exec_err);
    init_sys::exit_now(s, 127);
}

/// Read up to 8 bytes from `exec_err_pipe[0]` (retrying `EINTR`) and close `err_r`.
pub fn read_exec_err_frame(s: &mut Sys, err_r: i32) -> ([u8; 8], usize) {
    let mut buf: [u8; 8] = [0u8; 8];
    let mut got: usize = 0;
    while got < 8 {
        match init_sys::read_status_tail(s, err_r, &mut buf, got) {
            Ok(0) => break,
            Ok(n) => {
                if n <= 8 - got {
                    got += n;
                } else {
                    got = 8;
                }
            }
            Err(e) => {
                if e != EINTR {
                    break;
                }
            }
        }
    }
    let _ = init_sys::close_fd(s, err_r);
    (buf, got)
}

/// Wait for `child_pid` retrying `EINTR`, returning the raw `wstatus` word (`0` on non-`EINTR` error).
pub fn wait_direct_child(s: &mut Sys, child_pid: i32) -> i32 {
    let mut st: i32 = 0;
    loop {
        match init_sys::waitpid_blocking(s, child_pid) {
            Ok((_pid, wstatus)) => {
                st = wstatus;
                break;
            }
            Err(e) => {
                if e != EINTR {
                    break;
                }
            }
        }
    }
    st
}

/// Kill all remaining PID-namespace descendants (`kill(-1, SIGKILL)`) and reap until `ECHILD`.
pub fn kill_and_reap_descendants(s: &mut Sys) {
    init_sys::kill_all_sigkill(s);
    loop {
        match init_sys::waitpid_blocking(s, -1) {
            Ok((pid, _st)) => {
                if pid <= 0 {
                    break;
                }
            }
            Err(e) => {
                if e == EINTR {
                    continue;
                }
                if e == ECHILD {
                    break;
                }
                break;
            }
        }
    }
}

/// Supervise the forked guest child, reap descendants, and report terminal `InitStatusMsg`.
pub fn supervise_child(
    s: &mut Sys,
    child_pid: i32,
    err_r: i32,
    err_w: i32,
    status_fd: i32,
) -> i32 {
    let _ = init_sys::close_fd(s, err_w);
    let _ = init_sys::close_fd(s, 0);
    let _ = init_sys::close_fd(s, 1);
    let _ = init_sys::close_fd(s, 2);
    let (frame, got) = read_exec_err_frame(s, err_r);
    if got > 0 {
        let _ = wait_direct_child(s, child_pid);
        let (kind, flag, val) = decode_status_msg(&frame);
        if got == 8 && kind == PS_STATUS_EXEC_ERR {
            send_status(s, status_fd, PS_STATUS_EXEC_ERR, flag, val);
        } else {
            send_status(s, status_fd, PS_STATUS_EXEC_ERR, 0, EIO);
        }
        let _ = init_sys::close_fd(s, status_fd);
        return 0;
    }
    let st = wait_direct_child(s, child_pid);
    kill_and_reap_descendants(s);
    let (kind, flag, val) = classify_wait_status(st);
    send_status(s, status_fd, kind, flag, val);
    let _ = init_sys::close_fd(s, status_fd);
    0
}

/// Apply pre-isolation process attributes (`PDEATHSIG`, `CHILD_SUBREAPER`, `RLIMIT_CORE`, `RLIMIT_FSIZE`).
pub fn apply_process_limits(s: &mut Sys, view: &PlanView) -> Result<(), i32> {
    init_sys::prctl_pdeathsig_kill(s)?;
    init_sys::prctl_subreaper(s)?;
    init_sys::setrlimit_core_zero(s)?;
    if view.header.has_file_size_max {
        init_sys::setrlimit_fsize(s, view.header.file_size_max_bytes)?;
    }
    Ok(())
}

/// Parse `plan_buf`, run all pre-`READY` sandbox setup steps, and build `(ExecTable, envc)`.
pub fn setup_sandbox_from_plan(
    s: &mut Sys,
    plan_buf: &PlanBuf,
    ctrl_fd: &mut i32,
) -> Result<(ExecTable, u32), i32> {
    let data = init_sys::plan_buf_slice(plan_buf);
    let view = parse_plan(data)?;
    apply_process_limits(s, &view)?;
    ensure_loopback_up(s)?;
    if view.n_fwds > 0 {
        if let Err(e) = setup_port_forwards(s, *ctrl_fd, data, &view) {
            if *ctrl_fd >= 0 {
                let _ = init_sys::close_fd(s, *ctrl_fd);
                *ctrl_fd = -1;
            }
            return Err(e);
        }
    }
    if *ctrl_fd >= 0 {
        let _ = init_sys::close_fd(s, *ctrl_fd);
        *ctrl_fd = -1;
    }
    init_sys::prctl_no_new_privs(s)?;
    install_landlock(s, data, &view)?;
    install_seccomp(s, data, &view)?;
    let tbl = build_exec_table(s, data, &view)?;
    Ok((tbl, view.envc))
}

/// Complete container `psandbox-init` lifecycle (`--probe` or full sandboxed execution).
pub fn run_init(s: &mut Sys, argc: usize) -> i32 {
    let raw_fds = match parse_cli(s, argc) {
        CliMode::Probe => return 0,
        CliMode::Run(f) => f,
    };
    set_cloexec_if_valid(s, raw_fds.plan_fd);
    set_cloexec_if_valid(s, raw_fds.status_fd);
    set_cloexec_if_valid(s, raw_fds.go_fd);
    set_cloexec_if_valid(s, raw_fds.ctrl_fd);
    let fds = match validate_cli_fds(raw_fds) {
        Ok(f) => f,
        Err(e) => {
            send_status(s, raw_fds.status_fd, PS_STATUS_INIT_ERR, 0, e);
            return 1;
        }
    };
    let plan_buf = match read_plan_fd(s, fds.plan_fd) {
        Ok(b) => b,
        Err(e) => {
            let _ = init_sys::close_fd(s, fds.plan_fd);
            send_status(s, fds.status_fd, PS_STATUS_INIT_ERR, 0, e);
            return 1;
        }
    };
    let _ = init_sys::close_fd(s, fds.plan_fd);
    let mut ctrl_fd = fds.ctrl_fd;
    let (exec_tbl, envc) = match setup_sandbox_from_plan(s, &plan_buf, &mut ctrl_fd) {
        Ok(pair) => pair,
        Err(e) => {
            init_sys::plan_buf_free(s, plan_buf);
            send_status(s, fds.status_fd, PS_STATUS_INIT_ERR, 0, e);
            return 1;
        }
    };
    init_sys::plan_buf_free(s, plan_buf);
    send_status(s, fds.status_fd, PS_STATUS_READY, 0, 0);
    if !wait_for_go_byte(s, fds.go_fd) {
        let _ = init_sys::close_fd(s, fds.status_fd);
        return 0;
    }
    let (err_r, err_w) = match init_sys::pipe2_cloexec(s) {
        Ok(p) => p,
        Err(e) => {
            send_status(s, fds.status_fd, PS_STATUS_INIT_ERR, 0, e);
            return 1;
        }
    };
    match init_sys::fork_proc(s) {
        Ok(0) => {
            run_guest_child(s, err_r, err_w, fds.status_fd, &exec_tbl, envc);
            127
        }
        Ok(child_pid) => supervise_child(s, child_pid, err_r, err_w, fds.status_fd),
        Err(e) => {
            let _ = init_sys::close_fd(s, err_r);
            let _ = init_sys::close_fd(s, err_w);
            send_status(s, fds.status_fd, PS_STATUS_INIT_ERR, 0, e);
            1
        }
    }
}
