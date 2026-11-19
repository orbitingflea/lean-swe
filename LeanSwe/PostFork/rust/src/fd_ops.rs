//! Proved post-`fork` file-descriptor flag, clobber-free `0..2` stdio routing,
//! and `close_range` + `/proc/self/fd` `getdents64` descriptor-closing logic.
#![forbid(unsafe_code)]

use crate::sys::{self, Sys};

/// Linux `FD_CLOEXEC` descriptor flag bit.
pub const FD_CLOEXEC: i32 = 1;
/// Linux `EINTR` error code.
pub const EINTR: i32 = 4;
/// Linux `EIO` error code.
pub const EIO: i32 = 5;
/// Linux `EBADF` error code.
pub const EBADF: i32 = 9;
/// Linux `EINVAL` error code.
pub const EINVAL: i32 = 22;
/// Sentinel returned by `parse_dirent_name` for well-formed non-descriptor entries (`"."`, `".."`).
pub const DIRENT_OTHER: i32 = -1;
/// Sentinel returned by `parse_dirent_name` for malformed or non-NUL-terminated `d_name` slices.
pub const DIRENT_MALFORMED: i32 = -2;

/// Clear `FD_CLOEXEC` on `fd` while preserving any other descriptor flags via `F_GETFD` + `F_SETFD`.
pub fn clear_cloexec(s: &mut Sys, fd: i32) -> Result<(), i32> {
    match sys::fcntl_getfd(s, fd) {
        Ok(flags) => sys::fcntl_setfd(s, fd, flags & !FD_CLOEXEC),
        Err(e) => Err(e),
    }
}

/// Set `FD_CLOEXEC` on `fd` while preserving any other descriptor flags via `F_GETFD` + `F_SETFD`.
pub fn set_cloexec(s: &mut Sys, fd: i32) -> Result<(), i32> {
    match sys::fcntl_getfd(s, fd) {
        Ok(flags) => sys::fcntl_setfd(s, fd, flags | FD_CLOEXEC),
        Err(e) => Err(e),
    }
}

/// Verify that `stdin_fd`, `stdout_fd`, and `stderr_fd` are non-negative and currently open via `F_GETFD`.
pub fn probe_stdio_open(
    s: &mut Sys,
    stdin_fd: i32,
    stdout_fd: i32,
    stderr_fd: i32,
) -> Result<(), i32> {
    if stdin_fd < 0 || stdout_fd < 0 || stderr_fd < 0 {
        return Err(EBADF);
    }
    if let Err(e) = sys::fcntl_getfd(s, stdin_fd) {
        return Err(e);
    }
    if let Err(e) = sys::fcntl_getfd(s, stdout_fd) {
        return Err(e);
    }
    match sys::fcntl_getfd(s, stderr_fd) {
        Ok(_) => Ok(()),
        Err(e) => Err(e),
    }
}

/// Verify that every non-negative descriptor in `fds` is currently open via `F_GETFD`.
pub fn probe_open_slice(s: &mut Sys, fds: &[i32]) -> Result<(), i32> {
    let mut i: usize = 0;
    let n = fds.len();
    let mut err: i32 = 0;
    let mut failed: bool = false;
    while i < n {
        let fd = fds[i];
        if fd >= 0 {
            if let Err(e) = sys::fcntl_getfd(s, fd) {
                err = e;
                failed = true;
                break;
            }
        }
        i += 1;
    }
    if failed {
        Err(err)
    } else {
        Ok(())
    }
}

/// Clear `FD_CLOEXEC` on every non-negative descriptor in `fds` (negative sentinels are skipped).
pub fn clear_cloexec_slice(s: &mut Sys, fds: &[i32]) -> Result<(), i32> {
    let mut i: usize = 0;
    let n = fds.len();
    let mut err: i32 = 0;
    let mut failed: bool = false;
    while i < n {
        let fd = fds[i];
        if fd >= 0 {
            if let Err(e) = clear_cloexec(s, fd) {
                err = e;
                failed = true;
                break;
            }
        }
        i += 1;
    }
    if failed {
        Err(err)
    } else {
        Ok(())
    }
}

/// Return `true` iff `target >= 0` and `fds` contains `target`.
pub fn slice_contains_nonneg(fds: &[i32], target: i32) -> bool {
    if target < 0 {
        return false;
    }
    let mut i: usize = 0;
    let n = fds.len();
    let mut found: bool = false;
    while i < n {
        if fds[i] == target {
            found = true;
            break;
        }
        i += 1;
    }
    found
}

/// Return `true` iff `a` and `b` share any non-negative descriptor number.
pub fn slices_overlap_nonneg(a: &[i32], b: &[i32]) -> bool {
    let mut i: usize = 0;
    let n = a.len();
    let mut hit: bool = false;
    while i < n {
        let fd = a[i];
        if fd >= 0 && slice_contains_nonneg(b, fd) {
            hit = true;
            break;
        }
        i += 1;
    }
    hit
}

/// Return `true` iff `fds` contains any stdio slot `0`, `1`, or `2`.
pub fn slice_has_stdio_slot(fds: &[i32]) -> bool {
    let mut i: usize = 0;
    let n = fds.len();
    let mut hit: bool = false;
    while i < n {
        let fd = fds[i];
        if fd >= 0 && fd <= 2 {
            hit = true;
            break;
        }
        i += 1;
    }
    hit
}

/// Close every non-negative descriptor in `fds`, ignoring negative sentinels and `close` errors.
pub fn close_unused_slice(s: &mut Sys, fds: &[i32]) {
    let mut i: usize = 0;
    let n = fds.len();
    while i < n {
        let fd = fds[i];
        if fd >= 0 {
            let _ = sys::close(s, fd);
        }
        i += 1;
    }
}

/// Ensure `rep_w` lives at a descriptor `>= 3` with `FD_CLOEXEC` set; if `rep_w` starts in `0..=2`,
/// duplicate it to `>= 3` via `F_DUPFD_CLOEXEC` and close the original `0..=2` slot.
pub fn relocate_rep_above2(s: &mut Sys, rep_w: i32) -> Result<i32, i32> {
    if rep_w < 0 {
        Err(EBADF)
    } else if rep_w <= 2 {
        match sys::fcntl_dupfd_cloexec(s, rep_w, 3) {
            Ok(moved) => {
                let _ = sys::close(s, rep_w);
                Ok(moved)
            }
            Err(e) => Err(e),
        }
    } else {
        match set_cloexec(s, rep_w) {
            Ok(()) => Ok(rep_w),
            Err(e) => Err(e),
        }
    }
}

/// Install `stdin_fd`, `stdout_fd`, `stderr_fd` onto `0`, `1`, `2` without self-clobbering even
/// when inputs alias or permute `0..=2`, closing internal temporary descriptors unconditionally,
/// closing `> 2` caller source descriptors iff `close_sources_above2` is `true`, and clearing
/// `FD_CLOEXEC` on `0`, `1`, `2`.
pub fn setup_stdio(
    s: &mut Sys,
    stdin_fd: i32,
    stdout_fd: i32,
    stderr_fd: i32,
    close_sources_above2: bool,
) -> Result<(), i32> {
    if let Err(e) = probe_stdio_open(s, stdin_fd, stdout_fd, stderr_fd) {
        return Err(e);
    }
    let s0 = stdin_fd;
    let mut s1 = stdout_fd;
    let mut s2 = stderr_fd;
    let mut saved0: i32 = -1;
    let mut saved1: i32 = -1;
    if s0 != 0 && (s1 == 0 || s2 == 0) {
        match sys::fcntl_dupfd_cloexec(s, 0, 3) {
            Ok(fd) => {
                saved0 = fd;
                if s1 == 0 {
                    s1 = fd;
                }
                if s2 == 0 {
                    s2 = fd;
                }
            }
            Err(e) => return Err(e),
        }
    }
    if let Err(e) = sys::dup2(s, s0, 0) {
        if saved0 >= 0 {
            let _ = sys::close(s, saved0);
        }
        return Err(e);
    }
    if s1 != 1 && s2 == 1 {
        match sys::fcntl_dupfd_cloexec(s, 1, 3) {
            Ok(fd) => {
                saved1 = fd;
                s2 = fd;
            }
            Err(e) => {
                if saved0 >= 0 {
                    let _ = sys::close(s, saved0);
                }
                return Err(e);
            }
        }
    }
    if let Err(e) = sys::dup2(s, s1, 1) {
        if saved1 >= 0 {
            let _ = sys::close(s, saved1);
        }
        if saved0 >= 0 {
            let _ = sys::close(s, saved0);
        }
        return Err(e);
    }
    if let Err(e) = sys::dup2(s, s2, 2) {
        if saved1 >= 0 {
            let _ = sys::close(s, saved1);
        }
        if saved0 >= 0 {
            let _ = sys::close(s, saved0);
        }
        return Err(e);
    }
    if saved1 >= 0 {
        let _ = sys::close(s, saved1);
    }
    if saved0 >= 0 {
        let _ = sys::close(s, saved0);
    }
    if close_sources_above2 {
        if stdin_fd > 2 {
            let _ = sys::close(s, stdin_fd);
        }
        if stdout_fd > 2 && stdout_fd != stdin_fd {
            let _ = sys::close(s, stdout_fd);
        }
        if stderr_fd > 2 && stderr_fd != stdin_fd && stderr_fd != stdout_fd {
            let _ = sys::close(s, stderr_fd);
        }
    }
    if let Err(e) = clear_cloexec(s, 0) {
        return Err(e);
    }
    if let Err(e) = clear_cloexec(s, 1) {
        return Err(e);
    }
    clear_cloexec(s, 2)
}

/// Find the smallest kept descriptor `k > 2` (among `extra_keep_fd` and `keep_fds`) with `(k as u32) >= lo`.
pub fn next_keep_ge(extra_keep_fd: i32, keep_fds: &[i32], lo: u32) -> Option<u32> {
    let mut best: Option<u32> = if extra_keep_fd > 2 && (extra_keep_fd as u32) >= lo {
        Some(extra_keep_fd as u32)
    } else {
        None
    };
    let mut i: usize = 0;
    let n = keep_fds.len();
    while i < n {
        let fd = keep_fds[i];
        if fd > 2 {
            let u = fd as u32;
            if u >= lo {
                match best {
                    None => best = Some(u),
                    Some(cur) => {
                        if u < cur {
                            best = Some(u);
                        }
                    }
                }
            }
        }
        i += 1;
    }
    best
}

/// Close all descriptors `>= 3` outside `extra_keep_fd` and `keep_fds` via gap-wise `close_range`.
pub fn try_close_range_except(
    s: &mut Sys,
    extra_keep_fd: i32,
    keep_fds: &[i32],
) -> Result<(), i32> {
    let mut lo: u32 = 3;
    let mut err: i32 = 0;
    let mut failed: bool = false;
    loop {
        match next_keep_ge(extra_keep_fd, keep_fds, lo) {
            Some(k) => {
                if k > lo {
                    if let Err(e) = sys::close_range(s, lo, k - 1, 0) {
                        err = e;
                        failed = true;
                        break;
                    }
                }
                lo = k + 1;
            }
            None => {
                if let Err(e) = sys::close_range(s, lo, u32::MAX, 0) {
                    err = e;
                    failed = true;
                }
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

/// Parse a NUL-terminated `d_name` slice `buf[start..end]` from `getdents64`, returning
/// `fd >= 0` on canonical decimal descriptor names, `DIRENT_OTHER` (`-1`) on non-numeric names,
/// or `DIRENT_MALFORMED` (`-2`) on missing NUL or empty names.
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
    if nul - start > 1 && buf[start] == 48 {
        return DIRENT_OTHER;
    }
    let mut acc: u64 = 0;
    let mut j: usize = start;
    let mut digits_ok: bool = true;
    while j < nul && j < 256 {
        let b = buf[j];
        if b < 48 || b > 57 {
            digits_ok = false;
            break;
        }
        acc = acc * 10 + ((b - 48) as u64);
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

/// Scan one `getdents64` buffer `buf[0..n]` and close all non-kept descriptors `> 2`.
pub fn close_dirent_batch(
    s: &mut Sys,
    buf: &[u8; 256],
    n: usize,
    dirfd: i32,
    extra_keep_fd: i32,
    keep_fds: &[i32],
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
        if parsed > 2
            && parsed != dirfd
            && parsed != extra_keep_fd
            && !slice_contains_nonneg(keep_fds, parsed)
        {
            if let Err(e) = sys::close(s, parsed) {
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
pub fn close_via_proc_self_fd(
    s: &mut Sys,
    extra_keep_fd: i32,
    keep_fds: &[i32],
) -> Result<(), i32> {
    let dirfd = match sys::open_proc_self_fd(s) {
        Ok(fd) => fd,
        Err(e) => return Err(e),
    };
    let mut err: i32 = 0;
    let mut failed: bool = false;
    loop {
        let mut buf: [u8; 256] = [0u8; 256];
        match sys::getdents64(s, dirfd, &mut buf) {
            Ok(0) => break,
            Ok(n) => {
                if let Err(e) = close_dirent_batch(s, &buf, n, dirfd, extra_keep_fd, keep_fds) {
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
    if let Err(ce) = sys::close(s, dirfd) {
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

/// Close all descriptors `>= 3` except `extra_keep_fd` and `keep_fds`, trying gap-wise
/// `close_range` first and falling back to `/proc/self/fd` `getdents64`.
pub fn close_fds_above2_except(
    s: &mut Sys,
    extra_keep_fd: i32,
    keep_fds: &[i32],
) -> Result<(), i32> {
    match try_close_range_except(s, extra_keep_fd, keep_fds) {
        Ok(()) => Ok(()),
        Err(_) => close_via_proc_self_fd(s, extra_keep_fd, keep_fds),
    }
}

/// C-return-code wrapper around `close_fds_above2_except` returning `0` on success and positive `errno` on failure.
pub fn close_fds_above2_except_rc(
    s: &mut Sys,
    extra_keep_fd: i32,
    keep_fds: &[i32],
) -> i32 {
    match close_fds_above2_except(s, extra_keep_fd, keep_fds) {
        Ok(()) => 0,
        Err(e) => {
            if e > 0 {
                e
            } else {
                EIO
            }
        }
    }
}
