//! Flat scalar/pointer C-ABI pass-through (`--features standalone` only; excluded from Charon).

use core::ffi::c_char;

use crate::child::{
    report_and_exit, run_child, ChildFds, ExecSpec, EXIT_EXEC_FAILED, STAGE_VALIDATE,
};
use crate::fd_ops::{close_fds_above2_except_rc, EINVAL};
use crate::sys::{self, CStr, CStrArray, Sys};

/// Flat C-ABI input record for `leanswe_postfork_run_child`.
#[repr(C)]
pub struct CPostForkChildArgs {
    pub flags: u32,
    pub sync_r: i32,
    pub stdin_fd: i32,
    pub stdout_fd: i32,
    pub stderr_fd: i32,
    pub rep_w: i32,
    pub close_fds: *const i32,
    pub n_close_fds: usize,
    pub keep_fds: *const i32,
    pub n_keep_fds: usize,
    pub cwd: *const c_char,
    pub path: *const c_char,
    pub argv: *const *const c_char,
    pub envp: *const *const c_char,
}

#[inline(always)]
unsafe fn slice_i32_checked<'a>(ptr: *const i32, len: usize) -> Option<&'a [i32]> {
    if len == 0 {
        Some(&[])
    } else if ptr.is_null()
        || len > (isize::MAX as usize) / core::mem::size_of::<i32>()
        || (ptr as usize) & (core::mem::align_of::<i32>() - 1) != 0
    {
        None
    } else {
        Some(unsafe { core::slice::from_raw_parts(ptr, len) })
    }
}

/// Caller-agnostic C-ABI entrypoint executing `postfork::child::run_child`.
///
/// # Safety
/// Must be called in the child after `fork` with valid `args` or null.
#[no_mangle]
pub unsafe extern "C" fn leanswe_postfork_run_child(args: *const CPostForkChildArgs) {
    let mut s = unsafe { Sys::assume_forked_child() };
    if args.is_null() {
        sys::exit(&mut s, EXIT_EXEC_FAILED);
        return;
    }
    let a = unsafe { &*args };
    if a.path.is_null() || a.argv.is_null() || a.envp.is_null() {
        report_and_exit(&mut s, a.rep_w, STAGE_VALIDATE, EINVAL, EINVAL);
        return;
    }
    let close_fds = match unsafe { slice_i32_checked(a.close_fds, a.n_close_fds) } {
        Some(sl) => sl,
        None => {
            report_and_exit(&mut s, a.rep_w, STAGE_VALIDATE, EINVAL, EINVAL);
            return;
        }
    };
    let keep_fds = match unsafe { slice_i32_checked(a.keep_fds, a.n_keep_fds) } {
        Some(sl) => sl,
        None => {
            report_and_exit(&mut s, a.rep_w, STAGE_VALIDATE, EINVAL, EINVAL);
            return;
        }
    };
    let cwd = if a.cwd.is_null() {
        None
    } else {
        Some(unsafe { CStr::from_ptr(a.cwd) })
    };
    let path = unsafe { CStr::from_ptr(a.path) };
    let argv = unsafe { CStrArray::from_ptr(a.argv) };
    let envp = unsafe { CStrArray::from_ptr(a.envp) };
    let fds = ChildFds {
        flags: a.flags,
        sync_r: a.sync_r,
        stdin_fd: a.stdin_fd,
        stdout_fd: a.stdout_fd,
        stderr_fd: a.stderr_fd,
        rep_w: a.rep_w,
    };
    let exec = ExecSpec {
        cwd: cwd.as_ref(),
        path: &path,
        argv: &argv,
        envp: &envp,
    };
    run_child(&mut s, fds, close_fds, keep_fds, exec);
}

/// C-ABI helper exposing proved `close_fds_above2_except` (`0` on success, `errno > 0` on error).
///
/// # Safety
/// Must be called in a single-threaded child context with valid `(keep_fds, n_keep_fds)`.
#[no_mangle]
pub unsafe extern "C" fn leanswe_postfork_close_fds_above2_except(
    extra_keep_fd: i32,
    keep_fds: *const i32,
    n_keep_fds: usize,
) -> i32 {
    let mut s = unsafe { Sys::assume_forked_child() };
    let slice = match unsafe { slice_i32_checked(keep_fds, n_keep_fds) } {
        Some(sl) => sl,
        None => return EINVAL,
    };
    close_fds_above2_except_rc(&mut s, extra_keep_fd, slice)
}
