//! Trusted 1-syscall Linux boundary (`--opaque postfork::sys`).

use core::ffi::c_char;

/// Zero-sized capability token representing the child OS state after `fork`.
pub struct Sys {
    _private: (),
}

impl Sys {
    /// Construct the child state token inside the freshly forked child branch.
    ///
    /// # Safety
    /// Must be called only in the child process between `fork` and `execve`/`_exit`.
    pub unsafe fn assume_forked_child() -> Sys {
        Sys { _private: () }
    }
}

/// Borrowed NUL-terminated C string prepared before `fork`.
pub struct CStr {
    ptr: *const c_char,
}

/// Borrowed NULL-terminated array of NUL-terminated C strings prepared before `fork`.
pub struct CStrArray {
    ptr: *const *const c_char,
}

impl CStr {
    /// Wrap a NUL-terminated C string pointer.
    ///
    /// # Safety
    /// `ptr` must point to a valid NUL-terminated string live until `execve`/`_exit`.
    pub const unsafe fn from_ptr(ptr: *const c_char) -> CStr {
        CStr { ptr }
    }
}

impl CStrArray {
    /// Wrap a NULL-terminated C string-pointer array.
    ///
    /// # Safety
    /// `ptr` must point to a valid NULL-terminated array of valid C strings live until `execve`/`_exit`.
    pub const unsafe fn from_ptr(ptr: *const *const c_char) -> CStrArray {
        CStrArray { ptr }
    }
}

#[inline(always)]
fn errno() -> i32 {
    unsafe { *libc::__errno_location() }
}

#[inline(always)]
fn check_unit(r: libc::c_int) -> Result<(), i32> {
    if r < 0 {
        Err(errno())
    } else {
        Ok(())
    }
}

#[inline(always)]
fn check_i32(r: libc::c_int) -> Result<i32, i32> {
    if r < 0 {
        Err(errno())
    } else {
        Ok(r)
    }
}

#[inline(always)]
fn check_usize(r: isize) -> Result<usize, i32> {
    if r < 0 {
        Err(errno())
    } else {
        Ok(r as usize)
    }
}

/// `setpgid(0, 0)`.
pub fn setpgid_self(_s: &mut Sys) -> Result<(), i32> {
    check_unit(unsafe { libc::setpgid(0, 0) })
}

#[repr(C)]
struct KernelSigaction {
    sa_handler: usize,
    sa_flags: usize,
    sa_restorer: usize,
    sa_mask: u64,
}

fn rt_sigaction_set(sig: i32, handler: usize) -> Result<(), i32> {
    if sig < 1 || sig > 64 || sig == 32 || sig == 33 {
        return Err(libc::EINVAL);
    }
    let ksa = KernelSigaction {
        sa_handler: handler,
        sa_flags: 0,
        sa_restorer: 0,
        sa_mask: 0,
    };
    let r = unsafe {
        libc::syscall(
            libc::SYS_rt_sigaction,
            sig as libc::c_long,
            &ksa as *const KernelSigaction,
            core::ptr::null_mut::<KernelSigaction>(),
            8usize,
        )
    };
    if r < 0 {
        Err(errno())
    } else {
        Ok(())
    }
}

/// `rt_sigaction(sig, {SIG_DFL, 0, empty}, NULL)`.
pub fn sig_dfl(_s: &mut Sys, sig: i32) -> Result<(), i32> {
    rt_sigaction_set(sig, libc::SIG_DFL)
}

/// `rt_sigaction(sig, {SIG_IGN, 0, empty}, NULL)`.
pub fn sig_ign(_s: &mut Sys, sig: i32) -> Result<(), i32> {
    rt_sigaction_set(sig, libc::SIG_IGN)
}

/// `rt_sigprocmask(SIG_UNBLOCK, {sig}, NULL, 8)`.
pub fn sig_unblock(_s: &mut Sys, sig: i32) -> Result<(), i32> {
    if sig < 1 || sig > 64 {
        return Err(libc::EINVAL);
    }
    let mask: u64 = 1u64 << ((sig - 1) as u32);
    let r = unsafe {
        libc::syscall(
            libc::SYS_rt_sigprocmask,
            libc::SIG_UNBLOCK as libc::c_long,
            &mask as *const u64,
            core::ptr::null_mut::<u64>(),
            8usize,
        )
    };
    if r < 0 {
        Err(errno())
    } else {
        Ok(())
    }
}

/// `close(fd)`.
pub fn close(_s: &mut Sys, fd: i32) -> Result<(), i32> {
    check_unit(unsafe { libc::close(fd) })
}

/// `dup2(oldfd, newfd)`.
pub fn dup2(_s: &mut Sys, oldfd: i32, newfd: i32) -> Result<(), i32> {
    check_unit(unsafe { libc::dup2(oldfd, newfd) })
}

/// `fcntl(fd, F_GETFD)`.
pub fn fcntl_getfd(_s: &mut Sys, fd: i32) -> Result<i32, i32> {
    check_i32(unsafe { libc::fcntl(fd, libc::F_GETFD) })
}

/// `fcntl(fd, F_SETFD, flags)`.
pub fn fcntl_setfd(_s: &mut Sys, fd: i32, flags: i32) -> Result<(), i32> {
    check_unit(unsafe { libc::fcntl(fd, libc::F_SETFD, flags) })
}

/// `fcntl(fd, F_DUPFD_CLOEXEC, min_fd)`.
pub fn fcntl_dupfd_cloexec(_s: &mut Sys, fd: i32, min_fd: i32) -> Result<i32, i32> {
    check_i32(unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, min_fd) })
}

/// `syscall(SYS_close_range, first, last, flags)`.
pub fn close_range(_s: &mut Sys, first: u32, last: u32, flags: u32) -> Result<(), i32> {
    let r = unsafe {
        libc::syscall(
            libc::SYS_close_range,
            first as libc::c_ulong,
            last as libc::c_ulong,
            flags as libc::c_ulong,
        )
    };
    if r < 0 {
        Err(errno())
    } else {
        Ok(())
    }
}

/// `open("/proc/self/fd", O_RDONLY | O_DIRECTORY | O_CLOEXEC)`.
pub fn open_proc_self_fd(_s: &mut Sys) -> Result<i32, i32> {
    let path = b"/proc/self/fd\0".as_ptr() as *const c_char;
    let flags = libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC;
    check_i32(unsafe { libc::open(path, flags) })
}

/// `syscall(SYS_getdents64, dirfd, buf, 256)`.
pub fn getdents64(_s: &mut Sys, dirfd: i32, buf: &mut [u8; 256]) -> Result<usize, i32> {
    let r = unsafe {
        libc::syscall(
            libc::SYS_getdents64,
            dirfd as libc::c_long,
            buf.as_mut_ptr() as *mut libc::c_void,
            256usize,
        )
    };
    check_usize(r as isize)
}

/// `read(fd, buf, 1)`.
pub fn read1(_s: &mut Sys, fd: i32, buf: &mut [u8; 1]) -> Result<usize, i32> {
    check_usize(unsafe { libc::read(fd, buf.as_mut_ptr() as *mut libc::c_void, 1) })
}

/// `write(fd, buf, buf.len())`.
pub fn write(_s: &mut Sys, fd: i32, buf: &[u8]) -> Result<usize, i32> {
    check_usize(unsafe { libc::write(fd, buf.as_ptr() as *const libc::c_void, buf.len()) })
}

/// `chdir(path)`.
pub fn chdir(_s: &mut Sys, path: &CStr) -> Result<(), i32> {
    check_unit(unsafe { libc::chdir(path.ptr) })
}

/// `execve(path, argv, envp)`, returning `errno` on failure.
pub fn execve(_s: &mut Sys, path: &CStr, argv: &CStrArray, envp: &CStrArray) -> i32 {
    unsafe {
        libc::execve(path.ptr, argv.ptr, envp.ptr);
    }
    errno()
}

/// `_exit(code)`.
pub fn exit(_s: &mut Sys, code: i32) {
    unsafe { libc::_exit(code) }
}

#[cfg(feature = "standalone")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    unsafe { libc::_exit(127) }
}
