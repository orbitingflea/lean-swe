//! Trusted 1-syscall Linux boundary (`--opaque psandbox_init::init_sys`).

use core::ffi::c_char;

const LANDLOCK_CREATE_RULESET_VERSION: u32 = 1;
const LANDLOCK_RULE_PATH_BENEATH: u32 = 1;
const LANDLOCK_RULE_NET_PORT: u32 = 2;

#[repr(C)]
struct IfreqFlags {
    ifr_name: [u8; 16],
    ifr_flags: i16,
    ifr_pad: [u8; 22],
}

#[repr(C, align(8))]
struct CmsgRights32 {
    cmsg_hdr: libc::cmsghdr,
    fds: [i32; 32],
}

#[repr(C)]
struct LandlockRulesetAttr {
    handled_access_fs: u64,
    handled_access_net: u64,
}

#[repr(C, packed)]
struct LandlockPathBeneathAttr {
    allowed_access: u64,
    parent_fd: i32,
}

#[repr(C)]
struct LandlockNetPortAttr {
    allowed_access: u64,
    port: u64,
}

#[repr(C)]
struct SockFprog {
    len: u16,
    filter: *const u32,
}

/// Capability token representing the single-threaded container `psandbox-init` OS state.
pub struct Sys {
    argc: usize,
    argv: *const *const c_char,
}

impl Sys {
    /// Wrap the C `main(argc, argv)` vector into the root OS state token.
    ///
    /// # Safety
    /// Must be called once at process startup with the valid `(argc, argv)` from `crt1.o`.
    pub unsafe fn from_main_args(argc: i32, argv: *const *const c_char) -> Sys {
        Sys {
            argc: if argc > 0 { argc as usize } else { 0 },
            argv,
        }
    }
}

/// Owned byte buffer holding the serialized `LSWP0002` plan read from `plan_fd`.
pub struct PlanBuf {
    ptr: *mut u8,
    len: usize,
    cap: usize,
}

/// Single-slab pre-fork arena holding guest `program`, `cwd`, `argv`, and `envp` C strings.
pub struct ExecTable {
    slab: *mut u8,
    str_off: usize,
    str_len: usize,
    str_cap: usize,
    argv: *mut *const c_char,
    argc: u32,
    envp: *mut *mut c_char,
    envc: u32,
    program: *const c_char,
    cwd: *const c_char,
}

#[inline(always)]
fn errno() -> i32 {
    let e = unsafe { *libc::__errno_location() };
    if e > 0 { e } else { 5 }
}

#[inline(always)]
fn check_unit(r: libc::c_int) -> Result<(), i32> {
    if r < 0 { Err(errno()) } else { Ok(()) }
}

#[inline(always)]
fn check_i32(r: libc::c_int) -> Result<i32, i32> {
    if r < 0 { Err(errno()) } else { Ok(r) }
}

#[inline(always)]
fn check_usize(r: isize) -> Result<usize, i32> {
    if r < 0 { Err(errno()) } else { Ok(r as usize) }
}

/// Copy `argv[idx]` into `buf` when its length is `<= 64`, returning `len` (`0` if missing/null, sentinel `65` if `> 64`).
pub fn read_cli_arg(s: &mut Sys, idx: usize, buf: &mut [u8; 64]) -> usize {
    if idx >= s.argc || s.argv.is_null() {
        return 0;
    }
    let p = unsafe { *s.argv.add(idx) };
    if p.is_null() {
        return 0;
    }
    let n = unsafe { libc::strlen(p) };
    if n <= 64 {
        unsafe {
            core::ptr::copy_nonoverlapping(p as *const u8, buf.as_mut_ptr(), n);
        }
        n
    } else {
        65
    }
}

/// `fcntl(fd, F_GETFD, 0)`.
pub fn fcntl_getfd(_s: &mut Sys, fd: i32) -> Result<i32, i32> {
    check_i32(unsafe { libc::fcntl(fd, libc::F_GETFD, 0 as libc::c_int) })
}

/// `fcntl(fd, F_SETFD, flags)`.
pub fn fcntl_setfd(_s: &mut Sys, fd: i32, flags: i32) -> Result<(), i32> {
    check_unit(unsafe { libc::fcntl(fd, libc::F_SETFD, flags as libc::c_int) })
}

/// `close(fd)`.
pub fn close_fd(_s: &mut Sys, fd: i32) -> Result<(), i32> {
    check_unit(unsafe { libc::close(fd) })
}

/// `read(fd, buf, 1)`.
pub fn read1(_s: &mut Sys, fd: i32, buf: &mut [u8; 1]) -> Result<usize, i32> {
    check_usize(unsafe { libc::read(fd, buf.as_mut_ptr() as *mut libc::c_void, 1) })
}

/// `read(fd, &mut buf[off..8])` for the 8-byte `exec_err_pipe` status frame.
pub fn read_status_tail(_s: &mut Sys, fd: i32, buf: &mut [u8; 8], off: usize) -> Result<usize, i32> {
    if off >= 8 {
        return Ok(0);
    }
    let ptr = unsafe { buf.as_mut_ptr().add(off) as *mut libc::c_void };
    check_usize(unsafe { libc::read(fd, ptr, 8 - off) })
}

/// `write(fd, buf, buf.len())`.
pub fn write_fd(_s: &mut Sys, fd: i32, buf: &[u8]) -> Result<usize, i32> {
    check_usize(unsafe { libc::write(fd, buf.as_ptr() as *const libc::c_void, buf.len()) })
}

/// Allocate an empty `PlanBuf` with initial byte capacity `cap`.
pub fn plan_buf_new(_s: &mut Sys, cap: usize) -> Result<PlanBuf, i32> {
    let alloc_cap = if cap > 0 { cap } else { 1 };
    let ptr = unsafe { libc::malloc(alloc_cap) as *mut u8 };
    if ptr.is_null() {
        Err(libc::ENOMEM)
    } else {
        Ok(PlanBuf {
            ptr,
            len: 0,
            cap: alloc_cap,
        })
    }
}

/// Grow `buf` to `new_cap` bytes via `realloc`.
pub fn plan_buf_reserve(_s: &mut Sys, buf: &mut PlanBuf, new_cap: usize) -> Result<(), i32> {
    if new_cap <= buf.cap {
        return Ok(());
    }
    let nb = unsafe { libc::realloc(buf.ptr as *mut libc::c_void, new_cap) as *mut u8 };
    if nb.is_null() {
        Err(libc::ENOMEM)
    } else {
        buf.ptr = nb;
        buf.cap = new_cap;
        Ok(())
    }
}

/// Read one chunk from `fd` into the spare tail of `buf`.
pub fn plan_buf_read_once(_s: &mut Sys, fd: i32, buf: &mut PlanBuf) -> Result<usize, i32> {
    if buf.len >= buf.cap {
        return Ok(0);
    }
    let dst = unsafe { buf.ptr.add(buf.len) as *mut libc::c_void };
    let n = check_usize(unsafe { libc::read(fd, dst, buf.cap - buf.len) })?;
    buf.len += n;
    Ok(n)
}

/// Current byte length of `buf`.
pub fn plan_buf_len(buf: &PlanBuf) -> usize {
    buf.len
}

/// Current byte capacity of `buf`.
pub fn plan_buf_cap(buf: &PlanBuf) -> usize {
    buf.cap
}

/// Borrow the initialized bytes of `buf`.
pub fn plan_buf_slice(buf: &PlanBuf) -> &[u8] {
    if buf.len == 0 {
        &[]
    } else {
        unsafe { core::slice::from_raw_parts(buf.ptr, buf.len) }
    }
}

/// Free `buf`.
pub fn plan_buf_free(_s: &mut Sys, buf: PlanBuf) {
    if !buf.ptr.is_null() {
        unsafe {
            libc::free(buf.ptr as *mut libc::c_void);
        }
    }
}

/// `prctl(PR_SET_PDEATHSIG, SIGKILL)`.
pub fn prctl_pdeathsig_kill(_s: &mut Sys) -> Result<(), i32> {
    check_unit(unsafe { libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL, 0usize, 0usize, 0usize) })
}

/// `prctl(PR_SET_CHILD_SUBREAPER, 1)`.
pub fn prctl_subreaper(_s: &mut Sys) -> Result<(), i32> {
    check_unit(unsafe { libc::prctl(libc::PR_SET_CHILD_SUBREAPER, 1usize, 0usize, 0usize, 0usize) })
}

/// `prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)`.
pub fn prctl_no_new_privs(_s: &mut Sys) -> Result<(), i32> {
    check_unit(unsafe { libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1usize, 0usize, 0usize, 0usize) })
}

/// `setrlimit(RLIMIT_CORE, {0, 0})`.
pub fn setrlimit_core_zero(_s: &mut Sys) -> Result<(), i32> {
    let rl = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    check_unit(unsafe { libc::setrlimit(libc::RLIMIT_CORE, &rl) })
}

/// `setrlimit(RLIMIT_FSIZE, {max_bytes, max_bytes})`.
pub fn setrlimit_fsize(_s: &mut Sys, max_bytes: u64) -> Result<(), i32> {
    let lim = max_bytes as libc::rlim_t;
    let rl = libc::rlimit {
        rlim_cur: lim,
        rlim_max: lim,
    };
    check_unit(unsafe { libc::setrlimit(libc::RLIMIT_FSIZE, &rl) })
}

/// `socket(AF_INET, SOCK_DGRAM | SOCK_CLOEXEC, 0)`.
pub fn socket_udp_cloexec(_s: &mut Sys) -> Result<i32, i32> {
    check_i32(unsafe { libc::socket(libc::AF_INET, libc::SOCK_DGRAM | libc::SOCK_CLOEXEC, 0) })
}

fn lo_ifreq(flags: i16) -> IfreqFlags {
    let mut name = [0u8; 16];
    name[0] = b'l';
    name[1] = b'o';
    IfreqFlags {
        ifr_name: name,
        ifr_flags: flags,
        ifr_pad: [0u8; 22],
    }
}

/// `ioctl(sock_fd, SIOCGIFFLAGS, "lo")`.
pub fn ioctl_get_lo_flags(_s: &mut Sys, sock_fd: i32) -> Result<i16, i32> {
    let mut ifr = lo_ifreq(0);
    check_unit(unsafe { libc::ioctl(sock_fd, libc::SIOCGIFFLAGS, &mut ifr as *mut IfreqFlags) })?;
    Ok(ifr.ifr_flags)
}

/// `ioctl(sock_fd, SIOCSIFFLAGS, "lo", flags)`.
pub fn ioctl_set_lo_flags(_s: &mut Sys, sock_fd: i32, flags: i16) -> Result<(), i32> {
    let ifr = lo_ifreq(flags);
    check_unit(unsafe { libc::ioctl(sock_fd, libc::SIOCSIFFLAGS, &ifr as *const IfreqFlags) })
}

/// `socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0)`.
pub fn socket_tcp_nonblock_cloexec(_s: &mut Sys) -> Result<i32, i32> {
    let ty = libc::SOCK_STREAM | libc::SOCK_NONBLOCK | libc::SOCK_CLOEXEC;
    check_i32(unsafe { libc::socket(libc::AF_INET, ty, 0) })
}

/// `setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, 1)`.
pub fn setsockopt_reuseaddr(_s: &mut Sys, fd: i32) -> Result<(), i32> {
    let one: libc::c_int = 1;
    let rc = unsafe {
        libc::setsockopt(
            fd,
            libc::SOL_SOCKET,
            libc::SO_REUSEADDR,
            &one as *const libc::c_int as *const libc::c_void,
            core::mem::size_of::<libc::c_int>() as libc::socklen_t,
        )
    };
    check_unit(rc)
}

/// `bind(fd, 127.0.0.1:port)`.
pub fn bind_loopback_v4(_s: &mut Sys, fd: i32, port: u16) -> Result<(), i32> {
    let sa = libc::sockaddr_in {
        sin_family: libc::AF_INET as libc::sa_family_t,
        sin_port: port.to_be(),
        sin_addr: libc::in_addr {
            s_addr: 0x7f00_0001u32.to_be(),
        },
        sin_zero: [0u8; 8],
    };
    let rc = unsafe {
        libc::bind(
            fd,
            &sa as *const libc::sockaddr_in as *const libc::sockaddr,
            core::mem::size_of::<libc::sockaddr_in>() as libc::socklen_t,
        )
    };
    check_unit(rc)
}

/// `listen(fd, backlog)`.
pub fn listen_socket(_s: &mut Sys, fd: i32, backlog: i32) -> Result<(), i32> {
    check_unit(unsafe { libc::listen(fd, backlog) })
}

/// Send `fds[start .. start + batch]` (`1 <= batch <= 32`) via `SCM_RIGHTS` over `ctrl_fd`.
pub fn sendmsg_scm_batch(
    _s: &mut Sys,
    ctrl_fd: i32,
    fds: &[i32; 1024],
    start: usize,
    batch: usize,
) -> Result<usize, i32> {
    if batch == 0 || batch > 32 || start > 1024 - batch {
        return Err(libc::EINVAL);
    }
    let mut dummy: u8 = 1;
    let mut iov = libc::iovec {
        iov_base: &mut dummy as *mut u8 as *mut libc::c_void,
        iov_len: 1,
    };
    let data_bytes = (batch * 4) as u32;
    let cmsg_len = unsafe { libc::CMSG_LEN(data_bytes) } as usize;
    let cmsg_space = unsafe { libc::CMSG_SPACE(data_bytes) } as usize;
    let mut cbuf: CmsgRights32 = unsafe { core::mem::zeroed() };
    cbuf.cmsg_hdr.cmsg_len = cmsg_len as _;
    cbuf.cmsg_hdr.cmsg_level = libc::SOL_SOCKET;
    cbuf.cmsg_hdr.cmsg_type = libc::SCM_RIGHTS;
    unsafe {
        core::ptr::copy_nonoverlapping(fds.as_ptr().add(start), cbuf.fds.as_mut_ptr(), batch);
    }
    let mut msg: libc::msghdr = unsafe { core::mem::zeroed() };
    msg.msg_iov = &mut iov;
    msg.msg_iovlen = 1;
    msg.msg_control = &mut cbuf as *mut CmsgRights32 as *mut libc::c_void;
    msg.msg_controllen = cmsg_space as _;
    check_usize(unsafe { libc::sendmsg(ctrl_fd, &msg, libc::MSG_NOSIGNAL) })
}

/// Query the kernel Landlock ABI version (`SYS_landlock_create_ruleset`).
pub fn landlock_abi_version(_s: &mut Sys) -> Result<i32, i32> {
    let r = unsafe {
        libc::syscall(
            libc::SYS_landlock_create_ruleset,
            core::ptr::null::<libc::c_void>(),
            0usize,
            LANDLOCK_CREATE_RULESET_VERSION,
        )
    };
    if r < 0 {
        Err(errno())
    } else {
        Ok(r as i32)
    }
}

/// Create a Landlock ruleset covering `(handled_fs, handled_net)`.
pub fn landlock_create_ruleset(
    _s: &mut Sys,
    handled_fs: u64,
    handled_net: u64,
) -> Result<i32, i32> {
    let attr = LandlockRulesetAttr {
        handled_access_fs: handled_fs,
        handled_access_net: handled_net,
    };
    let r = unsafe {
        libc::syscall(
            libc::SYS_landlock_create_ruleset,
            &attr as *const LandlockRulesetAttr,
            16usize,
            0u32,
        )
    };
    if r < 0 {
        Err(errno())
    } else {
        Ok(r as i32)
    }
}

/// `open(path, O_PATH | O_CLOEXEC)` for a NUL-free byte slice `< 4096` bytes.
pub fn open_path_cloexec(_s: &mut Sys, path: &[u8]) -> Result<i32, i32> {
    let n = path.len();
    if n >= 4096 {
        return Err(libc::ENAMETOOLONG);
    }
    let mut cbuf = [0u8; 4096];
    unsafe {
        core::ptr::copy_nonoverlapping(path.as_ptr(), cbuf.as_mut_ptr(), n);
    }
    cbuf[n] = 0;
    check_i32(unsafe { libc::open(cbuf.as_ptr() as *const c_char, libc::O_PATH | libc::O_CLOEXEC) })
}

/// Query whether open descriptor `fd` refers to a directory via `fstat`.
pub fn fd_is_dir(_s: &mut Sys, fd: i32) -> Result<bool, i32> {
    let mut st: libc::stat = unsafe { core::mem::zeroed() };
    check_unit(unsafe { libc::fstat(fd, &mut st) })?;
    Ok((st.st_mode & libc::S_IFMT) == libc::S_IFDIR)
}

/// Add a `LANDLOCK_RULE_PATH_BENEATH` rule on `parent_fd` to `rs`.
pub fn landlock_add_path_rule(
    _s: &mut Sys,
    rs: i32,
    parent_fd: i32,
    allowed_access: u64,
) -> Result<(), i32> {
    let pb = LandlockPathBeneathAttr {
        allowed_access,
        parent_fd,
    };
    let r = unsafe {
        libc::syscall(
            libc::SYS_landlock_add_rule,
            rs as libc::c_int,
            LANDLOCK_RULE_PATH_BENEATH,
            &pb as *const LandlockPathBeneathAttr,
            0u32,
        )
    };
    if r < 0 { Err(errno()) } else { Ok(()) }
}

/// Add a `LANDLOCK_RULE_NET_PORT` rule on TCP `port` to `rs`.
pub fn landlock_add_net_port_rule(
    _s: &mut Sys,
    rs: i32,
    port: u16,
    allowed_access: u64,
) -> Result<(), i32> {
    let np = LandlockNetPortAttr {
        allowed_access,
        port: port as u64,
    };
    let r = unsafe {
        libc::syscall(
            libc::SYS_landlock_add_rule,
            rs as libc::c_int,
            LANDLOCK_RULE_NET_PORT,
            &np as *const LandlockNetPortAttr,
            0u32,
        )
    };
    if r < 0 { Err(errno()) } else { Ok(()) }
}

/// Enforce Landlock ruleset `rs` on the calling single-threaded process.
pub fn landlock_restrict_self(_s: &mut Sys, rs: i32) -> Result<(), i32> {
    let r = unsafe { libc::syscall(libc::SYS_landlock_restrict_self, rs as libc::c_int, 0u32) };
    if r < 0 { Err(errno()) } else { Ok(()) }
}

fn copy_seccomp_aligned(
    filter_bytes: &[u8],
    insn_count: u32,
    aligned: &mut [u32; 320],
) -> Result<(), i32> {
    if insn_count == 0 || insn_count > 160 {
        return Err(libc::EINVAL);
    }
    let byte_len = (insn_count as usize) * 8;
    if filter_bytes.len() != byte_len {
        return Err(libc::EINVAL);
    }
    unsafe {
        core::ptr::copy_nonoverlapping(
            filter_bytes.as_ptr(),
            aligned.as_mut_ptr() as *mut u8,
            byte_len,
        );
    }
    Ok(())
}

/// `syscall(SYS_seccomp, SECCOMP_SET_MODE_FILTER, 0, &prog)`.
pub fn seccomp_set_mode_filter(
    _s: &mut Sys,
    filter_bytes: &[u8],
    insn_count: u32,
) -> Result<(), i32> {
    let mut aligned = [0u32; 320];
    copy_seccomp_aligned(filter_bytes, insn_count, &mut aligned)?;
    let prog = SockFprog {
        len: insn_count as u16,
        filter: aligned.as_ptr(),
    };
    let r = unsafe {
        libc::syscall(
            libc::SYS_seccomp,
            libc::SECCOMP_SET_MODE_FILTER,
            0u32,
            &prog as *const SockFprog,
        )
    };
    if r < 0 { Err(errno()) } else { Ok(()) }
}

/// `prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &prog, 0, 0)`.
pub fn prctl_set_seccomp_filter(
    _s: &mut Sys,
    filter_bytes: &[u8],
    insn_count: u32,
) -> Result<(), i32> {
    let mut aligned = [0u32; 320];
    copy_seccomp_aligned(filter_bytes, insn_count, &mut aligned)?;
    let prog = SockFprog {
        len: insn_count as u16,
        filter: aligned.as_ptr(),
    };
    let r = unsafe {
        libc::prctl(
            libc::PR_SET_SECCOMP,
            libc::SECCOMP_MODE_FILTER,
            &prog as *const SockFprog,
            0usize,
            0usize,
        )
    };
    check_unit(r)
}

/// Allocate the single-slab pre-fork guest `ExecTable`.
pub fn exec_table_new(
    _s: &mut Sys,
    argc: u32,
    envc: u32,
    str_cap: usize,
) -> Result<ExecTable, i32> {
    let ptr_size = core::mem::size_of::<*const c_char>();
    let n_argv = (argc as usize).saturating_add(2);
    let n_envp = (envc as usize).saturating_add(1);
    let ptr_bytes = n_argv.saturating_add(n_envp).saturating_mul(ptr_size);
    let alloc_cap = if str_cap > 0 { str_cap } else { 1 };
    let total = ptr_bytes.checked_add(alloc_cap).ok_or(libc::ENOMEM)?;
    let slab = unsafe { libc::calloc(1, total) as *mut u8 };
    if slab.is_null() {
        return Err(libc::ENOMEM);
    }
    let argv = slab as *mut *const c_char;
    let envp = unsafe { slab.add(n_argv * ptr_size) as *mut *mut c_char };
    Ok(ExecTable {
        slab,
        str_off: ptr_bytes,
        str_len: 0,
        str_cap: alloc_cap,
        argv,
        argc,
        envp,
        envc,
        program: core::ptr::null(),
        cwd: core::ptr::null(),
    })
}

fn push_cstr_bytes(tbl: &mut ExecTable, bytes: &[u8]) -> Result<*mut c_char, i32> {
    let n = bytes.len();
    if n >= tbl.str_cap - tbl.str_len {
        return Err(libc::ENOMEM);
    }
    let dst = unsafe { tbl.slab.add(tbl.str_off + tbl.str_len) };
    if n > 0 {
        unsafe {
            core::ptr::copy_nonoverlapping(bytes.as_ptr(), dst, n);
        }
    }
    unsafe {
        *dst.add(n) = 0;
    }
    tbl.str_len += n + 1;
    Ok(dst as *mut c_char)
}

/// Store `program` (`argv[0]`) in `tbl`.
pub fn exec_table_set_program(
    _s: &mut Sys,
    tbl: &mut ExecTable,
    prog: &[u8],
) -> Result<(), i32> {
    let p = push_cstr_bytes(tbl, prog)? as *const c_char;
    tbl.program = p;
    unsafe {
        *tbl.argv = p;
    }
    Ok(())
}

/// Store `cwd` in `tbl`.
pub fn exec_table_set_cwd(_s: &mut Sys, tbl: &mut ExecTable, cwd: &[u8]) -> Result<(), i32> {
    let p = push_cstr_bytes(tbl, cwd)? as *const c_char;
    tbl.cwd = p;
    Ok(())
}

/// Store `argv[idx + 1]` in `tbl`.
pub fn exec_table_set_arg(
    _s: &mut Sys,
    tbl: &mut ExecTable,
    idx: u32,
    arg: &[u8],
) -> Result<(), i32> {
    if idx >= tbl.argc {
        return Err(libc::EINVAL);
    }
    let p = push_cstr_bytes(tbl, arg)? as *const c_char;
    unsafe {
        *tbl.argv.add((idx as usize) + 1) = p;
    }
    Ok(())
}

/// Store `"key=val\0"` at `envp[idx]` in `tbl`.
pub fn exec_table_set_env(
    _s: &mut Sys,
    tbl: &mut ExecTable,
    idx: u32,
    key: &[u8],
    val: &[u8],
) -> Result<(), i32> {
    if idx >= tbl.envc {
        return Err(libc::EINVAL);
    }
    let kl = key.len();
    let vl = val.len();
    let need = kl.saturating_add(vl).saturating_add(2);
    if need > tbl.str_cap - tbl.str_len {
        return Err(libc::ENOMEM);
    }
    let dst = unsafe { tbl.slab.add(tbl.str_off + tbl.str_len) };
    unsafe {
        if kl > 0 {
            core::ptr::copy_nonoverlapping(key.as_ptr(), dst, kl);
        }
        *dst.add(kl) = b'=';
        if vl > 0 {
            core::ptr::copy_nonoverlapping(val.as_ptr(), dst.add(kl + 1), vl);
        }
        *dst.add(kl + 1 + vl) = 0;
        *tbl.envp.add(idx as usize) = dst as *mut c_char;
    }
    tbl.str_len += need;
    Ok(())
}

/// `pipe2(O_CLOEXEC)`.
pub fn pipe2_cloexec(_s: &mut Sys) -> Result<(i32, i32), i32> {
    let mut p: [libc::c_int; 2] = [-1, -1];
    check_unit(unsafe { libc::pipe2(p.as_mut_ptr(), libc::O_CLOEXEC) })?;
    Ok((p[0], p[1]))
}

/// `fork()`.
pub fn fork_proc(_s: &mut Sys) -> Result<i32, i32> {
    check_i32(unsafe { libc::fork() })
}

/// `syscall(SYS_close_range, first, last, 0)`.
pub fn close_range(_s: &mut Sys, first: u32, last: u32) -> Result<(), i32> {
    let r = unsafe {
        libc::syscall(
            libc::SYS_close_range,
            first as libc::c_ulong,
            last as libc::c_ulong,
            0 as libc::c_ulong,
        )
    };
    if r < 0 { Err(errno()) } else { Ok(()) }
}

/// `open("/proc/self/fd", O_RDONLY | O_DIRECTORY | O_CLOEXEC)`.
pub fn open_proc_self_fd(_s: &mut Sys) -> Result<i32, i32> {
    let path = b"/proc/self/fd\0".as_ptr() as *const c_char;
    let flags = libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC;
    check_i32(unsafe { libc::open(path, flags) })
}

/// `syscall(SYS_getdents64, dirfd, buf, 256)`.
pub fn getdents64_chunk(_s: &mut Sys, dirfd: i32, buf: &mut [u8; 256]) -> Result<usize, i32> {
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

/// Reset `SIGPIPE` to `SIG_DFL`.
pub fn reset_sigpipe_dfl(_s: &mut Sys) {
    unsafe {
        let _ = libc::signal(libc::SIGPIPE, libc::SIG_DFL);
    }
}

/// `clearenv()` clearing inherited environment variables in the forked guest child.
pub fn clearenv_guest(_s: &mut Sys) -> Result<(), i32> {
    let rc = unsafe { libc::clearenv() };
    if rc != 0 {
        let e = unsafe { *libc::__errno_location() };
        Err(if e > 0 { e } else { libc::ENOMEM })
    } else {
        Ok(())
    }
}

/// `putenv(tbl.envp[idx])` installing one pre-built `"key=val\0"` entry into `environ`.
pub fn putenv_guest_entry(_s: &mut Sys, tbl: &ExecTable, idx: u32) -> Result<(), i32> {
    if idx >= tbl.envc {
        return Err(libc::EINVAL);
    }
    let kv = unsafe { *tbl.envp.add(idx as usize) };
    if kv.is_null() {
        return Err(libc::EINVAL);
    }
    let rc = unsafe { libc::putenv(kv) };
    if rc != 0 { Err(errno()) } else { Ok(()) }
}

/// `chdir(tbl.cwd)`.
pub fn chdir_guest(_s: &mut Sys, tbl: &ExecTable) -> Result<(), i32> {
    check_unit(unsafe { libc::chdir(tbl.cwd) })
}

/// `execvp(tbl.program, tbl.argv)`, returning positive `errno` on failure.
pub fn execvp_guest(_s: &mut Sys, tbl: &ExecTable) -> i32 {
    unsafe {
        let _ = libc::execvp(tbl.program, tbl.argv);
    }
    errno()
}

/// Blocking `waitpid(pid, &mut status, 0)`.
pub fn waitpid_blocking(_s: &mut Sys, pid: i32) -> Result<(i32, i32), i32> {
    let mut st: libc::c_int = 0;
    let r = check_i32(unsafe { libc::waitpid(pid, &mut st, 0) })?;
    Ok((r, st))
}

/// Best-effort `kill(-1, SIGKILL)` inside the PID namespace.
pub fn kill_all_sigkill(_s: &mut Sys) {
    unsafe {
        let _ = libc::kill(-1, libc::SIGKILL);
    }
}

/// Terminate the process immediately via `_exit(code)`.
pub fn exit_now(_s: &mut Sys, code: i32) {
    unsafe { libc::_exit(code) }
}

#[cfg(feature = "standalone")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    unsafe { libc::_exit(127) }
}
