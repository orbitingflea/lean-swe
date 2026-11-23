//! Proved zero-allocation `LSWP0002` wire plan decoder and bounds checker.
#![forbid(unsafe_code)]

/// Linux `EINVAL` error number (`22`).
pub const EINVAL: i32 = 22;

/// Maximum serialized plan payload accepted from `plan_fd` (`16 MiB`).
pub const PS_INIT_MAX_PLAN_BYTES: usize = 16 * 1024 * 1024;
/// Maximum `seccomp` classic BPF filter length (`160` 8-byte instructions).
pub const PS_SECCOMP_MAX_INSNS: u32 = 160;
/// Maximum `argc` count (`65,536`).
pub const MAX_ARGC: u32 = 65_536;
/// Maximum `envc` count (`65,536`).
pub const MAX_ENVC: u32 = 65_536;
/// Maximum system preset entry count (`1,024`).
pub const MAX_SYS_ENTRIES: u32 = 1_024;
/// Maximum `/etc` preset path count (`1,024`).
pub const MAX_ETC_PATHS: u32 = 1_024;
/// Maximum masked preset path count (`1,024`).
pub const MAX_MASK_PATHS: u32 = 1_024;
/// Maximum user mount count (`4,096`).
pub const MAX_MOUNTS: u32 = 4_096;
/// Maximum port-forward count (`1,024`).
pub const MAX_PORT_FORWARDS: u32 = 1_024;

/// Validated NUL-free byte slice span `data[start .. start + len]`.
#[derive(Clone, Copy)]
pub struct Span {
    pub start: usize,
    pub len: usize,
}

/// Check whether `sp` lies within `0..total_len` without arithmetic overflow.
pub fn span_end_ok(sp: Span, total_len: usize) -> bool {
    sp.start <= total_len && sp.len <= total_len - sp.start
}

/// Decoded classic BPF `sock_filter` instruction (`8` bytes on the wire).
#[derive(Clone, Copy)]
pub struct SockFilter {
    pub code: u16,
    pub jt: u8,
    pub jf: u8,
    pub k: u32,
}

/// Validated `LSWP0002` fixed header flags and limits consumed by `psandbox-init`.
#[derive(Clone, Copy)]
pub struct PlanHeader {
    pub allow_box_localhost: bool,
    pub has_file_size_max: bool,
    pub file_size_max_bytes: u64,
    pub landlock_min_abi: u32,
}

/// Validated section offsets and counts into an `LSWP0002` plan byte buffer.
#[derive(Clone, Copy)]
pub struct PlanView {
    pub header: PlanHeader,
    pub program: Span,
    pub cwd: Span,
    pub argc: u32,
    pub args_pos: usize,
    pub envc: u32,
    pub env_pos: usize,
    pub n_sys: u32,
    pub sys_pos: usize,
    pub n_etc: u32,
    pub etc_pos: usize,
    pub n_masks: u32,
    pub masks_pos: usize,
    pub n_mounts: u32,
    pub mounts_pos: usize,
    pub n_fwds: u32,
    pub fwds_pos: usize,
    pub seccomp_n: u32,
    pub seccomp_pos: usize,
}

/// Check the 8-byte `"LSWP0002"` magic prefix and return cursor `8`.
pub fn check_magic(data: &[u8]) -> Result<usize, i32> {
    if data.len() < 8 {
        return Err(EINVAL);
    }
    let m = b"LSWP0002";
    let mut i: usize = 0;
    let mut ok: bool = true;
    while i < 8 {
        if data[i] != m[i] {
            ok = false;
            break;
        }
        i += 1;
    }
    if ok {
        Ok(8)
    } else {
        Err(EINVAL)
    }
}

/// Read 1 byte at `pos`.
pub fn read_u8(data: &[u8], pos: usize) -> Result<(u8, usize), i32> {
    if pos >= data.len() {
        Err(EINVAL)
    } else {
        Ok((data[pos], pos + 1))
    }
}

/// Read a 2-byte little-endian `u16` at `pos`.
pub fn read_u16_le(data: &[u8], pos: usize) -> Result<(u16, usize), i32> {
    if data.len() < 2 || pos > data.len() - 2 {
        return Err(EINVAL);
    }
    let b0 = data[pos] as u16;
    let b1 = (data[pos + 1] as u16) << 8;
    Ok((b0 | b1, pos + 2))
}

/// Read a 4-byte little-endian `u32` at `pos`.
pub fn read_u32_le(data: &[u8], pos: usize) -> Result<(u32, usize), i32> {
    if data.len() < 4 || pos > data.len() - 4 {
        return Err(EINVAL);
    }
    let b0 = data[pos] as u32;
    let b1 = (data[pos + 1] as u32) << 8;
    let b2 = (data[pos + 2] as u32) << 16;
    let b3 = (data[pos + 3] as u32) << 24;
    Ok((b0 | b1 | b2 | b3, pos + 4))
}

/// Read an 8-byte little-endian `u64` at `pos`.
pub fn read_u64_le(data: &[u8], pos: usize) -> Result<(u64, usize), i32> {
    let (lo, p1) = read_u32_le(data, pos)?;
    let (hi, p2) = read_u32_le(data, p1)?;
    Ok(((lo as u64) | ((hi as u64) << 32), p2))
}

/// Return `true` iff `data[start..end]` (`end <= data.len()`) contains a `0` byte.
pub fn has_nul_in_range(data: &[u8], start: usize, end: usize) -> bool {
    let mut i: usize = start;
    let mut found: bool = false;
    while i < end && i < data.len() {
        if data[i] == 0 {
            found = true;
            break;
        }
        i += 1;
    }
    found
}

/// Read a 32-bit length-prefixed NUL-free byte span starting at `pos`.
pub fn read_str_span(data: &[u8], pos: usize) -> Result<(Span, usize), i32> {
    let (slen_u32, p1) = read_u32_le(data, pos)?;
    let slen = slen_u32 as usize;
    if slen > data.len() - p1 {
        return Err(EINVAL);
    }
    let end = p1 + slen;
    if has_nul_in_range(data, p1, end) {
        return Err(EINVAL);
    }
    Ok((Span { start: p1, len: slen }, end))
}

/// Validate the first 5 mandatory boolean flags (`empty_root..direct_cg`) and `landlock_min_abi >= 4`.
pub fn parse_header_part1(data: &[u8], pos: usize) -> Result<(u32, usize), i32> {
    let (empty_root, p1) = read_u8(data, pos)?;
    let (unshare_all, p2) = read_u8(data, p1)?;
    let (mount_proc, p3) = read_u8(data, p2)?;
    let (mount_dev, p4) = read_u8(data, p3)?;
    let (direct_cg, p5) = read_u8(data, p4)?;
    let (ll_abi, p6) = read_u32_le(data, p5)?;
    let flags_ok = (empty_root != 0)
        & (unshare_all != 0)
        & (mount_proc != 0)
        & (mount_dev != 0)
        & (direct_cg != 0)
        & (ll_abi >= 4);
    if flags_ok {
        Ok((ll_abi, p6))
    } else {
        Err(EINVAL)
    }
}

/// Validate `allow_box_localhost` and the 9 mandatory security boolean flags (`block_unix..clean_env`).
pub fn parse_header_part2(data: &[u8], pos: usize) -> Result<(bool, usize), i32> {
    let (allow_lo, p1) = read_u8(data, pos)?;
    let (block_unix, p2) = read_u8(data, p1)?;
    let (allow_pair, p3) = read_u8(data, p2)?;
    let (clone3_enosys, p4) = read_u8(data, p3)?;
    let (seccomp_deny, p5) = read_u8(data, p4)?;
    let (no_new_privs, p6) = read_u8(data, p5)?;
    let (rlimit_core0, p7) = read_u8(data, p6)?;
    let (subreaper, p8) = read_u8(data, p7)?;
    let (clean_env, p9) = read_u8(data, p8)?;
    let flags_ok = (block_unix != 0)
        & (allow_pair != 0)
        & (clone3_enosys != 0)
        & (seccomp_deny != 0)
        & (no_new_privs != 0)
        & (rlimit_core0 != 0)
        & (subreaper != 0)
        & (clean_env != 0);
    if flags_ok {
        Ok((allow_lo != 0, p9))
    } else {
        Err(EINVAL)
    }
}

/// Parse the 44-byte resource-limits block (`timeout_ms`, `mem`, `pids`, `fsize`, `max_out`).
pub fn parse_header_limits(data: &[u8], pos: usize) -> Result<((bool, u64), usize), i32> {
    let (_timeout_ms, p1) = read_u64_le(data, pos)?;
    let (_has_mem, p2) = read_u8(data, p1)?;
    let (_mem_max, p3) = read_u64_le(data, p2)?;
    let (_has_pids, p4) = read_u8(data, p3)?;
    let (_pids_max, p5) = read_u64_le(data, p4)?;
    let (has_fsize, p6) = read_u8(data, p5)?;
    let (fsize_max, p7) = read_u64_le(data, p6)?;
    let (_has_out, p8) = read_u8(data, p7)?;
    let (_max_out, p9) = read_u64_le(data, p8)?;
    Ok(((has_fsize != 0, fsize_max), p9))
}

/// Parse the complete fixed `LSWP0002` header after the 8-byte magic prefix.
pub fn parse_header(data: &[u8], pos: usize) -> Result<(PlanHeader, usize), i32> {
    let (landlock_min_abi, p1) = parse_header_part1(data, pos)?;
    let (allow_box_localhost, p2) = parse_header_part2(data, p1)?;
    let ((has_file_size_max, file_size_max_bytes), p3) = parse_header_limits(data, p2)?;
    Ok((
        PlanHeader {
            allow_box_localhost,
            has_file_size_max,
            file_size_max_bytes,
            landlock_min_abi,
        },
        p3,
    ))
}

/// Validate `count` consecutive NUL-free strings starting at `pos`.
pub fn scan_str_list(data: &[u8], pos: usize, count: u32) -> Result<usize, i32> {
    let mut cur: usize = pos;
    let mut i: u32 = 0;
    let mut bad: bool = false;
    while i < count {
        match read_str_span(data, cur) {
            Ok((_sp, next_pos)) => {
                cur = next_pos;
                i += 1;
            }
            Err(_) => {
                bad = true;
                break;
            }
        }
    }
    if bad {
        Err(EINVAL)
    } else {
        Ok(cur)
    }
}

/// Validate `envc` consecutive `(key, val)` NUL-free string pairs starting at `pos`.
pub fn scan_env_list(data: &[u8], pos: usize, envc: u32) -> Result<usize, i32> {
    let mut cur: usize = pos;
    let mut i: u32 = 0;
    let mut bad: bool = false;
    while i < envc {
        match read_str_span(data, cur) {
            Ok((_ksp, p1)) => match read_str_span(data, p1) {
                Ok((_vsp, p2)) => {
                    cur = p2;
                    i += 1;
                }
                Err(_) => {
                    bad = true;
                    break;
                }
            },
            Err(_) => {
                bad = true;
                break;
            }
        }
    }
    if bad {
        Err(EINVAL)
    } else {
        Ok(cur)
    }
}

/// Parse one system preset entry at `pos`, returning `(tag, path_span, next_pos)`.
pub fn read_sys_entry(data: &[u8], pos: usize) -> Result<(u8, Span, usize), i32> {
    let (tag, p1) = read_u8(data, pos)?;
    let (path, p2) = read_str_span(data, p1)?;
    if tag == 1 {
        let (_target, p3) = read_str_span(data, p2)?;
        Ok((tag, path, p3))
    } else {
        Ok((tag, path, p2))
    }
}

/// Validate `n_sys` system preset entries.
pub fn scan_sys_entries(data: &[u8], pos: usize, n_sys: u32) -> Result<usize, i32> {
    let mut cur: usize = pos;
    let mut i: u32 = 0;
    let mut bad: bool = false;
    while i < n_sys {
        match read_sys_entry(data, cur) {
            Ok((_tag, _path, next_pos)) => {
                cur = next_pos;
                i += 1;
            }
            Err(_) => {
                bad = true;
                break;
            }
        }
    }
    if bad {
        Err(EINVAL)
    } else {
        Ok(cur)
    }
}

/// Parse one mount entry at `pos`, returning `(tag, box_path_span, next_pos)`.
pub fn read_mount_entry(data: &[u8], pos: usize) -> Result<(u8, Span, usize), i32> {
    let (tag, p1) = read_u8(data, pos)?;
    if tag == 0 || tag == 1 {
        let (_host_path, p2) = read_str_span(data, p1)?;
        let (box_path, p3) = read_str_span(data, p2)?;
        Ok((tag, box_path, p3))
    } else if tag == 2 {
        let (box_path, p2) = read_str_span(data, p1)?;
        Ok((tag, box_path, p2))
    } else {
        Err(EINVAL)
    }
}

/// Validate `n_mounts` mount entries (`tag` in `0..=2`).
pub fn scan_mounts(data: &[u8], pos: usize, n_mounts: u32) -> Result<usize, i32> {
    let mut cur: usize = pos;
    let mut i: u32 = 0;
    let mut bad: bool = false;
    while i < n_mounts {
        match read_mount_entry(data, cur) {
            Ok((_tag, _bp, next_pos)) => {
                cur = next_pos;
                i += 1;
            }
            Err(_) => {
                bad = true;
                break;
            }
        }
    }
    if bad {
        Err(EINVAL)
    } else {
        Ok(cur)
    }
}

/// Read the `idx`-th `(box_port, host_port)` pair starting at `fwds_pos`.
pub fn read_port_forward_at(data: &[u8], fwds_pos: usize, idx: u32) -> Result<(u16, u16), i32> {
    if idx >= MAX_PORT_FORWARDS {
        return Err(EINVAL);
    }
    let off = (idx as usize) * 4;
    if off > data.len() || fwds_pos > data.len() - off {
        return Err(EINVAL);
    }
    let (box_port, p1) = read_u16_le(data, fwds_pos + off)?;
    let (host_port, _p2) = read_u16_le(data, p1)?;
    Ok((box_port, host_port))
}

/// Decode one 8-byte classic BPF `SockFilter` instruction at `pos`.
pub fn decode_sock_filter(data: &[u8], pos: usize) -> Result<(SockFilter, usize), i32> {
    let (code, p1) = read_u16_le(data, pos)?;
    let (jt, p2) = read_u8(data, p1)?;
    let (jf, p3) = read_u8(data, p2)?;
    let (k, p4) = read_u32_le(data, p3)?;
    Ok((SockFilter { code, jt, jf, k }, p4))
}

/// Validate the trailing `seccomp` BPF block (`1 <= seccomp_n <= 160` and exact end-of-buffer).
pub fn validate_seccomp_trailer(data: &[u8], pos: usize) -> Result<(u32, usize), i32> {
    let (seccomp_n, seccomp_pos) = read_u32_le(data, pos)?;
    if seccomp_n == 0 || seccomp_n > PS_SECCOMP_MAX_INSNS {
        return Err(EINVAL);
    }
    let seccomp_bytes = (seccomp_n as usize) * 8;
    if data.len() - seccomp_pos != seccomp_bytes {
        return Err(EINVAL);
    }
    Ok((seccomp_n, seccomp_pos))
}

/// Read a bounded count `<= max_count` at `pos`.
pub fn read_bounded_count(data: &[u8], pos: usize, max_count: u32) -> Result<(u32, usize), i32> {
    let (n, next_pos) = read_u32_le(data, pos)?;
    if n > max_count {
        Err(EINVAL)
    } else {
        Ok((n, next_pos))
    }
}

/// Validate and index an entire `LSWP0002` wire buffer into a zero-copy `PlanView`.
pub fn parse_plan(data: &[u8]) -> Result<PlanView, i32> {
    let p0 = check_magic(data)?;
    let (header, p1) = parse_header(data, p0)?;
    let (program, p2) = read_str_span(data, p1)?;
    let (cwd, p3) = read_str_span(data, p2)?;
    let (argc, args_pos) = read_bounded_count(data, p3, MAX_ARGC)?;
    let p4 = scan_str_list(data, args_pos, argc)?;
    let (envc, env_pos) = read_bounded_count(data, p4, MAX_ENVC)?;
    let p5 = scan_env_list(data, env_pos, envc)?;
    let (n_sys, sys_pos) = read_bounded_count(data, p5, MAX_SYS_ENTRIES)?;
    let p6 = scan_sys_entries(data, sys_pos, n_sys)?;
    let (n_etc, etc_pos) = read_bounded_count(data, p6, MAX_ETC_PATHS)?;
    let p7 = scan_str_list(data, etc_pos, n_etc)?;
    let (n_masks, masks_pos) = read_bounded_count(data, p7, MAX_MASK_PATHS)?;
    let p8 = scan_str_list(data, masks_pos, n_masks)?;
    let (n_mounts, mounts_pos) = read_bounded_count(data, p8, MAX_MOUNTS)?;
    let p9 = scan_mounts(data, mounts_pos, n_mounts)?;
    let (n_fwds, fwds_pos) = read_bounded_count(data, p9, MAX_PORT_FORWARDS)?;
    let fwds_bytes = (n_fwds as usize) * 4;
    if fwds_bytes > data.len() - fwds_pos {
        return Err(EINVAL);
    }
    let p10 = fwds_pos + fwds_bytes;
    let (seccomp_n, seccomp_pos) = validate_seccomp_trailer(data, p10)?;
    Ok(PlanView {
        header,
        program,
        cwd,
        argc,
        args_pos,
        envc,
        env_pos,
        n_sys,
        sys_pos,
        n_etc,
        etc_pos,
        n_masks,
        masks_pos,
        n_mounts,
        mounts_pos,
        n_fwds,
        fwds_pos,
        seccomp_n,
        seccomp_pos,
    })
}
