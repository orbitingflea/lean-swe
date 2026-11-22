#!/usr/bin/env python3
"""Automated mutation testing and Clang SanitizerCoverage (`trace-pc-guard`) runner."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import os
import pathlib
import re
import shutil
import signal
import subprocess
import tempfile
import time

REPO = pathlib.Path(__file__).resolve().parent.parent

SUITE_TO_DIR: dict[str, pathlib.Path] = {
    "RegExp": pathlib.Path("LeanSwe/RegExp"),
    "Glob": pathlib.Path("LeanSwe/Glob"),
    "Fs.Raw": pathlib.Path("LeanSwe/Fs/Raw"),
    "Fs": pathlib.Path("LeanSwe/Fs"),
    "Process": pathlib.Path("LeanSwe/Process"),
    "Time": pathlib.Path("LeanSwe/Time"),
    "Json": pathlib.Path("LeanSwe/Json"),
    "EnvVars.Raw": pathlib.Path("LeanSwe/EnvVars/Raw"),
    "EnvVars": pathlib.Path("LeanSwe/EnvVars"),
    "Uuid": pathlib.Path("LeanSwe/Uuid"),
    "Sqlite.Raw": pathlib.Path("LeanSwe/Sqlite/Raw"),
    "Sqlite": pathlib.Path("LeanSwe/Sqlite"),
    "Git": pathlib.Path("LeanSwe/Git"),
    "CmdLine": pathlib.Path("LeanSwe/CmdLine"),
    "NumParse": pathlib.Path("LeanSwe/NumParse"),
    "Toml": pathlib.Path("LeanSwe/Toml"),
    "TempDir": pathlib.Path("LeanSwe/TempDir"),
    "Compress": pathlib.Path("LeanSwe/Compress"),
    "Base64": pathlib.Path("LeanSwe/Base64"),
    "CryptoHash.Raw": pathlib.Path("LeanSwe/CryptoHash/Raw"),
    "CryptoHash": pathlib.Path("LeanSwe/CryptoHash"),
    "Tar": pathlib.Path("LeanSwe/Tar"),
    "ProcessSandbox.Seccomp": pathlib.Path("LeanSwe/ProcessSandbox/Seccomp"),
    "ProcessSandbox.Raw": pathlib.Path("LeanSwe/ProcessSandbox/Raw"),
    "ProcessSandbox": pathlib.Path("LeanSwe/ProcessSandbox"),
    "ConnectProxy": pathlib.Path("LeanSwe/ConnectProxy"),
    "NetRelay": pathlib.Path("LeanSwe/NetRelay"),
    "SlotPool": pathlib.Path("LeanSwe/SlotPool"),
    "LinuxSyscall.Sandbox": pathlib.Path("LeanSwe/LinuxSyscall/Sandbox"),
    "LinuxSyscall.TimeRand": pathlib.Path("LeanSwe/LinuxSyscall/TimeRand"),
    "LinuxSyscall.Passwd": pathlib.Path("LeanSwe/LinuxSyscall/Passwd"),
    "LinuxSyscall.Dns": pathlib.Path("LeanSwe/LinuxSyscall/Dns"),
    "LinuxSyscall.Poll": pathlib.Path("LeanSwe/LinuxSyscall/Poll"),
    "LinuxSyscall.Net": pathlib.Path("LeanSwe/LinuxSyscall/Net"),
    "LinuxSyscall.Process": pathlib.Path("LeanSwe/LinuxSyscall/Process"),
    "LinuxSyscall.Files": pathlib.Path("LeanSwe/LinuxSyscall/Files"),
    "PostFork": pathlib.Path("LeanSwe/PostFork"),
}

C_SHIM_TO_EXTERN_LIB: dict[str, str] = {
    "fs_shim.c": "leanswe_fs",
    "LeanSwe/LinuxSyscall/c/process_shim.c": "leanswe_linux_process",
    "envvars_shim.c": "leanswe_envvars",
    "timerand_shim.c": "leanswe_linux_timerand",
    "passwd_shim.c": "leanswe_linux_passwd",
    "dns_shim.c": "leanswe_linux_dns",
    "sqlite_shim.c": "leanswe_sqlite",
    "cryptohash_shim.c": "leanswe_cryptohash",
    "sandbox_shim.c": "leanswe_linux_sandbox",
    "fd_box.c": "leanswe_linux_fd_box",
    "poll_shim.c": "leanswe_linux_poll",
    "net_shim.c": "leanswe_linux_net",
    "files_shim.c": "leanswe_linux_files",
    "postfork_shim.c": "leanswe_postfork",
}

SUITE_TO_C_SHIMS: dict[str, list[pathlib.Path]] = {
    "LinuxSyscall.Sandbox": [pathlib.Path("LeanSwe/LinuxSyscall/c/sandbox_shim.c")],
    "LinuxSyscall.TimeRand": [pathlib.Path("LeanSwe/LinuxSyscall/c/timerand_shim.c")],
    "LinuxSyscall.Passwd": [pathlib.Path("LeanSwe/LinuxSyscall/c/passwd_shim.c")],
    "LinuxSyscall.Dns": [pathlib.Path("LeanSwe/LinuxSyscall/c/dns_shim.c")],
    "LinuxSyscall.Poll": [pathlib.Path("LeanSwe/LinuxSyscall/c/fd_box.c"), pathlib.Path("LeanSwe/LinuxSyscall/c/fd_box.h"), pathlib.Path("LeanSwe/LinuxSyscall/c/poll_shim.c")],
    "LinuxSyscall.Net": [pathlib.Path("LeanSwe/LinuxSyscall/c/fd_box.c"), pathlib.Path("LeanSwe/LinuxSyscall/c/fd_box.h"), pathlib.Path("LeanSwe/LinuxSyscall/c/net_shim.c")],
    "LinuxSyscall.Process": [pathlib.Path("LeanSwe/LinuxSyscall/c/fd_box.c"), pathlib.Path("LeanSwe/LinuxSyscall/c/fd_box.h"), pathlib.Path("LeanSwe/LinuxSyscall/c/process_shim.c")],
    "LinuxSyscall.Files": [pathlib.Path("LeanSwe/LinuxSyscall/c/fd_box.c"), pathlib.Path("LeanSwe/LinuxSyscall/c/fd_box.h"), pathlib.Path("LeanSwe/LinuxSyscall/c/files_shim.c")],
    "PostFork": [pathlib.Path("LeanSwe/PostFork/c/postfork_shim.c")],
}

SANCOV_RT_C = r"""
#define _POSIX_C_SOURCE 200809L
#define _GNU_SOURCE
#include <dlfcn.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

static uint32_t g_total_guards = 0;

static const char *leanswe_cov_path(void) {
  const char *path = getenv("LEANSWE_SANCOV_LOG");
  if (path && *path) return path;
#ifdef SANCOV_DEFAULT_LOG
  return SANCOV_DEFAULT_LOG;
#else
  return NULL;
#endif
}

void __sanitizer_cov_trace_pc_guard_init(uint32_t *start, uint32_t *stop) {
  if (start == stop || *start) return;
  for (uint32_t *x = start; x < stop; x++) {
    *x = ++g_total_guards;
  }
}

void __sanitizer_cov_trace_pc_guard(uint32_t *guard) {
  uint32_t id = *guard;
  if (!id) return;
  *guard = 0;
  const char *path = leanswe_cov_path();
  if (!path || !*path) return;
  int fd = open(path, O_WRONLY | O_CREAT | O_APPEND, 0644);
  if (fd >= 0) {
    void *pc = __builtin_return_address(0);
    Dl_info info;
    uintptr_t off = (uintptr_t)pc;
    if (dladdr(pc, &info) && info.dli_fbase) {
      off = (uintptr_t)pc - (uintptr_t)info.dli_fbase;
    }
    char buf[128];
    int n = snprintf(buf, sizeof(buf), "HIT %u 0x%llx 0x%llx\n",
                     id, (unsigned long long)(uintptr_t)pc, (unsigned long long)off);
    if (n > 0) (void)write(fd, buf, (size_t)n);
    close(fd);
  }
}

__attribute__((destructor))
static void leanswe_sancov_fini(void) {
  const char *path = leanswe_cov_path();
  if (!path || !*path || g_total_guards == 0) return;
  int fd = open(path, O_WRONLY | O_CREAT | O_APPEND, 0644);
  if (fd >= 0) {
    char buf[64];
    int n = snprintf(buf, sizeof(buf), "TOTAL %u\n", g_total_guards);
    if (n > 0) (void)write(fd, buf, (size_t)n);
    close(fd);
  }
}
"""


@dataclass
class Mutant:
    """One single-site source code mutation."""

    id: str
    rel_path: pathlib.Path
    line_no: int
    op: str
    old_line: str
    new_line: str
    desc: str


def generate_lean_mutants(rel_path: pathlib.Path, text: str) -> list[Mutant]:
    """Generate syntax and semantic mutants on a Lean `Impl.lean` file."""
    mutants: list[Mutant] = []
    lines = text.splitlines(keepends=True)
    for idx, line in enumerate(lines, start=1):
        stripped = line.strip()
        if not stripped or stripped.startswith("--") or stripped.startswith("/--") or stripped.startswith("import "):
            continue
        cands: list[tuple[str, str, str]] = []
        if "==" in line and "!=" not in line:
            cands.append(("BoolOp", line.replace("==", "!=", 1), "swap == to !="))
        if "||" in line:
            cands.append(("BoolOp", line.replace("||", "&&", 1), "swap || to &&"))
        m_if = re.match(r"^(\s*(?:else\s+)?)if\s+(.+?)\s+then([^\n]*)(\n?)$", line)
        if m_if and "msg.isEmpty" not in m_if.group(2) and m_if.group(2) != "false" and "else" not in m_if.group(3):
            cands.append(("GuardDrop", f"{m_if.group(1)}if false then{m_if.group(3)}{m_if.group(4)}", "drop conditional guard"))
        if ".filter fun " in line:
            cands.append(("DropFilter", re.sub(r"\.filter\s+fun\s+[^)]+", "", line, count=1), "drop filter predicate"))
        if "if msg.isEmpty then fallback else msg" in line:
            cands.append(("FallbackDrop", line.replace("if msg.isEmpty then fallback else msg", "msg"), "drop empty-message fallback"))
        if 'detail == "' in line:
            cands.append(("DetailMatchDrop", re.sub(r'detail == "[^"]+"', "false", line, count=1), "drop detail string match"))
        if '| .ok (some "") =>' in line:
            cands.append(("EmptyLitDrop", line.replace('| .ok (some "") =>', '| .ok (some "__NEVER__") =>'), "drop empty-string match arm"))
        if 'message := "' in line and "nonEmptyMsg" not in line and 'message := ""' not in line:
            new_l = re.sub(r'message := "[^"]+"', 'message := "alt-msg"', line, count=1)
            if new_l != line:
                cands.append(("MsgText", new_l, "alter literal diagnostic message text"))
        if "=> .otherError code detail" in line and not line.lstrip().startswith("| .otherError "):
            cands.append(("ArmSwap", line.replace("=> .otherError code detail", "=> .invalidArgument none code detail", 1),
                          "relabel IO.Error arm to invalidArgument"))
        elif "=> .invalidArgument" in line and "code detail" in line and not line.lstrip().startswith("| .invalidArgument "):
            cands.append(("ArmSwap", re.sub(r"=>\s*\.invalidArgument\b.*code detail", "=> .otherError code detail", line, count=1),
                          "relabel invalidArgument arm to otherError"))
        m_kind = re.search(r"kind\s*:=\s*\.(invalidEncoding|invalidKey|notFound|invalidInput|permissionDenied)\b", line)
        if m_kind:
            cands.append(("KindSwap", re.sub(r"kind\s*:=\s*\." + m_kind.group(1), "kind := .ioError", line, count=1),
                          f"relabel .{m_kind.group(1)} to .ioError"))
        m_jump = re.match(r"^(\s*(?:,|\[)\s*bpfJump\s+.+?)\s+(\d+)\s+(\d+)(\s*)$", line)
        if m_jump and m_jump.group(2) != m_jump.group(3):
            cands.append(("BpfJumpSwap", f"{m_jump.group(1)} {m_jump.group(3)} {m_jump.group(2)}{m_jump.group(4)}",
                          f"swap bpfJump jt/jf ({m_jump.group(2)} <-> {m_jump.group(3)})"))
        if "SECCOMP_RET_ERRNO_EPERM" in line:
            cands.append(("SeccompRetSwap", line.replace("SECCOMP_RET_ERRNO_EPERM", "SECCOMP_RET_ALLOW", 1),
                          "replace SECCOMP_RET_ERRNO_EPERM with SECCOMP_RET_ALLOW"))
        elif "SECCOMP_RET_ERRNO_ENOSYS" in line:
            cands.append(("SeccompRetSwap", line.replace("SECCOMP_RET_ERRNO_ENOSYS", "SECCOMP_RET_ALLOW", 1),
                          "replace SECCOMP_RET_ERRNO_ENOSYS with SECCOMP_RET_ALLOW"))
        elif "SECCOMP_RET_ALLOW" in line:
            cands.append(("SeccompRetSwap", line.replace("SECCOMP_RET_ALLOW", "SECCOMP_RET_ERRNO_EPERM", 1),
                          "replace SECCOMP_RET_ALLOW with SECCOMP_RET_ERRNO_EPERM"))
        m_arg = re.search(r"\(seccompArgLowOffset\s+(\d+)\)", line)
        if m_arg:
            arg_idx = int(m_arg.group(1))
            shifted = (arg_idx + 1) % 4
            cands.append(("ArgOffsetShift", line.replace(m_arg.group(0), f"(seccompArgLowOffset {shifted})", 1),
                          f"shift seccompArgLowOffset {arg_idx} -> {shifted}"))
        if "(c % 256)" in line:
            cands.append(("ByteLaneSwap", line.replace("(c % 256)", "((c / 256) % 256)", 1),
                          "perturb opcode low byte lane"))
        elif "((c / 256) % 256)" in line:
            cands.append(("ByteLaneSwap", line.replace("((c / 256) % 256)", "(c % 256)", 1),
                          "perturb opcode high byte lane"))
        elif "(k % 256)" in line:
            cands.append(("ByteLaneSwap", line.replace("(k % 256)", "((k / 256) % 256)", 1),
                          "perturb k byte 0 lane"))
        elif "((k / 256) % 256)" in line:
            cands.append(("ByteLaneSwap", line.replace("((k / 256) % 256)", "((k / 65536) % 256)", 1),
                          "perturb k byte 1 lane"))
        elif "((k / 65536) % 256)" in line:
            cands.append(("ByteLaneSwap", line.replace("((k / 65536) % 256)", "((k / 256) % 256)", 1),
                          "perturb k byte 2 lane"))
        elif "((k / 16777216) % 256)" in line:
            cands.append(("ByteLaneSwap", line.replace("((k / 16777216) % 256)", "((k / 65536) % 256)", 1),
                          "perturb k byte 3 lane"))
        if line.strip() == "| .aarch64 => []":
            indent = line[: len(line) - len(line.lstrip())]
            cands.append(("ArmX32GuardLeak",
                          f"{indent}| .aarch64 => [bpfJump BPF_JMP_JGE_K X32_SYSCALL_BIT 0 1, bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM]\n",
                          "emit x32 guard on aarch64"))
        for op, new_l, desc in cands:
            if new_l != line:
                mid = f"{rel_path.name}:{idx}:{op}"
                mutants.append(Mutant(mid, rel_path, idx, op, line, new_l, desc))
    return mutants


def _replace_if_condition(line: str) -> str:
    """Replace the balanced `if (...)` condition on `line` with `if (0)`."""
    m = re.search(r"\bif\s*\(", line)
    if not m:
        return line
    open_idx = m.end() - 1
    depth = 0
    for i in range(open_idx, len(line)):
        ch = line[i]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return line[: m.start()] + "if (0)" + line[i + 1 :]
    return line


def generate_c_mutants(rel_path: pathlib.Path, text: str) -> list[Mutant]:
    """Generate semantic mutants in a `c/*.c` shim file."""
    mutants: list[Mutant] = []
    lines = text.splitlines(keepends=True)
    for idx, line in enumerate(lines, start=1):
        stripped = line.strip()
        if not stripped or stripped.startswith("//") or stripped.startswith("/*") or stripped.startswith("#"):
            continue
        cands: list[tuple[str, str, str]] = []
        is_len_guard = any(tok in line for tok in ("len", "size", "cap", "argc", "count"))
        if not is_len_guard and ("0x" in line or "MAX" in line or "errno" in line or "status" in line or "rc " in line):
            if "<=" in line:
                cands.append(("CompSwap", line.replace("<=", "<", 1), "tighten <= to <"))
            elif ">=" in line:
                cands.append(("CompSwap", line.replace(">=", ">", 1), "tighten >= to >"))
            elif " < " in line and "for (" not in line:
                cands.append(("CompSwap", line.replace(" < ", " <= ", 1), "loosen < to <="))
            elif " > " in line and "->" not in line:
                cands.append(("CompSwap", line.replace(" > ", " >= ", 1), "loosen > to >="))
        if "if (" in line and "||" in line:
            cands.append(("BoolOp", line.replace("||", "&&", 1), "swap || to && in C guard"))
        if not is_len_guard and "if (" in line and (line.rstrip().endswith("{") or "return " in line) and "NULL ==" not in line and "!= NULL" not in line and "== NULL" not in line and "EFAULT" not in line:
            if "!key_ok || !val_ok" in line:
                cands.append(("DropUtf8Check", line.replace("!key_ok || !val_ok", "!key_ok"), "skip value UTF-8 validation"))
            cands.append(("DropGuard", _replace_if_condition(line), "drop C guard"))
        for eno in ("EINVAL", "EMFILE", "ENFILE", "EACCES", "ENOENT", "EPERM", "EEXIST", "ENOTDIR", "EISDIR", "ENOMEM", "ESRCH", "ECHILD", "EBADF", "EBUSY",
                    "ENOTSOCK", "EAFNOSUPPORT", "EOPNOTSUPP", "ECONNREFUSED", "EPIPE", "EAGAIN", "ENOBUFS", "EPROTO", "EMSGSIZE", "ENOSYS"):
            if eno in line:
                target_eno = "EIO" if eno != "EIO" else "EINVAL"
                cands.append(("ErrnoSwap", line.replace(eno, target_eno, 1), f"swap {eno} to {target_eno}"))
        for op, new_l, desc in cands:
            if new_l != line:
                mid = f"{rel_path.name}:{idx}:{op}"
                mutants.append(Mutant(mid, rel_path, idx, op, line, new_l, desc))
    return mutants


def has_systemd_scope() -> bool:
    """Return True if `systemd-run --user --scope` is available on this host."""
    if not shutil.which("systemd-run"):
        return False
    probe = subprocess.run(
        ["systemd-run", "--user", "--scope", "true"],
        capture_output=True,
        text=True,
    )
    return probe.returncode == 0


def build_mutant(work: pathlib.Path, use_systemd: bool) -> tuple[bool, float]:
    """Build `lean-swe-mut-test` without `Proofs`."""
    t0 = time.monotonic()
    cmd = ["lake", "-d", "harness", "build", "--wfail", "lean-swe-mut-test"]
    if use_systemd:
        cmd = ["systemd-run", "--user", "--scope", "-p", "MemoryMax=12G", *cmd]
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", str(max(1, min(os.cpu_count() or 2, 4))))
    bld = subprocess.run(cmd, cwd=work, env=env, capture_output=True, text=True)
    return bld.returncode == 0, time.monotonic() - t0


def run_suite_mode(work: pathlib.Path, mode: str, suite: str, timeout_s: float = 30.0) -> tuple[str, float]:
    """Run already-built `lean-swe-mut-test` with `--mode <mode> --suite <suite>`."""
    t0 = time.monotonic()
    exe = work / "harness/.lake/build/bin/lean-swe-mut-test"
    proc = subprocess.Popen(
        [str(exe), "--mode", mode, "--suite", suite],
        cwd=work,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    try:
        proc.communicate(timeout=timeout_s)
        dt = time.monotonic() - t0
        return ("KILLED" if proc.returncode != 0 else "SURVIVED"), dt
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.wait()
        return ("KILLED", time.monotonic() - t0)


def resolve_targets(root: pathlib.Path, suite: str) -> tuple[list[pathlib.Path], list[pathlib.Path]]:
    """Collect Lean `Impl.lean` (plus `ConnectProxy` `SysBridge.lean`/`Relay.lean`) and C shim targets."""
    if suite == "all":
        suite_names = list(SUITE_TO_DIR.keys())
    else:
        suite_names = [suite]
    lean_targets: list[pathlib.Path] = []
    c_targets: list[pathlib.Path] = []
    for sname in suite_names:
        d = SUITE_TO_DIR[sname]
        pkg_dir = root / d
        if pkg_dir.is_dir():
            child_suite_dirs = [
                root / sd
                for sd in SUITE_TO_DIR.values()
                if sd != d and (root / sd).is_relative_to(pkg_dir)
            ]
            for lf in sorted(pkg_dir.rglob("*Impl.lean")):
                if not any(lf.is_relative_to(cd) for cd in child_suite_dirs):
                    lean_targets.append(lf.relative_to(root))
            if sname == "ConnectProxy":
                lean_targets.extend((pkg_dir / n).relative_to(root) for n in ("SysBridge.lean", "Relay.lean") if (pkg_dir / n).is_file())
        if sname in SUITE_TO_C_SHIMS:
            for c_rel in SUITE_TO_C_SHIMS[sname]:
                if (root / c_rel).is_file() and c_rel not in c_targets:
                    c_targets.append(c_rel)
        c_dir = pkg_dir / "c"
        if c_dir.is_dir():
            for cf in sorted(c_dir.glob("*.c")):
                c_rel = cf.relative_to(root)
                if c_rel.as_posix() in C_SHIM_TO_EXTERN_LIB or cf.name in C_SHIM_TO_EXTERN_LIB:
                    if c_rel not in c_targets:
                        c_targets.append(c_rel)
    return lean_targets, c_targets


def measure_c_sancov(
    work: pathlib.Path,
    modes: list[str],
    suite: str,
    c_target: pathlib.Path,
    use_systemd: bool,
    timeout_s: float = 30.0,
) -> list[tuple[str, str, str]]:
    """Compile a C shim with Clang `trace-pc-guard` and measure edge and line coverage."""
    extern_lib = C_SHIM_TO_EXTERN_LIB.get(c_target.as_posix()) or C_SHIM_TO_EXTERN_LIB.get(c_target.name)
    if not extern_lib:
        return [(m, "unsupported", f"no extern_lib mapping for {c_target.name}") for m in modes]
    if c_target.name == "sqlite_shim.c":
        return [(m, "skipped", f"{c_target.name} requires multi-object/generated header linkage") for m in modes]

    lean_prefix = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
    clang = pathlib.Path(lean_prefix) / "bin" / "clang"
    if not clang.exists():
        return [(m, "no clang", f"missing bundled clang at {clang}") for m in modes]

    cov_ws = work / ".cov_ws"
    shutil.rmtree(cov_ws, ignore_errors=True)
    try:
        shutil.copytree(work, cov_ws, symlinks=True)

        rt_c = cov_ws / ".sancov_rt.c"
        rt_c.write_text(SANCOV_RT_C)
        shim_o = cov_ws / ".cov_shim.o"
        rt_o = cov_ws / ".cov_rt.o"
        cov_log = cov_ws / "sancov_active.log"

        cflags_common = [
            "-isystem", f"{lean_prefix}/include/clang",
            "-I", f"{lean_prefix}/include",
            "-O0", "-g", "-fPIC", "-Wall", "-Wextra", "-Werror",
        ]
        c1 = subprocess.run(
            [str(clang), *cflags_common, "-fsanitize-coverage=trace-pc-guard", "-c", str(cov_ws / c_target), "-o", str(shim_o)],
            capture_output=True, text=True,
        )
        if c1.returncode != 0:
            return [(m, "shim clang err", c1.stderr[:300]) for m in modes]
        c2 = subprocess.run(
            [str(clang), *cflags_common, f'-DSANCOV_DEFAULT_LOG="{cov_log}"', "-c", str(rt_c), "-o", str(rt_o)],
            capture_output=True, text=True,
        )
        if c2.returncode != 0:
            return [(m, "rt clang err", c2.stderr[:300]) for m in modes]

        lf = cov_ws / "lakefile.lean"
        new_extern = (
            f'extern_lib «{extern_lib}» pkg := do\n'
            f'  let name := nameToStaticLib "{extern_lib}"\n'
            '  let o1 ← inputBinFile (pkg.dir / ".cov_shim.o")\n'
            '  let o2 ← inputBinFile (pkg.dir / ".cov_rt.o")\n'
            '  buildStaticLib (pkg.staticLibDir / name) #[o1, o2]\n'
        )
        lf_text = lf.read_text()
        if c_target.name == "fd_box.c":
            lf_text = lf_text.replace("#[oJob, fdBoxJob]", "#[oJob]")
        lf_lines = lf_text.splitlines(keepends=True)
        patched: list[str] = []
        skip = False
        for ln in lf_lines:
            if ln.startswith(f"extern_lib «{extern_lib}»"):
                patched.append(new_extern)
                skip = True
            elif skip and (ln.startswith("@[") or ln.startswith("lean_exe") or ln.startswith("lean_lib") or ln.startswith("extern_lib")):
                skip = False
                patched.append(ln)
            elif not skip:
                patched.append(ln)
        lf.write_text("".join(patched))
        shutil.rmtree(cov_ws / ".lake/build", ignore_errors=True)
        shutil.rmtree(cov_ws / "harness/.lake/build", ignore_errors=True)
        built, _ = build_mutant(cov_ws, use_systemd)
        if not built:
            return [(m, "cov link err", "lake build failed") for m in modes]

        exe = cov_ws / "harness/.lake/build/bin/lean-swe-mut-test"
        elf_hdr = subprocess.run(["readelf", "-h", str(exe)], capture_output=True, text=True).stdout
        results: list[tuple[str, str, str]] = []
        for mode in modes:
            if cov_log.exists():
                cov_log.unlink()
            env = dict(os.environ, LEANSWE_SANCOV_LOG=str(cov_log))
            proc = subprocess.Popen(
                [str(exe), "--mode", mode, "--suite", suite],
                cwd=cov_ws,
                env=env,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                start_new_session=True,
            )
            try:
                stdout, stderr = proc.communicate(timeout=timeout_s)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
                results.append((mode, "cov run timeout", f"timed out after {timeout_s}s"))
                continue
            if proc.returncode != 0:
                results.append((mode, "cov run err", (stdout + stderr)[:300]))
                continue
            if not cov_log.exists():
                results.append((mode, "no sancov log", ""))
                continue
            hit_ids: set[int] = set()
            raw_pcs: set[str] = set()
            rel_offs: set[str] = set()
            total_guards = 0
            for ln in cov_log.read_text().splitlines():
                parts = ln.split()
                if len(parts) == 4 and parts[0] == "HIT":
                    hit_ids.add(int(parts[1]))
                    raw_pcs.add(parts[2])
                    rel_offs.add(parts[3])
                elif len(parts) == 2 and parts[0] == "TOTAL":
                    total_guards = max(total_guards, int(parts[1]))
            addrs = sorted(rel_offs if "DYN" in elf_hdr else raw_pcs)
            hit_lines: set[int] = set()
            if addrs:
                a2l = subprocess.run(["addr2line", "-e", str(exe), *addrs], capture_output=True, text=True)
                for out_ln in a2l.stdout.splitlines():
                    if c_target.name in out_ln:
                        m_ln = re.search(r":(\d+)", out_ln)
                        if m_ln:
                            hit_lines.add(int(m_ln.group(1)))
            pct = (100.0 * len(hit_ids) / total_guards) if total_guards else 0.0
            results.append((mode, "OK", f"edges={len(hit_ids)}/{total_guards} ({pct:.1f}%), hit_source_lines={len(hit_lines)} {sorted(hit_lines)[:15]}"))
        return results
    finally:
        shutil.rmtree(cov_ws, ignore_errors=True)


def main() -> int:
    """Run mutation generation, testing, and optional C coverage measurement."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=["baseline", "full"], default="full")
    parser.add_argument("--compare-modes", action="store_true", help="Compile each mutant once and evaluate baseline and full")
    parser.add_argument("--suite", choices=["all", *sorted(SUITE_TO_DIR.keys())], default="all")
    parser.add_argument("--with-c-cov", action="store_true")
    parser.add_argument("--c-cov-only", action="store_true")
    parser.add_argument("--timeout", type=float, default=30.0, help="Per-mutant execution timeout in seconds")
    parser.add_argument("--dry-run-files", nargs="*", help="Only list mutants generated for given file paths")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")

    if args.dry_run_files:
        tot = 0
        for fp_str in args.dry_run_files:
            fp = pathlib.Path(fp_str)
            txt = fp.read_text()
            muts = generate_c_mutants(fp, txt) if fp.suffix in (".c", ".h") else generate_lean_mutants(fp, txt)
            tot += len(muts)
            print(f"{fp}: {len(muts)} mutants")
            for m in muts:
                print(f"  - L{m.line_no} [{m.op}] {m.desc}")
        print(f"DRY_RUN_TOTAL: {tot}")
        return 0

    lean_targets, c_targets = resolve_targets(REPO, args.suite)
    use_systemd = has_systemd_scope()

    with tempfile.TemporaryDirectory(prefix="leanswe-mut-") as td:
        work = pathlib.Path(td) / "ws"
        shutil.copytree(REPO, work, symlinks=True, ignore=shutil.ignore_patterns(".lake", ".git"))
        eval_modes = ["baseline", "full"] if args.compare_modes else [args.mode]
        ok_init, t_init_bld = build_mutant(work, use_systemd)
        if not ok_init:
            print("Initial build failed!")
            return 1
        for mname in eval_modes:
            st, t_run = run_suite_mode(work, mname, args.suite, args.timeout)
            print(f"Initial check ({mname}, suite={args.suite}): status={st} build={t_init_bld:.2f}s run={t_run:.2f}s")
            if st != "SURVIVED":
                print(f"Initial suite {mname} failed!")
                return 1

        if (args.with_c_cov or args.c_cov_only) and c_targets:
            for ct in c_targets:
                if ct.suffix != ".c":
                    continue
                for mname, cst, cout in measure_c_sancov(work, eval_modes, args.suite, ct, use_systemd, args.timeout):
                    print(f"C sancov [{mname}] ({cst}, {ct}): {cout}")
        if args.c_cov_only: return 0
        mutants: list[Mutant] = []
        for rel in lean_targets: mutants.extend(generate_lean_mutants(rel, (work / rel).read_text()))
        for rel in c_targets: mutants.extend(generate_c_mutants(rel, (work / rel).read_text()))

        per_mode_killed: dict[str, int] = {m: 0 for m in eval_modes}
        per_mode_survived: dict[str, list[Mutant]] = {m: [] for m in eval_modes}
        per_mode_killed_sites: dict[str, set[tuple[str, int]]] = {m: set() for m in eval_modes}
        compile_fail = 0
        valid_times: list[float] = []
        all_times: list[float] = []
        touched_sites: set[tuple[str, int]] = set()

        for m in mutants:
            target_file = work / m.rel_path
            orig = target_file.read_text()
            lines = orig.splitlines(keepends=True)
            lines[m.line_no - 1] = m.new_line
            target_file.write_text("".join(lines))
            built, dt_bld = build_mutant(work, use_systemd)
            site = (str(m.rel_path), m.line_no)
            touched_sites.add(site)
            if not built:
                target_file.write_text(orig)
                all_times.append(dt_bld)
                compile_fail += 1
                print(f"[COMPILE_FAIL] {dt_bld:5.2f}s  {m.id}  ({m.desc})")
                continue

            mode_statuses: dict[str, str] = {}
            dt_runs = 0.0
            for mname in eval_modes:
                st, dt_r = run_suite_mode(work, mname, args.suite, args.timeout)
                dt_runs += dt_r
                mode_statuses[mname] = st
                if st == "KILLED":
                    per_mode_killed[mname] += 1
                    per_mode_killed_sites[mname].add(site)
                else:
                    per_mode_survived[mname].append(m)
            target_file.write_text(orig)
            dt = dt_bld + dt_runs
            all_times.append(dt)
            valid_times.append(dt_bld + (dt_runs / len(eval_modes)))
            primary = eval_modes[-1]
            tag_str = " ".join(f"{mn}:{mode_statuses[mn][0]}" for mn in eval_modes) if len(eval_modes) > 1 else mode_statuses[primary]
            print(f"[{mode_statuses[primary]:8s}] {dt:5.2f}s  {m.id}  ({tag_str})  ({m.desc})")

        valid = len(mutants) - compile_fail
        avg_all = sum(all_times) / len(all_times) if all_times else 0.0
        avg_valid = sum(valid_times) / len(valid_times) if valid_times else 0.0
        for mname in eval_modes:
            k_cnt = per_mode_killed[mname]
            surv = per_mode_survived[mname]
            ksites = per_mode_killed_sites[mname]
            sem_tot = valid - sum(1 for sm in surv if sm.op == "MsgText")
            kill_rate = (100.0 * k_cnt / valid) if valid else 0.0
            sem_rate = (100.0 * k_cnt / sem_tot) if sem_tot else 0.0
            site_cov = (100.0 * len(ksites) / len(touched_sites)) if touched_sites else 0.0
            print(
                f"\nMUTATION_SUMMARY mode={mname} suite={args.suite}: total={len(mutants)} valid={valid} "
                f"killed={k_cnt} survived={len(surv)} compile_fail={compile_fail} "
                f"kill_rate={kill_rate:.1f}% sem_kill={k_cnt}/{sem_tot} ({sem_rate:.1f}%) "
                f"site_cov={len(ksites)}/{len(touched_sites)} ({site_cov:.1f}%) "
                f"avg_valid={avg_valid:.2f}s avg_all={avg_all:.2f}s total_time={sum(all_times):.1f}s"
            )
            if mname == eval_modes[-1] and surv:
                print("SURVIVING MUTANTS (final mode):")
                for sm in surv:
                    print(f"  - {sm.rel_path}:{sm.line_no} [{sm.op}] {sm.desc}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
