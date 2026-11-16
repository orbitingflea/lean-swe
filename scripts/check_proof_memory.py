#!/usr/bin/env python3
"""Measure peak private memory (RssAnon) for Lean source files using lake env."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

DEFAULT_LIMIT_MB = 1024.0
DEFAULT_JOBS = 2
DEFAULT_POLL_INTERVAL_S = 0.02
DEFAULT_TOP_N = 10
CONFIG_FILENAME = ".proof-memory.json"


def find_repo_root(start: Path) -> Path:
    """Locate the repository root containing .proof-memory.json or lakefile.lean."""
    for candidate in (start, *start.parents):
        if (candidate / CONFIG_FILENAME).is_file() or (candidate / "lakefile.lean").is_file():
            return candidate
    return start


def load_default_limit_mb(repo_root: Path) -> float:
    """Read max_private_mb from .proof-memory.json when present, else use DEFAULT_LIMIT_MB."""
    config_path = repo_root / CONFIG_FILENAME
    if not config_path.exists():
        return DEFAULT_LIMIT_MB
    data = json.loads(config_path.read_text(encoding="utf-8"))
    value = data.get("max_private_mb")
    if isinstance(value, (int, float)) and not isinstance(value, bool) and value > 0:
        return float(value)
    raise ValueError(f"Invalid max_private_mb in {config_path}: {value!r}")


def load_lake_env(repo_root: Path) -> dict[str, str]:
    """Capture environment variables from lake env without relying on external tools."""
    raw = subprocess.check_output(
        ["lake", "env", "python3", "-c", "import json, os; print(json.dumps(dict(os.environ)))"],
        cwd=repo_root,
        text=True,
    )
    return json.loads(raw)


def discover_lean_files(repo_root: Path) -> list[str]:
    """Return sorted module Lean files in the repository, excluding lakefile.lean."""
    try:
        out = subprocess.check_output(
            ["git", "ls-files", "--cached", "--others", "--exclude-standard", "*.lean"],
            cwd=repo_root,
            text=True,
        )
        files = [line.strip() for line in out.splitlines() if line.strip()]
    except (subprocess.CalledProcessError, FileNotFoundError):
        files = [str(p.relative_to(repo_root)) for p in repo_root.rglob("*.lean") if not p.is_symlink()]
    excluded_prefixes = (".lake/", "build/")
    return sorted(
        f for f in files
        if f != "lakefile.lean"
        and not any(f.startswith(pfx) for pfx in excluded_prefixes)
        and not (repo_root / f).is_symlink()
    )


def normalize_file_arg(raw: str, cwd: Path, repo_root: Path) -> str:
    """Resolve user-supplied file paths relative to repo_root when inside the repository."""
    p = Path(raw)
    abs_p = (p if p.is_absolute() else (cwd / p)).resolve()
    try:
        return str(abs_p.relative_to(repo_root.resolve()))
    except ValueError:
        return raw


def sample_rss_anon_kb(pid: int) -> int | None:
    """Read current RssAnon in KiB from /proc/<pid>/status, returning None if unavailable."""
    try:
        with open(f"/proc/{pid}/status", encoding="utf-8") as status_file:
            for line in status_file:
                if line.startswith("RssAnon:"):
                    return int(line.split()[1])
    except (OSError, ValueError, IndexError):
        return None
    return None


def measure_file(
    lean_bin: str,
    env: dict[str, str],
    repo_root: Path,
    rel_path: str,
    poll_interval_s: float,
) -> dict[str, object]:
    """Run lean on one file and sample peak RssAnon until exit."""
    peak_anon_kb: int | None = None
    with tempfile.TemporaryFile(mode="w+", encoding="utf-8", errors="replace") as out_file:
        t0 = time.monotonic()
        proc = subprocess.Popen(
            [lean_bin, rel_path],
            cwd=repo_root,
            env=env,
            stdout=out_file,
            stderr=subprocess.STDOUT,
        )
        while True:
            sample = sample_rss_anon_kb(proc.pid)
            if sample is not None:
                peak_anon_kb = sample if peak_anon_kb is None else max(peak_anon_kb, sample)
            if proc.poll() is not None:
                break
            time.sleep(poll_interval_s)
        proc.wait()
        wall_s = time.monotonic() - t0
        out_file.seek(0)
        output = out_file.read().strip()
    return {
        "file": rel_path,
        "anon_mb": (peak_anon_kb / 1024.0) if peak_anon_kb is not None else None,
        "wall_s": wall_s,
        "rc": proc.returncode,
        "output": output,
    }


def parse_args(argv: list[str]) -> argparse.Namespace:
    """Parse CLI options for proof private memory checks."""
    parser = argparse.ArgumentParser(description="Check peak RssAnon per Lean file.")
    parser.add_argument("files", nargs="*", help="Lean files to check (default: all repo modules).")
    parser.add_argument(
        "--limit-mb",
        type=float,
        default=None,
        help=f"Maximum allowed peak RssAnon in MiB (default: {CONFIG_FILENAME} max_private_mb or {DEFAULT_LIMIT_MB:.0f}).",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=DEFAULT_JOBS,
        help=f"Maximum concurrent lean processes (default: {DEFAULT_JOBS}).",
    )
    parser.add_argument(
        "--top",
        type=int,
        default=DEFAULT_TOP_N,
        help=f"Number of top rows to print (default: {DEFAULT_TOP_N}).",
    )
    parser.add_argument(
        "--poll-interval",
        type=float,
        default=DEFAULT_POLL_INTERVAL_S,
        help=f"Sampling interval in seconds (default: {DEFAULT_POLL_INTERVAL_S}).",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """Entry point for per-file Lean private memory verification."""
    cwd = Path.cwd()
    repo_root = find_repo_root(Path(__file__).resolve().parent)
    args = parse_args(sys.argv[1:] if argv is None else argv)
    limit_mb = args.limit_mb if args.limit_mb is not None else load_default_limit_mb(repo_root)
    if args.jobs < 1:
        print("ERROR: --jobs must be >= 1", file=sys.stderr)
        return 2
    if limit_mb <= 0:
        print("ERROR: --limit-mb must be > 0", file=sys.stderr)
        return 2

    files = (
        [normalize_file_arg(f, cwd, repo_root) for f in args.files]
        if args.files
        else discover_lean_files(repo_root)
    )
    if not files:
        print("ERROR: no Lean files found to check", file=sys.stderr)
        return 2

    env = load_lake_env(repo_root)
    lean_bin = shutil.which("lean", path=env.get("PATH")) or "lean"

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        rows = list(
            pool.map(
                lambda f: measure_file(lean_bin, env, repo_root, f, args.poll_interval),
                files,
            )
        )

    ranked = sorted(
        rows,
        key=lambda r: (
            r["anon_mb"] is None,
            -(float(r["anon_mb"]) if r["anon_mb"] is not None else 0.0),
            -float(r["wall_s"]),
            str(r["file"]),
        ),
    )
    over_limit = [r for r in ranked if r["anon_mb"] is not None and float(r["anon_mb"]) > limit_mb]
    unmeasured = [r for r in ranked if r["anon_mb"] is None and int(r["rc"]) == 0]
    failed = [r for r in ranked if int(r["rc"]) != 0]
    measured_vals = [float(r["anon_mb"]) for r in ranked if r["anon_mb"] is not None]
    max_anon_mb = max(measured_vals) if measured_vals else 0.0

    print(
        f"Summary: checked={len(ranked)} limit_mb={limit_mb:.1f} "
        f"max_anon_mb={max_anon_mb:.1f} over_limit={len(over_limit)} "
        f"unmeasured={len(unmeasured)} failed={len(failed)}"
    )
    print(f"{'Rank':>4}  {'Peak RssAnon (MB)':>17}  {'Wall (s)':>8}  {'Exit':>4}  File")
    for idx, row in enumerate(ranked[: max(args.top, 0)], 1):
        anon_str = f"{float(row['anon_mb']):>17.1f}" if row["anon_mb"] is not None else f"{'N/A':>17}"
        print(
            f"{idx:>4}  {anon_str}  {float(row['wall_s']):>8.2f}  "
            f"{int(row['rc']):>4}  {row['file']}"
        )

    for row in over_limit:
        print(
            f"OVER_LIMIT: {row['file']} measured={float(row['anon_mb']):.1f} MB limit={limit_mb:.1f} MB",
            file=sys.stderr,
        )
    for row in unmeasured:
        print(
            f"UNMEASURED: {row['file']} peak RssAnon unavailable",
            file=sys.stderr,
        )
    for row in failed:
        err_note = f" output={row['output']}" if row["output"] else ""
        print(f"CHECK_FAILED: {row['file']} rc={row['rc']}{err_note}", file=sys.stderr)

    return 1 if (over_limit or unmeasured or failed) else 0


if __name__ == "__main__":
    raise SystemExit(main())
