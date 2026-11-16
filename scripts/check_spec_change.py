#!/usr/bin/env python3
"""Fail unmarked pull requests that touch frozen spec files."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

SPEC_BASENAMES = frozenset({"Types.lean", "Model.lean", "SpecTests.lean", "Interface.lean"})
REQUIRED_LABEL = "spec-change"
ALLOW_NEW_PACKAGES = True


def resolve_repo_root() -> Path:
    """Return the Git repository top-level directory."""
    top = subprocess.check_output(
        ["git", "rev-parse", "--show-toplevel"],
        text=True,
    ).strip()
    return Path(top)


def resolve_effective_base(repo_root: Path, base_ref: str, head_ref: str) -> str:
    """Resolve merge-base(base_ref, head_ref), falling back to verified base_ref on shallow clones."""
    base_commit = subprocess.check_output(
        ["git", "rev-parse", "--verify", f"{base_ref}^{{commit}}"],
        cwd=repo_root,
        text=True,
    ).strip()
    head_commit = subprocess.check_output(
        ["git", "rev-parse", "--verify", f"{head_ref}^{{commit}}"],
        cwd=repo_root,
        text=True,
    ).strip()
    mb = subprocess.run(
        ["git", "merge-base", base_commit, head_commit],
        cwd=repo_root,
        capture_output=True,
        text=True,
    )
    if mb.returncode == 0 and mb.stdout.strip():
        return mb.stdout.strip()
    return base_commit


def is_spec_file(rel_path: str) -> bool:
    """Return True when rel_path is a frozen spec file under Core/ or LeanSwe/."""
    parts = Path(rel_path).parts
    if not parts:
        return False
    if parts[0] == "Core" and rel_path.endswith(".lean"):
        return True
    if parts[0] == "LeanSwe" and len(parts) >= 2 and parts[-1] in SPEC_BASENAMES:
        return True
    return False


def top_package_dir(rel_path: str) -> str | None:
    """Return 'LeanSwe/<Pkg>' for paths under LeanSwe/<Pkg>/..., else None."""
    parts = Path(rel_path).parts
    if len(parts) >= 3 and parts[0] == "LeanSwe":
        return f"LeanSwe/{parts[1]}"
    return None


def existing_top_packages_at_base(repo_root: Path, base_ref: str) -> set[str]:
    """Return the set of 'LeanSwe/<Pkg>' directories present in base_ref."""
    proc = subprocess.run(
        ["git", "ls-tree", "-d", "--name-only", base_ref, "LeanSwe/"],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=True,
    )
    return {line.strip().rstrip("/") for line in proc.stdout.splitlines() if line.strip().startswith("LeanSwe/")}


def has_spec_change_label(event_path: Path | None, force_mark: bool) -> bool:
    """Return True when --has-mark is passed or the GitHub PR payload carries REQUIRED_LABEL."""
    if force_mark:
        return True
    if event_path is None or not event_path.exists():
        return False
    payload = json.loads(event_path.read_text(encoding="utf-8"))
    pr_obj = payload.get("pull_request") or {}
    labels = pr_obj.get("labels") or []
    return any(isinstance(lbl, dict) and lbl.get("name") == REQUIRED_LABEL for lbl in labels)


def diff_entries(repo_root: Path, base_ref: str, head_ref: str) -> list[tuple[str, list[str]]]:
    """Return (status_code, [paths...]) from NUL-delimited git diff --name-status --find-renames -z."""
    raw = subprocess.check_output(
        ["git", "diff", "--name-status", "--find-renames", "-z", base_ref, head_ref],
        cwd=repo_root,
    ).decode("utf-8", errors="surrogateescape")
    tokens = raw.split("\0")
    entries: list[tuple[str, list[str]]] = []
    idx = 0
    while idx < len(tokens):
        status = tokens[idx]
        if not status:
            idx += 1
            continue
        if status[0] in ("R", "C"):
            entries.append((status, [tokens[idx + 1], tokens[idx + 2]]))
            idx += 3
        else:
            entries.append((status, [tokens[idx + 1]]))
            idx += 2
    return entries


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Verify spec-change approval mark on PR diffs.")
    parser.add_argument("--base", required=True, help="Base commit or ref to diff against.")
    parser.add_argument("--head", default="HEAD", help="Head commit or ref (default: HEAD).")
    parser.add_argument(
        "--event-path",
        default=os.environ.get("GITHUB_EVENT_PATH"),
        help="Path to GitHub Actions event JSON payload.",
    )
    parser.add_argument("--has-mark", action="store_true", help="Treat spec-change mark as present.")
    args = parser.parse_args(argv)

    repo_root = resolve_repo_root()
    effective_base = resolve_effective_base(repo_root, args.base, args.head)
    base_pkgs = existing_top_packages_at_base(repo_root, effective_base)
    entries = diff_entries(repo_root, effective_base, args.head)

    locked_spec_hits: list[str] = []
    new_pkg_spec_hits: list[str] = []

    for status, paths in entries:
        spec_paths = [p for p in paths if is_spec_file(p)]
        if not spec_paths:
            continue
        if ALLOW_NEW_PACKAGES and status == "A" and len(paths) == 1:
            pkg = top_package_dir(paths[0])
            if pkg is not None and pkg not in base_pkgs:
                new_pkg_spec_hits.append(f"{status}\t{paths[0]}")
                continue
        locked_spec_hits.append(f"{status}\t{' -> '.join(paths)}")

    event_file = Path(args.event_path) if args.event_path else None
    marked = has_spec_change_label(event_file, args.has_mark)

    if not locked_spec_hits:
        if new_pkg_spec_hits:
            print(
                f"SPEC_CHECK: ok (new-package spec files={len(new_pkg_spec_hits)}, "
                "locked spec files touched=0)"
            )
        else:
            print("SPEC_CHECK: ok (spec files touched=0)")
        return 0

    if marked:
        print(
            f"SPEC_CHECK: ok (mark='{REQUIRED_LABEL}' present, "
            f"locked spec files touched={len(locked_spec_hits)})"
        )
        for hit in locked_spec_hits:
            print(f"  APPROVED_SPEC_CHANGE: {hit}")
        return 0

    print(
        f"SPEC_CHECK: failed (missing '{REQUIRED_LABEL}' label for "
        f"{len(locked_spec_hits)} locked spec file(s))",
        file=sys.stderr,
    )
    for hit in locked_spec_hits:
        print(
            f"UNMARKED_SPEC_CHANGE: {hit} (get user approval in chat, then apply label '{REQUIRED_LABEL}')",
            file=sys.stderr,
        )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
