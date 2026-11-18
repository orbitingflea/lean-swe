#!/usr/bin/env python3
"""Hash-based PR deduplicator selecting changed Fuzz suites from Fuzz/suites.json."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import fnmatch
import hashlib
import json
from pathlib import Path
import shlex
import subprocess
import sys
from typing import Any


@dataclass(frozen=True)
class SuiteSpec:
    """Declarative manifest entry for a single fuzz suite."""

    name: str
    paths: tuple[str, ...]


@dataclass(frozen=True)
class SuiteManifest:
    """Parsed Fuzz/suites.json manifest."""

    version: int
    common_paths: tuple[str, ...]
    suites: tuple[SuiteSpec, ...]


@dataclass(frozen=True)
class SuiteDiffResult:
    """Base and head hash comparison for one fuzz suite."""

    name: str
    base_hash: str
    head_hash: str
    changed: bool


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise ValueError(f"Duplicate JSON key: {k!r}")
        out[k] = v
    return out


def _validate_path_list(raw: Any, label: str) -> tuple[str, ...]:
    if not isinstance(raw, list):
        raise ValueError(f"{label} must be a list of path strings")
    cleaned: list[str] = []
    for item in raw:
        if not isinstance(item, str) or not item.strip():
            raise ValueError(f"{label} items must be non-empty strings")
        norm = item[2:] if item.startswith("./") else item
        cleaned.append(norm)
    return tuple(cleaned)


def parse_manifest_text(raw_text: str) -> SuiteManifest:
    """Parse and validate a Fuzz/suites.json document."""
    try:
        data = json.loads(raw_text, object_pairs_hook=_reject_duplicate_keys)
    except json.JSONDecodeError as exc:
        raise ValueError(f"Invalid manifest JSON: {exc}") from exc
    if not isinstance(data, dict):
        raise ValueError("Manifest root must be a JSON object")
    allowed_top = {"version", "common_paths", "suites"}
    unknown_top = set(data.keys()) - allowed_top
    if unknown_top:
        raise ValueError(f"Unknown top-level manifest keys: {sorted(unknown_top)}")
    version = data.get("version")
    if isinstance(version, bool) or version != 1:
        raise ValueError(f"Unsupported manifest version: {version!r}")
    common_paths = _validate_path_list(data.get("common_paths", []), "common_paths")
    suites_raw = data.get("suites")
    if not isinstance(suites_raw, dict):
        raise ValueError("Manifest 'suites' must be a JSON object")
    suites: list[SuiteSpec] = []
    for suite_name, entry in suites_raw.items():
        if not isinstance(suite_name, str) or not suite_name.strip():
            raise ValueError(f"Invalid suite name: {suite_name!r}")
        if isinstance(entry, list):
            paths = _validate_path_list(entry, f"suites.{suite_name}")
        elif isinstance(entry, dict):
            unknown_entry = set(entry.keys()) - {"paths", "description"}
            if unknown_entry:
                raise ValueError(f"Unknown keys in suites.{suite_name}: {sorted(unknown_entry)}")
            paths = _validate_path_list(entry.get("paths"), f"suites.{suite_name}.paths")
        else:
            raise ValueError(f"suites.{suite_name} must be an object or path list")
        suites.append(SuiteSpec(name=suite_name, paths=paths))
    return SuiteManifest(version=version, common_paths=common_paths, suites=tuple(suites))


def load_manifest(manifest_path: Path) -> SuiteManifest:
    """Read and parse a manifest file from disk."""
    return parse_manifest_text(manifest_path.read_text(encoding="utf-8"))


def path_matches_pattern(rel_path: str, pattern: str) -> bool:
    """Return True if repo-relative path `rel_path` matches `pattern` (file, dir prefix, or glob)."""
    norm_pat = pattern[2:] if pattern.startswith("./") else pattern
    if any(ch in norm_pat for ch in ("*", "?", "[")):
        return fnmatch.fnmatchcase(rel_path, norm_pat)
    if norm_pat.endswith("/"):
        return rel_path.startswith(norm_pat)
    return rel_path == norm_pat or rel_path.startswith(norm_pat + "/")


def read_git_tree(repo_dir: Path, rev: str) -> dict[str, tuple[str, str]]:
    """Return `{rel_path: (mode, blob_sha)}` for all entries in git tree `rev`."""
    proc = subprocess.run(
        ["git", "-C", str(repo_dir), "ls-tree", "-r", "-z", rev],
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        err = proc.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"git ls-tree failed for {rev}: {err}")
    entries: dict[str, tuple[str, str]] = {}
    for record in proc.stdout.split(b"\x00"):
        if not record:
            continue
        meta_bytes, path_bytes = record.split(b"\t", 1)
        parts = meta_bytes.decode("utf-8").split(" ")
        mode, _obj_type, obj_sha = parts[0], parts[1], parts[2]
        rel_path = path_bytes.decode("utf-8")
        entries[rel_path] = (mode, obj_sha)
    return entries


def read_git_manifest_suites(repo_dir: Path, rev: str, rel_manifest: str) -> dict[str, Any] | None:
    """Read `suites` mapping from `rel_manifest` at git `rev`, or None if absent."""
    proc = subprocess.run(
        ["git", "-C", str(repo_dir), "cat-file", "-e", f"{rev}:{rel_manifest}"],
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        return None
    show = subprocess.run(
        ["git", "-C", str(repo_dir), "show", f"{rev}:{rel_manifest}"],
        capture_output=True,
        text=True,
        check=False,
    )
    if show.returncode != 0:
        return None
    manifest = parse_manifest_text(show.stdout)
    return {s.name: list(s.paths) for s in manifest.suites}


def compute_suite_hash(
    tree_entries: dict[str, tuple[str, str]],
    patterns: tuple[str, ...],
    manifest_entry: list[str] | None = None,
) -> str:
    """Compute a deterministic SHA-256 digest over matched tree blobs and optional suite manifest entry."""
    hasher = hashlib.sha256()
    if manifest_entry is not None:
        encoded_entry = json.dumps(manifest_entry, separators=(",", ":")).encode("utf-8")
        hasher.update(b"manifest\x00" + encoded_entry + b"\x00")
    matched = [
        (rel_path, mode, sha)
        for rel_path, (mode, sha) in tree_entries.items()
        if any(path_matches_pattern(rel_path, pat) for pat in patterns)
    ]
    matched.sort(key=lambda item: item[0])
    for rel_path, mode, sha in matched:
        hasher.update(f"{mode} {sha} {rel_path}\x00".encode("utf-8"))
    return hasher.hexdigest()


def compute_changed_suites(
    repo_dir: Path,
    base_rev: str,
    head_rev: str,
    manifest: SuiteManifest,
    rel_manifest: str | None = None,
) -> list[SuiteDiffResult]:
    """Compare per-suite input hashes between `base_rev` and `head_rev`."""
    base_tree = read_git_tree(repo_dir, base_rev)
    head_tree = read_git_tree(repo_dir, head_rev)
    base_suites = read_git_manifest_suites(repo_dir, base_rev, rel_manifest) if rel_manifest else None
    head_suites = read_git_manifest_suites(repo_dir, head_rev, rel_manifest) if rel_manifest else None
    results: list[SuiteDiffResult] = []
    for spec in manifest.suites:
        patterns = manifest.common_paths + spec.paths
        base_entry = base_suites.get(spec.name) if base_suites is not None else None
        head_entry = head_suites.get(spec.name) if head_suites is not None else None
        base_hash = compute_suite_hash(base_tree, patterns, base_entry)
        head_hash = compute_suite_hash(head_tree, patterns, head_entry)
        results.append(
            SuiteDiffResult(
                name=spec.name,
                base_hash=base_hash,
                head_hash=head_hash,
                changed=(base_hash != head_hash),
            )
        )
    return results


def build_smoke_command(runner: str, suites: list[str], extra_args: list[str]) -> list[str]:
    """Construct the `leanswe-fuzz --smoke --suite ...` command for changed suites."""
    cmd = [runner, "--smoke"]
    for suite in suites:
        cmd.extend(["--suite", suite])
    cmd.extend(extra_args)
    return cmd


def _resolve_rel_manifest(repo_dir: Path, manifest_path: Path) -> str | None:
    try:
        rel = manifest_path.resolve().relative_to(repo_dir.resolve())
    except ValueError:
        return None
    return rel.as_posix()


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint for hash-based PR suite deduplication."""
    parser = argparse.ArgumentParser(
        description="Hash-based PR deduplicator for LeanSwe Fuzz suites."
    )
    parser.add_argument("--base", required=True, help="Base git commit/ref SHA.")
    parser.add_argument("--head", default="HEAD", help="Head git commit/ref SHA (default: HEAD).")
    parser.add_argument(
        "--manifest",
        default="Fuzz/suites.json",
        help="Path to suite manifest JSON (default: Fuzz/suites.json).",
    )
    parser.add_argument(
        "--repo",
        default=".",
        help="Path to git repository root (default: .).",
    )
    parser.add_argument(
        "--format",
        choices=("lines", "json", "hashes"),
        default="lines",
        help="Output format when listing changed suites (default: lines).",
    )
    parser.add_argument(
        "--run",
        action="store_true",
        help="Execute `leanswe-fuzz --smoke --suite ...` for changed suites (exits 0 if none changed).",
    )
    parser.add_argument(
        "--runner",
        default=".lake/build/bin/leanswe-fuzz",
        help="Path to leanswe-fuzz executable when --run is passed.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="With --run, print the smoke command without executing it.",
    )
    parser.add_argument(
        "--extra-arg",
        action="append",
        default=[],
        help="Extra argument forwarded to leanswe-fuzz under --run (repeatable).",
    )
    args = parser.parse_args(argv)

    repo_dir = Path(args.repo)
    manifest_path = Path(args.manifest)
    if not manifest_path.is_absolute():
        manifest_path = repo_dir / manifest_path

    try:
        manifest = load_manifest(manifest_path)
        rel_manifest = _resolve_rel_manifest(repo_dir, manifest_path)
        diffs = compute_changed_suites(repo_dir, args.base, args.head, manifest, rel_manifest)
    except (ValueError, OSError, RuntimeError) as exc:
        print(f"FUZZ_CHANGED_ERROR: {exc}", file=sys.stderr)
        return 2

    changed = [d.name for d in diffs if d.changed]

    if args.run:
        if not changed:
            print("FUZZ_CHANGED: none (0 boundary suites changed)")
            return 0
        cmd = build_smoke_command(args.runner, changed, args.extra_arg)
        if args.dry_run:
            print(f"DRY_RUN: {shlex.join(cmd)}")
            return 0
        proc = subprocess.run(cmd, cwd=repo_dir, check=False)
        return proc.returncode

    if args.format == "json":
        payload = {
            "base": args.base,
            "head": args.head,
            "changed_suites": changed,
            "suites": {
                d.name: {
                    "changed": d.changed,
                    "base_hash": d.base_hash,
                    "head_hash": d.head_hash,
                }
                for d in diffs
            },
        }
        print(json.dumps(payload, indent=2))
    elif args.format == "hashes":
        for d in diffs:
            status = "changed" if d.changed else "unchanged"
            print(f"{d.name}\t{status}\t{d.base_hash[:12]}\t{d.head_hash[:12]}")
    else:
        for name in changed:
            print(name)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
