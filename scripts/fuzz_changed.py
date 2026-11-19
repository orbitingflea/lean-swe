#!/usr/bin/env python3
"""Hash-based PR deduplicator selecting changed Fuzz suites from Fuzz/suites.json."""

from __future__ import annotations

import argparse, hashlib, json, os, posixpath, re, shlex, subprocess, sys
from collections import deque
from pathlib import Path
from typing import Any, NamedTuple

SUITE_NAME_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]*")


class SuiteSpec(NamedTuple):
    name: str
    paths: tuple[str, ...]

class SuiteManifest(NamedTuple):
    version: int
    common_paths: tuple[str, ...]
    suites: tuple[SuiteSpec, ...]

class SuiteDiffResult(NamedTuple):
    name: str
    base_hash: str
    head_hash: str
    changed: bool

def _enc(s: str) -> bytes: return s.encode("utf-8", "surrogateescape")
def _dec(b: bytes) -> str: return b.decode("utf-8", "surrogateescape")
def _has_ctrl(s: str) -> bool: return any(ord(c) < 32 or ord(c) == 127 for c in s)

def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out: raise ValueError(f"Duplicate JSON key: {k!r}")
        out[k] = v
    return out

def validate_git_rev(rev: str, label: str = "revision") -> str:
    """Reject empty, padded, option-like, control-char, tree-ish, or range git revisions."""
    if not rev or rev != rev.strip(): raise ValueError(f"Invalid git {label}: {rev!r}")
    if rev.startswith("-"): raise ValueError(f"Git {label} must not start with '-': {rev!r}")
    if _has_ctrl(rev) or any(ch.isspace() for ch in rev): raise ValueError(f"Invalid characters in git {label}: {rev!r}")
    if ":" in rev or ".." in rev: raise ValueError(f"Git {label} must not contain ':' or '..': {rev!r}")
    return rev

def _validate_path_list(raw: Any, label: str, *, allow_empty: bool = True) -> tuple[str, ...]:
    if not isinstance(raw, list) or (not allow_empty and not raw):
        raise ValueError(f"{label} must be a {'list' if allow_empty else 'non-empty list'} of path strings")
    cleaned: list[str] = []
    for item in raw:
        if not isinstance(item, str) or not item: raise ValueError(f"{label} items must be non-empty strings")
        if item != item.strip() or _has_ctrl(item): raise ValueError(f"{label} path has invalid whitespace or control chars: {item!r}")
        if item == "./" or item.startswith("/") or "//" in item or "\\" in item:
            raise ValueError(f"{label} path must be a normalized repo-relative path: {item!r}")
        norm = item[2:] if item.startswith("./") else item
        if not norm or norm.startswith("/") or "//" in norm:
            raise ValueError(f"{label} path must be a normalized repo-relative path: {item!r}")
        if any(p in (".", "..") for p in norm.split("/") if p):
            raise ValueError(f"{label} path must not contain '.' or '..' segments: {item!r}")
        cleaned.append(norm)
    return tuple(cleaned)

def parse_manifest_text(raw_text: str) -> SuiteManifest:
    """Parse and validate a Fuzz/suites.json document."""
    try: data = json.loads(raw_text, object_pairs_hook=_reject_duplicate_keys)
    except json.JSONDecodeError as exc: raise ValueError(f"Invalid manifest JSON: {exc}") from exc
    if not isinstance(data, dict): raise ValueError("Manifest root must be a JSON object")
    unknown_top = set(data.keys()) - {"version", "common_paths", "suites"}
    if unknown_top: raise ValueError(f"Unknown top-level manifest keys: {sorted(unknown_top)}")
    version = data.get("version")
    if type(version) is not int or version != 1: raise ValueError(f"Unsupported manifest version: {version!r}")
    common_paths = _validate_path_list(data.get("common_paths", []), "common_paths", allow_empty=True)
    suites_raw = data.get("suites")
    if not isinstance(suites_raw, dict): raise ValueError("Manifest 'suites' must be a JSON object")
    suites: list[SuiteSpec] = []
    for name, entry in suites_raw.items():
        if not isinstance(name, str) or SUITE_NAME_RE.fullmatch(name) is None:
            raise ValueError(f"Invalid suite name: {name!r}")
        if isinstance(entry, list):
            paths = _validate_path_list(entry, f"suites.{name}", allow_empty=False)
        elif isinstance(entry, dict):
            unknown_entry = set(entry.keys()) - {"paths", "description"}
            if unknown_entry: raise ValueError(f"Unknown keys in suites.{name}: {sorted(unknown_entry)}")
            if "description" in entry and (not isinstance(entry["description"], str) or "\x00" in entry["description"]):
                raise ValueError(f"suites.{name}.description must be a string without NUL bytes")
            paths = _validate_path_list(entry.get("paths"), f"suites.{name}.paths", allow_empty=False)
        else:
            raise ValueError(f"suites.{name} must be an object or path list")
        suites.append(SuiteSpec(name=name, paths=paths))
    return SuiteManifest(version=version, common_paths=common_paths, suites=tuple(suites))

def load_manifest(manifest_path: Path) -> SuiteManifest:
    """Read and parse a manifest file from disk."""
    return parse_manifest_text(manifest_path.read_text(encoding="utf-8"))

def _seg_matches(pat: str, seg: str) -> bool:
    pi = si = match = 0; star = -1; pn, sn = len(pat), len(seg)
    while si < sn:
        if pi < pn and (pat[pi] == "?" or pat[pi] == seg[si]): pi += 1; si += 1
        elif pi < pn and pat[pi] == "*": star, match, pi = pi, si, pi + 1
        elif star != -1: pi, match = star + 1, match + 1; si = match
        else: return False
    while pi < pn and pat[pi] == "*": pi += 1
    return pi == pn

def path_matches_pattern(rel_path: str, pattern: str, mode: str = "") -> bool:
    """Return True if repo-relative path `rel_path` matches `pattern` (literal, dir prefix, or segment glob)."""
    norm_pat = pattern[2:] if pattern.startswith("./") else pattern
    base_pat = norm_pat.rstrip("/")
    if not base_pat: return False
    pat_parts = base_pat.split("/")
    if pat_parts == ["**"]: return True
    path_parts = rel_path.split("/")
    n, m = len(path_parts), len(pat_parts)
    trailing_dir = norm_pat.endswith("/") or pat_parts[-1] == "**"
    dp, strict_prefix = [True] + [False] * n, False
    for idx, seg_pat in enumerate(pat_parts):
        if seg_pat == "**":
            seen = False
            dp = [seen := (seen or v) for v in dp]
        else:
            dp = [False] + [dp[j] and _seg_matches(seg_pat, path_parts[j]) for j in range(n)]
        if idx < m - 1 and dp[n]: strict_prefix = True
    return any(dp[:n]) or (dp[n] and ((not trailing_dir) or mode in ("160000", "120000"))) or (mode in ("120000", "160000") and strict_prefix)

def _git_raw(repo_dir: Path, *args: str, input_bytes: bytes | None = None, err_ctx: str = "git") -> bytes:
    proc = subprocess.run(["git", "-C", str(repo_dir), *args], input=input_bytes, capture_output=True, check=False)
    if proc.returncode != 0:
        raise RuntimeError(f"{err_ctx}: {proc.stderr.decode('utf-8', errors='replace').strip() or 'failed'}")
    return proc.stdout

def _git_repo_info(repo_dir: Path) -> tuple[str, str]:
    top = _dec(_git_raw(repo_dir, "rev-parse", "--show-toplevel", err_ctx=f"Not a git repository ({repo_dir})")).rstrip("\r\n")
    pfx = _dec(_git_raw(repo_dir, "rev-parse", "--show-prefix", err_ctx=f"git rev-parse --show-prefix ({repo_dir})")).rstrip("\r\n")
    return top, pfx

def _verify_git_tree_rev(repo_dir: Path, safe_rev: str) -> None:
    _git_repo_info(repo_dir)
    _git_raw(repo_dir, "rev-parse", "--verify", "--quiet", f"{safe_rev}^{{tree}}", err_ctx=f"Invalid git revision {safe_rev!r}")

def read_git_tree(repo_dir: Path, rev: str) -> dict[str, tuple[str, str]]:
    """Return `{rel_path: (mode, blob_sha)}` for all entries in git tree `rev`."""
    safe_rev = validate_git_rev(rev)
    _verify_git_tree_rev(repo_dir, safe_rev)
    out = _git_raw(repo_dir, "ls-tree", "-r", "-z", "--full-tree", f"{safe_rev}^{{tree}}", err_ctx=f"git ls-tree failed for {safe_rev}")
    entries: dict[str, tuple[str, str]] = {}
    for record in out.split(b"\x00"):
        if record:
            meta_bytes, path_bytes = record.split(b"\t", 1)
            parts = meta_bytes.decode("ascii").split(" ")
            entries[_dec(path_bytes)] = (parts[0], parts[2])
    return entries

def _read_symlink_targets(repo_dir: Path, tree_entries: dict[str, tuple[str, str]]) -> dict[str, str]:
    links = [(p, sha) for p, (mode, sha) in tree_entries.items() if mode == "120000"]
    if not links: return {}
    shas = sorted({sha for _, sha in links})
    raw = _git_raw(repo_dir, "cat-file", "--batch", input_bytes=("\n".join(shas) + "\n").encode("ascii"), err_ctx="git cat-file --batch")
    by_sha: dict[str, str] = {}
    pos = 0
    while pos < len(raw):
        nl = raw.index(b"\n", pos)
        hdr = raw[pos:nl].decode("ascii", errors="replace").split(" ")
        pos = nl + 1
        if len(hdr) >= 3 and hdr[1] in ("blob", "tree", "commit", "tag"):
            size = int(hdr[2])
            if hdr[1] == "blob":
                by_sha[hdr[0]] = _dec(raw[pos : pos + size])
            pos += size + 1
    return {p: by_sha[sha] for p, sha in links if sha in by_sha}

def _resolve_symlink_in_tree(
    rel_path: str, tree_entries: dict[str, tuple[str, str]], symlink_targets: dict[str, str], max_hops: int = 40
) -> tuple[str, ...]:
    target = symlink_targets.get(rel_path)
    if target is None or target.startswith("/"):
        return ("external", target if target is not None else "missing-target")
    if not target: return ("dangling", "<empty>")
    base_dir = posixpath.dirname(rel_path)
    cur_parts, pending, hops = (base_dir.split("/") if base_dir else []), deque(target.split("/")), 0
    while pending:
        comp = pending.popleft()
        if comp in ("", "."): continue
        if comp == "..":
            if not cur_parts: return ("external", target)
            cur_parts.pop()
            continue
        cur_parts.append(comp)
        prefix = "/".join(cur_parts)
        if prefix in tree_entries:
            p_mode, p_sha = tree_entries[prefix]
            if p_mode == "160000": return ("submodule", prefix, p_sha, "/".join(pending))
            if p_mode == "120000":
                hops += 1
                if hops > max_hops: return ("cycle", prefix)
                nxt = symlink_targets.get(prefix)
                if not nxt or nxt.startswith("/"): return ("external", nxt if nxt is not None else prefix)
                cur_parts.pop()
                pending.extendleft(reversed(nxt.split("/")))
    resolved = "/".join(cur_parts)
    if not resolved: return ("dir", "")
    if resolved in tree_entries: return ("file", resolved, *tree_entries[resolved])
    return ("dir", resolved) if any(p.startswith(resolved + "/") for p in tree_entries) else ("dangling", resolved)

def read_git_manifest(repo_dir: Path, rev: str, rel_manifest: str) -> SuiteManifest | None:
    """Read and parse `rel_manifest` regular-file blob at git `rev`, or None if absent at `rev`."""
    safe_rev = validate_git_rev(rev)
    _verify_git_tree_rev(repo_dir, safe_rev)
    out = _git_raw(repo_dir, "ls-tree", "-z", "--full-tree", f"{safe_rev}^{{tree}}", "--", rel_manifest, err_ctx=f"git ls-tree {safe_rev}:{rel_manifest}")
    records = [r for r in out.split(b"\x00") if r]
    if not records: return None
    meta_bytes, path_bytes = records[0].split(b"\t", 1)
    if _dec(path_bytes) != rel_manifest: return None
    mode, obj_type, obj_sha = meta_bytes.decode("ascii").split(" ")[:3]
    if mode not in ("100644", "100755") or obj_type != "blob":
        raise ValueError(f"Manifest {rel_manifest!r} at {safe_rev} is not a regular file blob (mode={mode}, type={obj_type})")
    raw = _git_raw(repo_dir, "cat-file", "blob", obj_sha, err_ctx=f"git cat-file blob {safe_rev}:{rel_manifest}")
    try: return parse_manifest_text(raw.decode("utf-8"))
    except UnicodeDecodeError as exc: raise ValueError(f"Manifest {rel_manifest!r} at {safe_rev} is not valid UTF-8: {exc}") from exc

def compute_suite_hash(
    tree_entries: dict[str, tuple[str, str]], patterns: tuple[str, ...], manifest_entry: list[str] | None = None,
    symlink_targets: dict[str, str] | None = None, unresolved_out: list[str] | None = None, side_tag: str = "",
) -> str:
    """Compute a deterministic SHA-256 digest over matched tree blobs, dereferenced symlinks, and patterns."""
    hasher = hashlib.sha256()
    if manifest_entry is not None:
        hasher.update(b"manifest\x00" + json.dumps(manifest_entry, separators=(",", ":")).encode("utf-8") + b"\x00")
    matched = sorted(
        ((p, m, s) for p, (m, s) in tree_entries.items() if any(path_matches_pattern(p, pat, mode=m) for pat in patterns)),
        key=lambda item: _enc(item[0]),
    )
    visited: set[str] = set()
    queue: deque[str] = deque()
    for rel_path, mode, sha in matched:
        hasher.update(f"{mode} {sha} ".encode("ascii") + _enc(rel_path) + b"\x00")
        if mode == "120000" and symlink_targets is not None: queue.append(rel_path)
    while queue:
        lp = queue.popleft()
        if lp in visited: continue
        visited.add(lp)
        res = _resolve_symlink_in_tree(lp, tree_entries, symlink_targets or {})
        kind = res[0]
        if kind == "file":
            hasher.update(b"symlink-file\x00" + _enc(lp) + b"\x00" + f"{res[2]} {res[3]} ".encode("ascii") + _enc(res[1]) + b"\x00")
        elif kind == "dir":
            pfx = res[1] + "/" if res[1] else ""
            hasher.update(b"symlink-dir\x00" + _enc(lp) + b"\x00")
            for p, m, s in sorted(((k, v[0], v[1]) for k, v in tree_entries.items() if not pfx or k.startswith(pfx)), key=lambda it: _enc(it[0])):
                hasher.update(f"{m} {s} ".encode("ascii") + _enc(p) + b"\x00")
                if m == "120000" and p not in visited: queue.append(p)
        elif kind == "submodule":
            hasher.update(b"symlink-submodule\x00" + _enc(lp) + b"\x00" + f"160000 {res[2]} ".encode("ascii") + _enc(res[1]) + b"\x00" + _enc(res[3]) + b"\x00")
        elif kind == "dangling":
            hasher.update(b"symlink-dangling\x00" + _enc(lp) + b"\x00" + _enc(res[1]) + b"\x00")
        else:
            if unresolved_out is not None: unresolved_out.append(f"{lp!r} ({kind}: {res[1]!r})")
            hasher.update(f"symlink-{kind}-{side_tag}\x00".encode("ascii") + _enc(lp) + b"\x00")
    return hasher.hexdigest()

def compute_changed_suites(
    repo_dir: Path, base_rev: str, head_rev: str, manifest: SuiteManifest,
    base_manifest: SuiteManifest | None = None, manifest_in_git: bool = False, allow_deleted: bool = False,
) -> list[SuiteDiffResult]:
    """Compare per-suite input hashes between `base_rev` and `head_rev`."""
    safe_base, safe_head = validate_git_rev(base_rev, "base"), validate_git_rev(head_rev, "head")
    if manifest_in_git and base_manifest is not None:
        head_names = {s.name for s in manifest.suites}
        deleted = [s.name for s in base_manifest.suites if s.name not in head_names]
        if deleted:
            if not allow_deleted:
                raise ValueError(f"Suite(s) deleted from manifest: {', '.join(deleted)} (pass --allow-deleted-suites if intentional)")
            print(f"FUZZ_CHANGED_WARN: allowing deleted suite(s): {', '.join(deleted)}", file=sys.stderr)
    base_tree, head_tree = read_git_tree(repo_dir, safe_base), read_git_tree(repo_dir, safe_head)
    base_links, head_links = _read_symlink_targets(repo_dir, base_tree), _read_symlink_targets(repo_dir, head_tree)
    base_by_name = {s.name: s for s in base_manifest.suites} if base_manifest is not None else {}
    results: list[SuiteDiffResult] = []
    for spec in manifest.suites:
        head_pats = manifest.common_paths + spec.paths
        unresolved: list[str] = []
        head_h = compute_suite_hash(head_tree, head_pats, list(head_pats) if manifest_in_git else None, head_links, unresolved, "head")
        if manifest_in_git:
            if base_manifest is None or spec.name not in base_by_name:
                base_h = hashlib.sha256(f"absent\x00{spec.name}\x00".encode("utf-8")).hexdigest()
            else:
                base_pats = base_manifest.common_paths + base_by_name[spec.name].paths
                base_h = compute_suite_hash(base_tree, base_pats, list(base_pats), base_links, unresolved, "base")
        else:
            base_h = compute_suite_hash(base_tree, head_pats, None, base_links, unresolved, "base")
        if unresolved:
            print(f"FUZZ_CHANGED_WARN: suite={spec.name} unresolved symlink(s): {', '.join(unresolved)}", file=sys.stderr)
        results.append(SuiteDiffResult(spec.name, base_h, head_h, changed=(base_h != head_h or bool(unresolved))))
    return results

def build_smoke_command(runner: str, suites: list[str], extra_args: list[str]) -> list[str]:
    """Construct the `leanswe-fuzz --smoke --suite ...` command for changed suites."""
    return [runner, "--smoke", *[tok for s in suites for tok in ("--suite", s)], *extra_args]

def check_manifest_drift(runner: str, repo_dir: Path, manifest: SuiteManifest) -> None:
    """Verify `manifest.suites` exactly matches `runner --list-suites`."""
    if "\x00" in runner: raise ValueError(f"Runner path contains NUL byte: {runner!r}")
    proc = subprocess.run([runner, "--list-suites"], cwd=repo_dir, capture_output=True, check=False)
    if proc.returncode != 0:
        raise RuntimeError(f"{runner!r} --list-suites failed (rc={proc.returncode}): {proc.stderr.decode('utf-8', errors='replace').strip()}")
    listed = [ln.strip() for ln in proc.stdout.decode("utf-8", errors="replace").splitlines() if ln.strip()]
    if len(listed) != len(set(listed)):
        raise ValueError(f"Duplicate suite(s) reported by {runner} --list-suites: {listed}")
    m_set, r_set = {s.name for s in manifest.suites}, set(listed)
    if m_set != r_set:
        raise ValueError(f"Manifest drift vs {runner} --list-suites: missing_in_manifest={sorted(r_set - m_set)} missing_in_runner={sorted(m_set - r_set)}")

def _resolve_rel_manifest(repo_dir: Path, manifest_path: Path, toplevel: str, prefix: str) -> str | None:
    repo_abs, repo_real = os.path.normpath(os.path.abspath(str(repo_dir))), os.path.normpath(os.path.realpath(str(repo_dir)))
    roots = [os.path.normpath(toplevel)]
    suffix = (os.sep + os.path.normpath(prefix.rstrip("/"))) if prefix else ""
    for base in (repo_abs, repo_real):
        if not prefix: roots.append(base)
        elif base.endswith(suffix): roots.append(os.path.normpath(base[: -len(suffix)]))
    raw_str = str(manifest_path)
    cands = [os.path.normpath(raw_str)] if manifest_path.is_absolute() else [os.path.normpath(os.path.join(b, raw_str)) for b in (repo_abs, repo_real)]
    if manifest_path.is_absolute() and cands[0].startswith(repo_abs + os.sep):
        cands.append(os.path.normpath(os.path.join(repo_real, cands[0][len(repo_abs) + 1 :])))
    cands.extend(os.path.normpath(os.path.join(os.path.realpath(os.path.dirname(c)), os.path.basename(c))) for c in list(cands))
    for cand in cands:
        for root in roots:
            if cand == root: raise ValueError(f"Manifest path points to repository root directory: {manifest_path!s}")
            if cand.startswith(root + os.sep): return Path(cand[len(root) + 1 :]).as_posix()
    return None

def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint for hash-based PR suite deduplication."""
    p = argparse.ArgumentParser(description="Hash-based PR deduplicator for LeanSwe Fuzz suites.")
    p.add_argument("--base", required=True); p.add_argument("--head", default="HEAD")
    p.add_argument("--manifest", default="Fuzz/suites.json"); p.add_argument("--repo", default=".")
    p.add_argument("--format", choices=("lines", "json", "hashes"), default="lines")
    p.add_argument("--run", action="store_true"); p.add_argument("--runner", default=".lake/build/bin/leanswe-fuzz")
    p.add_argument("--dry-run", action="store_true"); p.add_argument("--extra-arg", action="append", default=[])
    p.add_argument("--check-manifest", action="store_true"); p.add_argument("--allow-deleted-suites", action="store_true")
    args = p.parse_args(argv)
    repo_dir, raw_manifest = Path(args.repo), Path(args.manifest)
    try:
        if "\x00" in args.runner or any("\x00" in a for a in args.extra_arg):
            raise ValueError("CLI runner/extra-arg must not contain NUL bytes")
        safe_base, safe_head = validate_git_rev(args.base, "base"), validate_git_rev(args.head, "head")
        toplevel, prefix = _git_repo_info(repo_dir)
        top_dir = Path(toplevel)
        rel_manifest = _resolve_rel_manifest(repo_dir, raw_manifest, toplevel, prefix)
        if rel_manifest is not None:
            head_manifest = read_git_manifest(repo_dir, safe_head, rel_manifest)
            if head_manifest is None: raise RuntimeError(f"Manifest {rel_manifest} not found in git revision {safe_head}")
            try: base_manifest = read_git_manifest(repo_dir, safe_base, rel_manifest)
            except ValueError as exc:
                print(f"FUZZ_CHANGED_WARN: base manifest unusable ({exc}); treating all suites as changed", file=sys.stderr)
                base_manifest = None
            active_manifest = head_manifest
            diffs = compute_changed_suites(repo_dir, safe_base, safe_head, head_manifest, base_manifest, True, args.allow_deleted_suites)
        else:
            active_manifest = load_manifest(raw_manifest if raw_manifest.is_absolute() else repo_dir / raw_manifest)
            diffs = compute_changed_suites(repo_dir, safe_base, safe_head, active_manifest, None, False, args.allow_deleted_suites)
        if args.check_manifest: check_manifest_drift(args.runner, top_dir, active_manifest)
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
        try: proc = subprocess.run(cmd, cwd=top_dir, check=False)
        except (OSError, ValueError) as exc:
            print(f"FUZZ_CHANGED_ERROR: failed to execute {cmd[0]!r}: {exc}", file=sys.stderr)
            return 2
        return 128 + (-proc.returncode) if proc.returncode < 0 else proc.returncode
    if args.format == "json":
        print(json.dumps({"base": safe_base, "head": safe_head, "changed_suites": changed, "suites": {d.name: {"changed": d.changed, "base_hash": d.base_hash, "head_hash": d.head_hash} for d in diffs}}, indent=2))
    elif args.format == "hashes":
        for d in diffs: print(f"{d.name}\t{'changed' if d.changed else 'unchanged'}\t{d.base_hash[:12]}\t{d.head_hash[:12]}")
    else:
        for name in changed: print(name)
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
