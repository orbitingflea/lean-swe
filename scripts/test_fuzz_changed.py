#!/usr/bin/env python3
"""Unit and git-integration tests for scripts/fuzz_changed.py and audit workflows."""

from __future__ import annotations

import copy, io, json, os, re, shlex, shutil, signal, stat, subprocess, sys, tempfile, time, unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(Path(__file__).resolve().parent))
import fuzz_changed

SAMPLE_MANIFEST = {
    "version": 1,
    "common_paths": ["Fuzz/Common/", "Fuzz/Main.lean"],
    "suites": {
        "envvars": {"paths": ["LeanSwe/EnvVars/Impl.lean", "LeanSwe/EnvVars/Model.lean", "LeanSwe/EnvVars/Raw/", "Fuzz/EnvVars/"]},
        "cryptohash": {"paths": ["LeanSwe/CryptoHash/Impl.lean", "LeanSwe/CryptoHash/Model.lean", "LeanSwe/CryptoHash/Raw/", "Fuzz/CryptoHash/"]},
    },
}

def _git(repo: Path, *args: str, env_extra: dict[str, str] | None = None) -> str:
    env = {**os.environ, "GIT_AUTHOR_NAME": "Test Author", "GIT_AUTHOR_EMAIL": "test@example.com", "GIT_COMMITTER_NAME": "Test Author", "GIT_COMMITTER_EMAIL": "test@example.com", **(env_extra or {})}
    return subprocess.check_output(["git", *args], cwd=repo, env=env, stderr=subprocess.DEVNULL, text=True).strip()

def _write_files(repo: Path, files: dict[str, str]) -> None:
    for rel, content in files.items():
        path = repo / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")

def _commit_all(repo: Path, message: str, env_extra: dict[str, str] | None = None) -> str:
    _git(repo, "add", "-A"); _git(repo, "commit", "-m", message, env_extra=env_extra)
    return _git(repo, "rev-parse", "HEAD")

def _make_script(path: Path, body: str) -> Path:
    path.write_text(f"#!/bin/sh\n{body}\n", encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IEXEC)
    return path

def _extract_run_blocks(path: Path) -> list[tuple[str, str]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    blocks: list[tuple[str, str]] = []
    cur_name, i = "<step>", 0
    while i < len(lines):
        stripped = lines[i].lstrip()
        if lines[i].startswith("      - name: "):
            cur_name = lines[i].split(": ", 1)[1].strip()
        elif stripped in ("run: |", "run: |-"):
            indent = len(lines[i]) - len(stripped) + 2
            body: list[str] = []
            i += 1
            while i < len(lines) and (lines[i] == "" or lines[i].startswith(" " * indent)):
                body.append(lines[i][indent:] if len(lines[i]) >= indent else "")
                i += 1
            blocks.append((cur_name, "\n".join(body) + "\n"))
            continue
        elif stripped.startswith("run: "):
            blocks.append((cur_name, stripped[5:] + "\n"))
        i += 1
    return blocks

class FuzzChangedUnitTests(unittest.TestCase):
    """Pure manifest parsing, validation, and path matching tests."""

    def test_parse_manifest_validation_holes(self) -> None:
        for bad_json in ('{"version": 2, "suites": {}}', '{"version": 1.0, "suites": {}}', '{"version": true, "suites": {}}', '{"version": 1, "suites": {}, "suites": {}}'):
            with self.assertRaises(ValueError): fuzz_changed.parse_manifest_text(bad_json)
        for bad_path in ("./", "/abs/path", "a//b", "a\\b", "../escape", "Fuzz/Common/ ", "", "a/\nb", "a\x00b"):
            bad = copy.deepcopy(SAMPLE_MANIFEST); bad["common_paths"] = [bad_path]
            with self.assertRaises(ValueError): fuzz_changed.parse_manifest_text(json.dumps(bad))
        for bad_name in ("", " ", " float ", "selftest,float", "a\nb", "a\tb", "--all", "a\x00b"):
            with self.assertRaises(ValueError): fuzz_changed.parse_manifest_text(json.dumps({"version": 1, "suites": {bad_name: {"paths": ["a.lean"]}}}))
        for bad_desc in (12345, {"x": 1}, None, "bad\x00desc"):
            with self.assertRaises(ValueError): fuzz_changed.parse_manifest_text(json.dumps({"version": 1, "suites": {"ok": {"description": bad_desc, "paths": ["a.lean"]}}}))
        for bad_paths in ({"paths": []}, []):
            with self.assertRaises(ValueError): fuzz_changed.parse_manifest_text(json.dumps({"version": 1, "suites": {"ok": bad_paths}}))

    def test_validate_git_rev_rejects_flags_whitespace_treeish_and_ranges(self) -> None:
        for bad_rev in ("", "-h", "--upload-pack=evil", "HEAD\x00", "main branch", " main", "HEAD:Fuzz", ":0:file", "a..b", "a\nb"):
            with self.assertRaises(ValueError): fuzz_changed.validate_git_rev(bad_rev)

    def test_path_matching_globs_brackets_and_submodules(self) -> None:
        m = fuzz_changed.path_matches_pattern
        for args in (("Fuzz/Common/Rng.lean", "Fuzz/Common/"), ("LeanSwe/EnvVars/Impl.lean", "LeanSwe/EnvVars/Impl.lean"),
                     ("LeanSwe/EnvVars/Raw/c/shim.c", "LeanSwe/*/Raw/"), ("LeanSwe/EnvVars/Raw/c/shim.c", "LeanSwe/*/Raw"),
                     ("LeanSwe/c/foo.c", "LeanSwe/**/c/*.c"), ("LeanSwe/a/b/c/foo.c", "LeanSwe/**/c/*.c"),
                     ("LeanSwe/LinuxSyscall/c/sandbox_shim.c", "LeanSwe/LinuxSyscall/c/*.c"), ("abc", "a?c"), ("Fuzz/foo[1].lean", "Fuzz/foo[1].lean")):
            self.assertTrue(m(*args), args)
        for args in (("Fuzz/CommonExtra/Foo.lean", "Fuzz/Common/"), ("LeanSwe/EnvVarsExtra/Impl.lean", "LeanSwe/EnvVars"),
                     ("LeanSwe/EnvVars/RawExtra/c/shim.c", "LeanSwe/*/Raw/"), ("LeanSwe/a/b/c/nested/foo.c", "LeanSwe/**/c/*.c"),
                     ("LeanSwe/LinuxSyscall/c/sub/nested/foo.c", "LeanSwe/LinuxSyscall/c/*.c"), ("a/c", "a?c"), ("Fuzz/foo1.lean", "Fuzz/foo[1].lean")):
            self.assertFalse(m(*args), args)
        self.assertTrue(m("Fuzz/submod", "Fuzz/submod/", mode="160000"))
        self.assertFalse(m("Fuzz/submod", "Fuzz/submod/", mode="100644"))
        self.assertTrue(m("a", "a/", mode="120000")); self.assertTrue(m("a", "a/**", mode="120000"))
        self.assertTrue(m("a", "**/a/", mode="120000")); self.assertTrue(m("a", "a/b.lean", mode="120000"))
        t0 = time.monotonic()
        self.assertFalse(m("a" * 30, "a" + "*" * 10 + "b"))
        self.assertFalse(m("a" * 28, "*a" * 11 + "*b"))
        self.assertLess(time.monotonic() - t0, 0.2)

    def test_build_smoke_command(self) -> None:
        self.assertEqual(fuzz_changed.build_smoke_command("harness/.lake/build/bin/leanswe-fuzz", ["envvars", "cryptohash"], ["--self-test-shrink"]),
                         ["harness/.lake/build/bin/leanswe-fuzz", "--smoke", "--suite", "envvars", "--suite", "cryptohash", "--self-test-shrink"])

    def test_real_repo_manifest_and_workflows(self) -> None:
        manifest = fuzz_changed.load_manifest(REPO_ROOT / "harness" / "Fuzz" / "suites.json")
        self.assertEqual(manifest.version, 1)
        self.assertNotIn("harness/Fuzz/SelfTest.lean", manifest.common_paths)
        self.assertIn(".github/workflows/audit.yml", manifest.common_paths)
        self.assertIn(".github/actions/install-lean/action.yml", manifest.common_paths)
        by_name = {s.name: s for s in manifest.suites}
        self.assertIn("selftest", by_name); self.assertIn("float", by_name); self.assertIn("cmdline", by_name)
        self.assertIn("envvars", by_name); self.assertIn("cryptohash", by_name); self.assertIn("dns", by_name)
        for ws, sub in (("sandbox", "Sandbox"), ("timerand", "TimeRand"), ("files", "Files"), ("process", "Process"), ("poll", "Poll"), ("net", "Net")):
            self.assertIn(ws, by_name)
            self.assertIn(f"harness/Fuzz/LinuxSyscall/{sub}/", by_name[ws].paths)
            self.assertIn(f"LeanSwe/LinuxSyscall/{sub}/", by_name[ws].paths)
        self.assertIn("Core/", manifest.common_paths)
        self.assertIn("passwd", by_name); self.assertIn("sqlite", by_name); self.assertIn("git", by_name); self.assertIn("json", by_name); self.assertIn("toml", by_name); self.assertIn("uuid", by_name); self.assertIn("time", by_name)
        self.assertEqual(by_name["json"].paths, ("LeanSwe/Json/", "harness/Fuzz/Json/"))
        self.assertEqual(by_name["toml"].paths, ("LeanSwe/Toml/", "LeanSwe/NumParse/", "harness/Fuzz/Toml/"))
        self.assertTrue({"LeanSwe/Git/", "LeanSwe/Process/", "LeanSwe/EnvVars/", "LeanSwe/Fs/", "harness/Fuzz/Git/"}.issubset(by_name["git"].paths))
        self.assertIn("LeanSwe/LinuxSyscall/Passwd/", by_name["passwd"].paths)
        self.assertIn("LeanSwe/LinuxSyscall/c/passwd_shim.c", by_name["passwd"].paths)
        self.assertIn("LeanSwe/LinuxSyscall/Common/", by_name["passwd"].paths)
        self.assertIn("postfork", by_name)
        self.assertIn("LeanSwe/LinuxSyscall/Common/", by_name["postfork"].paths)
        self.assertIn("LeanSwe/LinuxSyscall/c/fd_box.h", by_name["postfork"].paths)
        self.assertIn("harness/Fuzz/SelfTest.lean", by_name["selftest"].paths)
        self.assertEqual(by_name["sqlite"].paths, ("LeanSwe/Sqlite/", "harness/Fuzz/Sqlite/"))
        self.assertIn("LeanSwe/LinuxSyscall/Sandbox/", by_name["files"].paths); self.assertIn("LeanSwe/LinuxSyscall/c/sandbox_shim.c", by_name["files"].paths)
        audit = (REPO_ROOT / ".github" / "workflows" / "audit.yml").read_text(encoding="utf-8")
        daily = (REPO_ROOT / ".github" / "workflows" / "audit-daily.yml").read_text(encoding="utf-8")
        self.assertNotIn("leanswe-world-fuzz", audit); self.assertNotIn("leanswe-world-fuzz", daily)
        for wf in (audit, daily): self.assertIn("--suite Git ", wf); self.assertIn(",Git,", wf); self.assertIn("python3 -B -m unittest discover -s scripts -p 'test_*.py'", wf)
        self.assertNotIn("test -f scripts/test_fuzz_changed.py", daily); self.assertIn("--check-manifest", daily)
        self.assertIn("leanswe-fuzz --all --exclude sandbox,timerand,files,process,poll,net ", daily); self.assertNotIn("leanswe-fuzz --suite float ", daily)
        for req in (
            "--sandbox-strace-fault-check",
            "vm.memfd_noexec",
            "--timerand-strace-fault-check",
            "--files-strace-fault-check",
            "--process-strace-fault-check",
            "--poll-strace-fault-check",
            "--net-strace-fault-check",
            "--seed 11262680905236430927 --steps 50000 --self-test-shrink --require-ns",
            "--suite postfork --steps 500 --self-test-shrink 0<&- >/dev/null",
        ):
            self.assertIn(req, daily, f"missing from audit-daily.yml: {req}")
            self.assertIn(req, audit, f"missing from audit.yml: {req}")
        self.assertIn("if: success() && steps.fuzz_gate.outcome == 'success' && steps.fuzz_gate.outputs.run_files == 'true'", audit)
        self.assertIn("PR_LABELS_JSON: ${{ toJson(github.event.pull_request.labels.*.name) }}", audit)
        self.assertIn("INPUT_FUZZ_SUITES: ${{ inputs.fuzz_suites }}", audit)
        self.assertIn("fuzz_suites:", audit)
        self.assertIn("types: [opened, synchronize, reopened, labeled, unlabeled]", audit)
        self.assertNotIn("check_proof_memory.py", audit)
        self.assertIn("check_proof_memory.py", daily)
        mut_re = r"lean-swe-mut-test --mode full --suite ([A-Za-z0-9_.,]+)"
        audit_mut = [s for csv in re.findall(mut_re, audit) for s in csv.split(",")]
        daily_mut = [s for csv in re.findall(mut_re, daily) for s in csv.split(",")]
        self.assertEqual(len(audit_mut), len(set(audit_mut)), f"duplicate mut suite in audit.yml: {audit_mut}")
        self.assertEqual(sorted(audit_mut), sorted(daily_mut))

    def test_real_repo_manifest_transitive_closure(self) -> None:
        manifest = fuzz_changed.load_manifest(REPO_ROOT / "harness" / "Fuzz" / "suites.json")
        by_name = {s.name: s for s in manifest.suites}
        for pat in manifest.common_paths:
            self.assertTrue((REPO_ROOT / pat).exists(), f"missing common_path: {pat}")
        for s in manifest.suites:
            for pat in s.paths:
                self.assertTrue((REPO_ROOT / pat).exists(), f"missing {s.name} path: {pat}")

        def parse_lean_imports(path: Path) -> list[str]:
            mods: list[str] = []
            block_depth = 0
            for line in path.read_text(encoding="utf-8").splitlines():
                s = line.strip()
                if block_depth > 0 or s.startswith("/-"):
                    i = 0
                    while i < len(line):
                        if line[i : i + 2] == "/-":
                            block_depth += 1; i += 2
                        elif line[i : i + 2] == "-/" and block_depth > 0:
                            block_depth -= 1; i += 2
                        else:
                            i += 1
                    continue
                if not s or s.startswith("--") or s in ("prelude", "module"):
                    continue
                m = re.match(r"^(?:(?:private|public|meta)\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)\b", s)
                if m:
                    mods.append(m.group(1))
                else:
                    break
            return mods

        def resolve_mod(mod: str) -> str | None:
            rel = mod.replace(".", "/") + ".lean"
            if (REPO_ROOT / rel).is_file():
                return rel
            if (REPO_ROOT / "harness" / rel).is_file():
                return f"harness/{rel}"
            return None

        sym_to_c: dict[str, set[str]] = {}
        c_roots = (REPO_ROOT / "LeanSwe", REPO_ROOT / "harness" / "Fuzz")
        for base in c_roots:
            for p in sorted(list(base.rglob("*.c")) + list(base.rglob("*.h"))):
                rel_p = p.relative_to(REPO_ROOT)
                if "target" in rel_p.parts or p.name in ("sqlite3.c", "sqlite3.h"):
                    continue
                txt = p.read_text(encoding="utf-8", errors="replace")
                rel = rel_p.as_posix()
                for m in re.finditer(r"^[A-Za-z_][^\n;{}]*?\b(leanswe_[A-Za-z0-9_]+)\s*\([^{;]*?\)\s*\{", txt, re.M | re.S):
                    sym_to_c.setdefault(m.group(1), set()).add(rel)

        def expand_native(seeds: set[str]) -> set[str]:
            out: set[str] = set()
            stack = list(seeds)
            root_real = REPO_ROOT.resolve()
            while stack:
                cur = stack.pop()
                if cur in out:
                    continue
                out.add(cur)
                if cur.endswith(("sqlite3.c", "sqlite3.h")):
                    continue
                fp = REPO_ROOT / cur
                if not fp.is_file():
                    continue
                txt = fp.read_text(encoding="utf-8", errors="replace")
                for m in re.finditer(r'^\s*#\s*include\s+"([^"]+)"', txt, re.M):
                    tgt = (fp.parent / m.group(1)).resolve().relative_to(root_real).as_posix()
                    if (REPO_ROOT / tgt).is_file() and tgt not in out:
                        stack.append(tgt)
                if cur.endswith("fd_box.h"):
                    stack.append("LeanSwe/LinuxSyscall/c/fd_box.c")
                if cur.endswith("sqlite3.h"):
                    stack.append("LeanSwe/Sqlite/Raw/c/sqlite3.c")
                if cur.endswith(("postfork_shim.c", "postfork_fuzz.c")):
                    for rs in (REPO_ROOT / "LeanSwe/PostFork/rust").rglob("*"):
                        if rs.is_file():
                            rrel = rs.relative_to(REPO_ROOT)
                            if "target" not in rrel.parts:
                                stack.append(rrel.as_posix())
            return out

        def transitive_deps(lean_seeds: list[str]) -> tuple[set[str], set[str]]:
            seen_lean: set[str] = set()
            stack = list(lean_seeds)
            while stack:
                cur = stack.pop()
                if cur in seen_lean:
                    continue
                seen_lean.add(cur)
                for mod in parse_lean_imports(REPO_ROOT / cur):
                    dep = resolve_mod(mod)
                    if dep is not None and dep not in seen_lean:
                        stack.append(dep)
            c_seeds: set[str] = set()
            for lf in seen_lean:
                txt = (REPO_ROOT / lf).read_text(encoding="utf-8")
                for m in re.finditer(r'@\[extern\s+"(leanswe_[A-Za-z0-9_]+)"\]', txt):
                    sym = m.group(1)
                    self.assertIn(sym, sym_to_c, f"unmapped extern {sym} in {lf}")
                    c_seeds |= sym_to_c[sym]
            return seen_lean, expand_native(c_seeds)

        def is_covered(rel: str, pats: tuple[str, ...]) -> bool:
            return any(fuzz_changed.path_matches_pattern(rel, pat) for pat in pats)

        suite_roots = {
            "selftest": ["harness/Fuzz/SelfTest.lean"],
            **{
                s: sorted(p.relative_to(REPO_ROOT).as_posix() for p in (REPO_ROOT / d).rglob("*.lean"))
                for s, d in (
                    ("float", "harness/Fuzz/Float"), ("cmdline", "harness/Fuzz/CmdLine"),
                    ("envvars", "harness/Fuzz/EnvVars"), ("cryptohash", "harness/Fuzz/CryptoHash"),
                    ("passwd", "harness/Fuzz/Passwd"), ("dns", "harness/Fuzz/Dns"),
                    ("compress", "harness/Fuzz/Compress"), ("postfork", "harness/Fuzz/PostFork"), ("processsandbox", "harness/Fuzz/ProcessSandbox"),
                    ("sqlite", "harness/Fuzz/Sqlite"), ("git", "harness/Fuzz/Git"), ("json", "harness/Fuzz/Json"), ("toml", "harness/Fuzz/Toml"), ("uuid", "harness/Fuzz/Uuid"), ("time", "harness/Fuzz/Time"),
                    ("sandbox", "harness/Fuzz/LinuxSyscall/Sandbox"), ("timerand", "harness/Fuzz/LinuxSyscall/TimeRand"),
                    ("files", "harness/Fuzz/LinuxSyscall/Files"), ("process", "harness/Fuzz/LinuxSyscall/Process"),
                    ("poll", "harness/Fuzz/LinuxSyscall/Poll"), ("net", "harness/Fuzz/LinuxSyscall/Net"),
                )
            },
        }
        self.assertEqual(set(suite_roots.keys()), set(by_name.keys()))
        mapped_files = set().union(*suite_roots.values())
        unmapped = {
            p.relative_to(REPO_ROOT).as_posix() for p in (REPO_ROOT / "harness/Fuzz").rglob("*.lean")
        } - mapped_files
        self.assertEqual(
            unmapped,
            {
                "harness/Fuzz/Common/Coverage.lean", "harness/Fuzz/Common/Rng.lean",
                "harness/Fuzz/Common/Shrink.lean", "harness/Fuzz/Common/Suite.lean",
                "harness/Fuzz/LinuxSyscall/Env.lean", "harness/Fuzz/LinuxSyscall/Main.lean",
                "harness/Fuzz/LinuxSyscall/ProcessEnv.lean", "harness/Fuzz/LinuxSyscall/Rng.lean",
                "harness/Fuzz/LinuxSyscall/SandboxEnv.lean", "harness/Fuzz/Main.lean",
            },
        )
        main_imports = {resolve_mod(m) for m in parse_lean_imports(REPO_ROOT / "harness/Fuzz/Main.lean")}
        self.assertTrue(main_imports <= mapped_files | {"harness/Fuzz/Common/Suite.lean", "harness/Fuzz/LinuxSyscall/Env.lean", "harness/Fuzz/LinuxSyscall/Main.lean"}, main_imports)
        ls_main_imports = {resolve_mod(m) for m in parse_lean_imports(REPO_ROOT / "harness/Fuzz/LinuxSyscall/Main.lean")}
        self.assertTrue(ls_main_imports <= mapped_files | {"harness/Fuzz/Common/Suite.lean", "harness/Fuzz/LinuxSyscall/Env.lean", "harness/Fuzz/LinuxSyscall/ProcessEnv.lean", "LeanSwe/Fs/Interface.lean", "LeanSwe/LinuxSyscall/Files/SpecTests.lean"}, ls_main_imports)

        common_lean, common_native = transitive_deps(["harness/Fuzz/LinuxSyscall/Env.lean", "harness/Fuzz/Common/Suite.lean"])
        common_native |= expand_native({"harness/Fuzz/LinuxSyscall/c/fuzz_env.c"})
        self.assertEqual(sorted(f for f in common_lean if not is_covered(f, manifest.common_paths)), [])
        self.assertEqual(sorted(f for f in common_native if not is_covered(f, manifest.common_paths)), [])
        for proof_path in ("LeanSwe/Fs/Proofs/Foo.lean", "LeanSwe/LinuxSyscall/Files/Proofs/Foo.lean", "LeanSwe/LinuxSyscall/TimeRand/Proofs.lean"):
            self.assertFalse(is_covered(proof_path, manifest.common_paths), proof_path)

        extra_roots = {"files": ["LeanSwe/LinuxSyscall/Files/SpecTests.lean"], "poll": ["LeanSwe/Fs/Interface.lean"], "net": ["LeanSwe/Fs/Interface.lean"]}
        for sname, seeds in suite_roots.items():
            pats = manifest.common_paths + by_name[sname].paths
            s_lean, s_native = transitive_deps(seeds + extra_roots.get(sname, []))
            miss_l = sorted(f for f in (s_lean | common_lean) if not is_covered(f, pats))
            miss_n = sorted(f for f in (s_native | common_native) if not is_covered(f, pats))
            self.assertEqual((miss_l, miss_n), ([], []), f"suite {sname!r} missing deps in suites.json")

class FuzzChangedGitIntegrationTests(unittest.TestCase):
    """End-to-end git history, symlink, submodule, locale, drift, and workflow tests."""

    def _init_repo(self, tmp: Path) -> tuple[Path, str]:
        repo = tmp / "repo"; repo.mkdir(); _git(repo, "init", "-b", "main")
        _write_files(repo, {
            "harness/Fuzz/suites.json": json.dumps(SAMPLE_MANIFEST, indent=2) + "\n",
            "Fuzz/Common/Rng.lean": "def rng := 1\n", "Fuzz/Main.lean": "def main := 0\n",
            "LeanSwe/EnvVars/Impl.lean": "def envImpl := 1\n", "LeanSwe/EnvVars/Model.lean": "def envModel := 1\n",
            "LeanSwe/EnvVars/Proofs.lean": "theorem envProof : True := trivial\n",
            "LeanSwe/EnvVars/Raw/c/envvars_shim.c": "int f(void) { return 0; }\n", "Fuzz/EnvVars/Suite.lean": "def envSuite := 1\n",
            "LeanSwe/CryptoHash/Impl.lean": "def chImpl := 1\n", "LeanSwe/CryptoHash/Model.lean": "def chModel := 1\n",
            "LeanSwe/CryptoHash/Raw/c/cryptohash_shim.c": "int g(void) { return 0; }\n", "Fuzz/CryptoHash/Suite.lean": "def chSuite := 1\n",
            "LeanSwe/Tar/Impl.lean": "def tarImpl := 1\n", "README.md": "hello\n",
        })
        return repo, _commit_all(repo, "initial commit")

    def _run_cli(self, argv: list[str]) -> tuple[int, str, str]:
        out_buf, err_buf = io.StringIO(), io.StringIO()
        with redirect_stdout(out_buf), redirect_stderr(err_buf):
            rc = fuzz_changed.main(argv)
        return rc, out_buf.getvalue(), err_buf.getvalue()

    def test_unrelated_single_common_revert_delete_rename(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            repo, base = self._init_repo(Path(tmpdir))
            _write_files(repo, {"README.md": "docs\n", "LeanSwe/Tar/Impl.lean": "def tarImpl := 2\n", "LeanSwe/EnvVars/Proofs.lean": "theorem envProof : 1 = 1 := rfl\n"})
            h1 = _commit_all(repo, "unrelated")
            self.assertEqual(self._run_cli(["--repo", str(repo), "--base", base, "--head", h1])[:2], (0, ""))
            rc_run, out_run, _ = self._run_cli(["--repo", str(repo), "--base", base, "--head", h1, "--run", "--runner", "/nonexistent/fuzz"])
            self.assertEqual(rc_run, 0); self.assertIn("FUZZ_CHANGED: none", out_run)

            _write_files(repo, {"LeanSwe/EnvVars/Raw/c/envvars_shim.c": "int f(void) { return 1; }\n"})
            h2 = _commit_all(repo, "edit envvars")
            dollar_dir = Path(tmpdir) / "dir$TESTVAR_literal"; dollar_dir.mkdir()
            log_path = dollar_dir / "runner-args.txt"
            fake = _make_script(repo / "fake-fuzz.sh", f'printf "%s\\n" "$@" > {shlex.quote(str(log_path))}')
            self.assertEqual(self._run_cli(["--repo", str(repo), "--base", base, "--head", h2, "--run", "--runner", str(fake)])[0], 0)
            self.assertEqual(log_path.read_text(encoding="utf-8").splitlines(), ["--smoke", "--suite", "envvars"])

            _git(repo, "checkout", "-b", "common", base); _write_files(repo, {"Fuzz/Common/Rng.lean": "def rng := 2\n"})
            self.assertEqual(self._run_cli(["--repo", str(repo), "--base", base, "--head", _commit_all(repo, "edit common")])[:2], (0, "envvars\ncryptohash\n"))

            _git(repo, "checkout", "-b", "rev", base)
            _write_files(repo, {"LeanSwe/CryptoHash/Model.lean": "def chModel := 99\n"}); _commit_all(repo, "tmp")
            _write_files(repo, {"LeanSwe/CryptoHash/Model.lean": "def chModel := 1\n"})
            self.assertEqual(self._run_cli(["--repo", str(repo), "--base", base, "--head", _commit_all(repo, "revert")])[:2], (0, ""))

            _git(repo, "checkout", "-b", "del", base); _git(repo, "rm", "Fuzz/EnvVars/Suite.lean")
            self.assertEqual(self._run_cli(["--repo", str(repo), "--base", base, "--head", _commit_all(repo, "del")])[:2], (0, "envvars\n"))

            _git(repo, "checkout", "-b", "ren", base); _git(repo, "mv", "Fuzz/CryptoHash/Suite.lean", "Fuzz/CryptoHash/SuiteRenamed.lean")
            self.assertEqual(self._run_cli(["--repo", str(repo), "--base", base, "--head", _commit_all(repo, "ren")])[:2], (0, "cryptohash\n"))

    def test_head_manifest_add_suite_common_removal_subdir_and_deleted_suite(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            repo, base = self._init_repo(Path(tmpdir))
            _git(repo, "checkout", "-b", "add-suite", base)
            m_add = copy.deepcopy(SAMPLE_MANIFEST); m_add["suites"]["sqlite"] = {"paths": ["LeanSwe/Sqlite/Model.lean", "Fuzz/Sqlite/"]}
            _write_files(repo, {"harness/Fuzz/suites.json": json.dumps(m_add) + "\n", "Fuzz/Sqlite/Suite.lean": "def s := 1\n"})
            add_sha = _commit_all(repo, "add sqlite")

            _git(repo, "checkout", "-b", "rem-common", base)
            m_rem = copy.deepcopy(SAMPLE_MANIFEST); m_rem["common_paths"] = ["Fuzz/Common/"]
            _write_files(repo, {"harness/Fuzz/suites.json": json.dumps(m_rem) + "\n", "Fuzz/Main.lean": "def main := 42\n"})
            rem_sha = _commit_all(repo, "drop main from common")

            _git(repo, "checkout", "-b", "del-suite", base)
            m_del = copy.deepcopy(SAMPLE_MANIFEST); del m_del["suites"]["envvars"]
            _write_files(repo, {"harness/Fuzz/suites.json": json.dumps(m_del) + "\n", "LeanSwe/EnvVars/Impl.lean": "def envImpl := 99\n"})
            del_sha = _commit_all(repo, "delete envvars suite")

            _git(repo, "checkout", base)
            self.assertEqual(self._run_cli(["--repo", str(repo), "--base", base, "--head", add_sha])[:2], (0, "sqlite\n"))
            self.assertEqual(self._run_cli(["--repo", str(repo), "--base", base, "--head", rem_sha])[:2], (0, "envvars\ncryptohash\n"))
            rc_del, _, err_del = self._run_cli(["--repo", str(repo), "--base", base, "--head", del_sha])
            self.assertEqual(rc_del, 2); self.assertIn("deleted from manifest: envvars", err_del)
            rc_ok, out_ok, err_ok = self._run_cli(["--repo", str(repo), "--base", base, "--head", del_sha, "--allow-deleted-suites"])
            self.assertEqual((rc_ok, out_ok.splitlines()), (0, [])); self.assertIn("FUZZ_CHANGED_WARN:", err_ok)

            sub = repo / "harness/Fuzz"
            self.assertEqual(self._run_cli(["--repo", str(sub), "--manifest", str(repo / "harness/Fuzz/suites.json"), "--base", base, "--head", add_sha])[:2], (0, "sqlite\n"))
            (repo / "harness/.lake/build/bin").mkdir(parents=True)
            _make_script(repo / "harness/.lake/build/bin/leanswe-fuzz", 'if [ "$1" = "--list-suites" ]; then printf "envvars\\ncryptohash\\n"; fi')
            self.assertEqual(self._run_cli(["--repo", str(sub), "--manifest", "suites.json", "--base", base, "--head", base, "--check-manifest"])[0], 0)
            self.assertEqual(self._run_cli(["--repo", str(sub), "--manifest", "suites.json", "--base", base, "--head", rem_sha, "--run"])[0], 0)
            link_sub = Path(tmpdir) / "link_to_fuzz"; os.symlink(str(sub), link_sub)
            _write_files(repo, {"harness/Fuzz/suites.json": json.dumps(SAMPLE_MANIFEST) + "\n"})
            for m_arg in (["--repo", str(link_sub), "--manifest", "suites.json"], ["--repo", str(repo), "--manifest", str(link_sub / "suites.json")], ["--repo", str(repo), "--manifest", "../link_to_fuzz/suites.json"]):
                rc_ls, _, err_ls = self._run_cli([*m_arg, "--base", base, "--head", del_sha])
                self.assertEqual(rc_ls, 2, m_arg); self.assertIn("deleted from manifest: envvars", err_ls)

    def test_submodule_gitlink_and_tracked_symlinks(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            repo, base = self._init_repo(Path(tmpdir))
            m = copy.deepcopy(SAMPLE_MANIFEST)
            m["suites"]["sub_slash"] = {"paths": ["Fuzz/submod/"]}
            m["suites"]["sub_noslash"] = {"paths": ["Fuzz/submod"]}
            m["suites"]["dirlink"] = {"paths": ["Fuzz/LinkedDir/"]}
            m["suites"]["dirdeep"] = {"paths": ["Fuzz/LinkedDir/Inner.lean"]}
            _write_files(repo, {"harness/Fuzz/suites.json": json.dumps(m) + "\n", "Shared/common.lean": "def c := 1\n", "SharedDir/x.lean": "def x := 1\n", "RealLinked/Inner.lean": "def i := 1\n"})
            os.symlink("../../Shared/common.lean", repo / "Fuzz/EnvVars/link.lean"); os.symlink("../../SharedDir", repo / "Fuzz/EnvVars/linkdir")
            os.symlink("../../Fuzz/submod/inner.lean", repo / "Fuzz/EnvVars/sublink.lean"); os.symlink("../RealLinked", repo / "Fuzz/LinkedDir")
            _git(repo, "add", "-A"); _git(repo, "update-index", "--add", "--cacheinfo", f"160000,{base},Fuzz/submod")
            _git(repo, "commit", "-m", "add gitlink and symlinks"); s0 = _git(repo, "rev-parse", "HEAD")

            _write_files(repo, {"Shared/common.lean": "def c := 2\n", "RealLinked/Inner.lean": "def i := 2\n"})
            _git(repo, "add", "Shared/common.lean", "RealLinked/Inner.lean"); _git(repo, "commit", "-m", "edit targets")
            s1 = _git(repo, "rev-parse", "HEAD")
            self.assertEqual(set(self._run_cli(["--repo", str(repo), "--base", s0, "--head", s1])[1].splitlines()), {"envvars", "dirlink", "dirdeep"})

            _git(repo, "checkout", "-b", "dirlink_b", s0); _write_files(repo, {"SharedDir/x.lean": "def x := 2\n"})
            _git(repo, "add", "SharedDir/x.lean"); _git(repo, "commit", "-m", "edit dir")
            self.assertEqual(self._run_cli(["--repo", str(repo), "--base", s0, "--head", _git(repo, "rev-parse", "HEAD")])[:2], (0, "envvars\n"))

            _git(repo, "checkout", "-b", "subbump", s0); _git(repo, "update-index", "--add", "--cacheinfo", f"160000,{s1},Fuzz/submod")
            _git(repo, "commit", "-m", "bump gitlink")
            self.assertEqual(set(self._run_cli(["--repo", str(repo), "--base", s0, "--head", _git(repo, "rev-parse", "HEAD")])[1].splitlines()), {"envvars", "sub_slash", "sub_noslash"})

            _git(repo, "checkout", "-b", "extlink", s0)
            os.symlink("/tmp/outside_target", repo / "Fuzz/CryptoHash/ext.lean")
            os.symlink("cyc_b", repo / "Fuzz/EnvVars/cyc_a"); os.symlink("cyc_a", repo / "Fuzz/EnvVars/cyc_b")
            _git(repo, "add", "Fuzz/CryptoHash/ext.lean", "Fuzz/EnvVars/cyc_a", "Fuzz/EnvVars/cyc_b")
            _git(repo, "commit", "-m", "add external and cyclic symlinks"); s4 = _git(repo, "rev-parse", "HEAD")
            rc_e, out_e, err_e = self._run_cli(["--repo", str(repo), "--base", s4, "--head", s4])
            self.assertEqual(rc_e, 0); self.assertEqual(set(out_e.splitlines()), {"envvars", "cryptohash"}); self.assertIn("unresolved symlink", err_e)
            fake_obj = subprocess.check_output(["git", "hash-object", "-w", "-t", "commit", "--stdin"], cwd=repo, input=f"tree {_git(repo, 'rev-parse', 'HEAD^{tree}')}\nauthor a <a@a> 0 +0000\ncommitter a <a@a> 0 +0000\n\n{s1} blob notanint\n".encode()).decode().strip()
            self.assertEqual(fuzz_changed._read_symlink_targets(repo, {"Fuzz/EnvVars/link.lean": ("120000", _git(repo, "rev-parse", f"{s0}:Fuzz/EnvVars/link.lean")), "Fuzz/bad": ("120000", fake_obj)}), {"Fuzz/EnvVars/link.lean": "../../Shared/common.lean"})

    def test_manifest_symlink_schema_upgrade_nonutf8_locale_errors_and_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            repo, base = self._init_repo(Path(tmpdir))
            bad_manifest = Path(tmpdir) / "outside.json"
            bad_manifest.write_text(json.dumps({"version": 1, "suites": {"other": {"paths": ["nope"]}}}), encoding="utf-8")
            (repo / "harness/Fuzz/suites.json").unlink(); os.symlink(str(bad_manifest), repo / "harness/Fuzz/suites.json")
            _git(repo, "checkout", "-b", "edit-only", base); _write_files(repo, {"LeanSwe/EnvVars/Impl.lean": "def envImpl := 9\n"})
            _git(repo, "add", "LeanSwe/EnvVars/Impl.lean"); _git(repo, "commit", "-m", "edit env"); edit_sha = _git(repo, "rev-parse", "HEAD")
            self.assertEqual(self._run_cli(["--repo", str(repo), "--base", base, "--head", edit_sha])[:2], (0, "envvars\n"))
            (repo / "harness/Fuzz/suites.json").unlink(); _git(repo, "checkout", "--", "harness/Fuzz/suites.json")

            _git(repo, "checkout", "-b", "symlink-manifest", base); _write_files(repo, {"harness/Fuzz/real_old.json": json.dumps(SAMPLE_MANIFEST) + "\n"})
            (repo / "harness/Fuzz/suites.json").unlink(); os.symlink("real_old.json", repo / "harness/Fuzz/suites.json"); sym_base = _commit_all(repo, "symlink manifest")
            (repo / "harness/Fuzz/suites.json").unlink(); (repo / "harness/Fuzz/real_old.json").unlink()
            _write_files(repo, {"harness/Fuzz/suites.json": json.dumps(SAMPLE_MANIFEST) + "\n"}); sym_head = _commit_all(repo, "regular manifest")
            for co in (sym_base, sym_head):
                _git(repo, "checkout", co)
                rc_s, out_s, err_s = self._run_cli(["--repo", str(repo), "--base", sym_base, "--head", sym_head])
                self.assertEqual((rc_s, out_s.splitlines()), (0, ["envvars", "cryptohash"])); self.assertIn("base manifest unusable", err_s)
            rc_sh, _, err_sh = self._run_cli(["--repo", str(repo), "--base", sym_head, "--head", sym_base])
            self.assertEqual(rc_sh, 2); self.assertIn("not a regular file blob", err_sh)

            _git(repo, "checkout", "-b", "upgrade", base); _write_files(repo, {"harness/Fuzz/suites.json": json.dumps({"version": 0, "suites": {}}) + "\n"})
            old_v0 = _commit_all(repo, "v0")
            m_utf8 = copy.deepcopy(SAMPLE_MANIFEST); m_utf8["suites"]["envvars"]["description"] = "em-dash \u2014 ok"
            _write_files(repo, {"harness/Fuzz/suites.json": json.dumps(m_utf8, ensure_ascii=False) + "\n"}); new_v1 = _commit_all(repo, "v1")
            env_c = {**os.environ, "LC_ALL": "C", "PYTHONCOERCECLOCALE": "0", "PYTHONUTF8": "0"}
            subp = subprocess.run([sys.executable, "-B", str(REPO_ROOT / "scripts/fuzz_changed.py"), "--repo", str(repo), "--base", old_v0, "--head", new_v1], env=env_c, capture_output=True, text=True)
            self.assertEqual((subp.returncode, subp.stdout.splitlines()), (0, ["envvars", "cryptohash"]), subp.stderr)

            _git(repo, "checkout", "-b", "nonutf8", base)
            raw_blob = subprocess.check_output(["git", "hash-object", "-w", "--stdin"], cwd=repo, input=b"x").decode().strip()
            subprocess.run(["git", "update-index", "--index-info"], cwd=repo, input=f"100644 {raw_blob}\t".encode() + b"Tests/bad_\xff_fixture.bin\n", check=True)
            _git(repo, "commit", "-m", "non-utf8"); self.assertEqual(self._run_cli(["--repo", str(repo), "--base", base, "--head", _git(repo, "rev-parse", "HEAD")])[:2], (0, ""))

            nongit = Path(tmpdir) / "nongit"; nongit.mkdir()
            rc_ng, _, err_ng = self._run_cli(["--repo", str(nongit), "--base", base, "--head", "HEAD"])
            self.assertEqual(rc_ng, 2); self.assertIn("Not a git repository", err_ng)
            for bad_args in (["--repo", str(repo), "--base", f"{base}:Fuzz", "--head", edit_sha], ["--repo", str(repo), "--base=-bad", "--head", edit_sha],
                             ["--repo", str(repo), "--base", base, "--head", edit_sha, "--run", "--runner", "/bin/true\x00"],
                             ["--repo", str(repo), "--base", base, "--head", edit_sha, "--run", "--runner", "/nonexistent/fuzz"]):
                rc_b, _, err_b = self._run_cli(bad_args)
                self.assertEqual(rc_b, 2); self.assertIn("FUZZ_CHANGED_ERROR:", err_b)

            ok_runner = _make_script(repo / "r_ok.sh", 'printf "envvars\\ncryptohash\\n"')
            drift_runner = _make_script(repo / "r_drift.sh", 'printf "envvars\\ncryptohash\\nextra\\n"')
            self.assertEqual(self._run_cli(["--repo", str(repo), "--base", base, "--head", base, "--check-manifest", "--runner", str(ok_runner)])[0], 0)
            rc_dr, _, err_dr = self._run_cli(["--repo", str(repo), "--base", base, "--head", base, "--check-manifest", "--runner", str(drift_runner)])
            self.assertEqual(rc_dr, 2); self.assertIn("Manifest drift", err_dr)

    def test_audit_yml_pr_base_extraction_hardening(self) -> None:
        lines = (REPO_ROOT / ".github" / "workflows" / "audit.yml").read_text(encoding="utf-8").splitlines()
        start = next(i for i, ln in enumerate(lines) if "Fetch pull-request base commit" in ln)
        snippet = [ln[10:] for ln in lines[start : start + 20] if ln.startswith("          ") and not ln.strip().startswith("RECORDED_BASE:")]
        script = "\n".join(snippet[: snippet.index("git fetch --no-tags --depth=1 origin -- \"$BASE\"")]) + '\necho "$BASE"\n'
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir); src = root / "src"; src.mkdir(); _git(src, "init", "-b", "main")
            marker = root / "pwned"; _write_files(src, {"a.txt": "1\n"})
            c0 = _commit_all(src, f"orphan\n\nparent --upload-pack=touch {marker}\n" + ("parent " + "0" * 40 + "\n") * 200); rec = "a" * 40
            r0 = subprocess.run(["bash", "-c", script], cwd=src, env={**os.environ, "RECORDED_BASE": rec}, capture_output=True, text=True)
            self.assertEqual((r0.returncode, r0.stdout.strip(), marker.exists()), (0, rec, False))
            _write_files(src, {"b.txt": "2\n"}); c1 = _commit_all(src, "single")
            r1 = subprocess.run(["bash", "-c", script], cwd=src, env={**os.environ, "RECORDED_BASE": rec}, capture_output=True, text=True)
            self.assertEqual((r1.returncode, r1.stdout.strip()), (0, rec))
            _git(src, "checkout", "-b", "pr", c0); _write_files(src, {"p.txt": "3\n"}); _commit_all(src, "pr")
            _git(src, "checkout", "main"); _git(src, "merge", "--no-ff", "pr", "-m", "merge\n\n" + "parent deadbeef\n" * 200)
            r2 = subprocess.run(["bash", "-c", script], cwd=src, env={**os.environ, "RECORDED_BASE": rec}, capture_output=True, text=True)
            self.assertEqual((r2.returncode, r2.stdout.strip()), (0, c1))
            shallow = root / "shallow"; _git(root, "clone", "--depth=1", f"file://{src}", str(shallow))
            r3 = subprocess.run(["bash", "-c", script], cwd=shallow, env={**os.environ, "RECORDED_BASE": rec}, capture_output=True, text=True)
            self.assertEqual((r3.returncode, r3.stdout.strip()), (0, c1))
            cr_env = {"GIT_AUTHOR_NAME": f"Evil\rparent {'1'*40}\rparent {'2'*40}\rx", "GIT_COMMITTER_NAME": f"Evil\rparent {'1'*40}\rx"}
            _git(src, "checkout", "--orphan", "cr-orphan"); _write_files(src, {"z.txt": "z\n"}); _commit_all(src, "cr", env_extra=cr_env)
            rcr = subprocess.run(["bash", "-c", script], cwd=src, env={**os.environ, "RECORDED_BASE": rec}, capture_output=True, text=True)
            self.assertEqual((rcr.returncode, rcr.stdout.strip()), (0, rec))
    def test_audit_yml_fuzz_gate_dispatch_and_syntax(self) -> None:
        for wf_name in ("audit.yml", "audit-daily.yml"):
            blocks = _extract_run_blocks(REPO_ROOT / ".github" / "workflows" / wf_name)
            self.assertGreater(len(blocks), 5)
            for step_name, script in blocks:
                chk = subprocess.run(["bash", "-n"], input=script, text=True, capture_output=True)
                self.assertEqual(chk.returncode, 0, f"{wf_name} step {step_name!r}: {chk.stderr}")

        audit_blocks = dict(_extract_run_blocks(REPO_ROOT / ".github" / "workflows" / "audit.yml"))
        gate_script = audit_blocks["Run opt-in fuzz suites"]
        all_suites = [
            "selftest", "float", "cmdline", "envvars", "cryptohash", "passwd", "dns",
            "compress", "postfork", "sqlite", "git", "json", "toml", "uuid", "time", "sandbox", "timerand", "files",
            "process", "poll", "net",
        ]
        manifest = {"version": 1, "common_paths": [], "suites": {s: {"paths": [f"s/{s}/"]} for s in all_suites}}
        runner_body = "\n".join([
            f"#!{sys.executable}",
            "import json, os, sys",
            "args = sys.argv[1:]",
            "if args == ['--list-suites']:",
            "    print(os.environ['FAKE_SUITES'])",
            "    sys.exit(0)",
            "closed = []",
            "for fd in (0, 1, 2):",
            "    try: os.fstat(fd)",
            "    except OSError: closed.append(fd)",
            "with open(os.environ['FAKE_LOG'], 'a', encoding='utf-8') as f:",
            "    f.write(json.dumps({'args': args, 'closed': closed}) + '\\n')",
        ])
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            fake_bin = root / "bin"; fake_bin.mkdir()
            _make_script(fake_bin / "sudo", "exit 1")
            repo = root / "repo"; repo.mkdir(); _git(repo, "init", "-b", "main")
            _write_files(repo, {
                ".gitignore": "harness/.lake/\n",
                "harness/Fuzz/suites.json": json.dumps(manifest) + "\n",
                "README.md": "v0\n",
                **{f"s/{s}/f.lean": "def x := 0\n" for s in all_suites},
            })
            (repo / "scripts").mkdir(exist_ok=True)
            (repo / "scripts/fuzz_changed.py").write_text((REPO_ROOT / "scripts/fuzz_changed.py").read_text(encoding="utf-8"), encoding="utf-8")
            _commit_all(repo, "base")
            rp = repo / "harness/.lake/build/bin/leanswe-fuzz"
            rp.parent.mkdir(parents=True, exist_ok=True)
            rp.write_text(runner_body + "\n", encoding="utf-8")
            rp.chmod(rp.stat().st_mode | stat.S_IEXEC)

            def run_gate(
                event: str,
                pr_labels_json: str = "null",
                fuzz_suites: str = "",
                suites_out: list[str] | None = None,
            ) -> tuple[int, str, str, list[dict[str, object]], dict[str, str]]:
                log_p = root / "calls.jsonl"; log_p.unlink(missing_ok=True)
                out_p = root / "gh_out.txt"; out_p.unlink(missing_ok=True)
                env = {
                    **os.environ,
                    "PATH": f"{fake_bin}:{os.environ.get('PATH', '')}",
                    "GITHUB_EVENT_NAME": event,
                    "GITHUB_OUTPUT": str(out_p),
                    "PR_LABELS_JSON": pr_labels_json,
                    "INPUT_FUZZ_SUITES": fuzz_suites,
                    "FAKE_LOG": str(log_p),
                    "FAKE_SUITES": "\n".join(all_suites if suites_out is None else suites_out),
                }
                proc = subprocess.run(["bash", "-c", gate_script], cwd=repo, env=env, capture_output=True, text=True)
                calls = [json.loads(ln) for ln in log_p.read_text(encoding="utf-8").splitlines() if ln.strip()] if log_p.exists() else []
                outs = dict(ln.split("=", 1) for ln in out_p.read_text(encoding="utf-8").splitlines() if "=" in ln) if out_p.exists() else {}
                return proc.returncode, proc.stdout, proc.stderr, calls, outs

            # Default pull_request (no run-fuzz:* labels) and push skip all fuzz suites.
            for labels_json in ("[]", "null", "", json.dumps(["spec-change", "add-foreign-lang", "bug"])):
                rc, out, err, calls, outs = run_gate("pull_request", pr_labels_json=labels_json)
                self.assertEqual((rc, calls, outs), (0, [], {"run_files": "false"}), (labels_json, err))
                self.assertIn("selected_suites=none", out)
            rc, out, err, calls, outs = run_gate("push", pr_labels_json=json.dumps(["run-fuzz:net"]), fuzz_suites="net")
            self.assertEqual((rc, calls, outs), (0, [], {"run_files": "false"}), err)
            self.assertIn("selected_suites=none", out)

            # Single heavy PR label (run-fuzz:net): runs closed-stdio smoke + heavy net block only.
            rc, _, err, calls, outs = run_gate("pull_request", pr_labels_json=json.dumps(["run-fuzz:net"]))
            self.assertEqual((rc, outs), (0, {"run_files": "false"}), err)
            self.assertEqual(calls, [
                {"args": ["--smoke", "--suite", "net", "--self-test-shrink"], "closed": [0, 1, 2]},
                {"args": ["--net-strace-fault-check"], "closed": []},
                {"args": ["--suite", "net", "--steps", "50000", "--self-test-shrink", "--require-ns"], "closed": []},
                {"args": ["--suite", "net", "--seed", "11262680905236430927", "--steps", "50000", "--self-test-shrink", "--require-ns"], "closed": []},
                {"args": ["--suite", "net", "--steps", "50000", "--random-seed", "--self-test-shrink", "--require-ns"], "closed": []},
            ])

            # Multi-label PR (run-fuzz:net + run-fuzz:sqlite + unrelated label): exact subset, deterministic order, deduped.
            rc, out, err, calls, outs = run_gate("pull_request", pr_labels_json=json.dumps(["run-fuzz:net", "spec-add", "run-fuzz:sqlite", "run-fuzz:sqlite"]))
            self.assertEqual((rc, outs), (0, {"run_files": "false"}), err)
            self.assertIn("selected_suites=sqlite,net", out)
            self.assertEqual([c["args"] for c in calls], [
                ["--smoke", "--suite", "net", "--self-test-shrink"],
                ["--smoke", "--suite", "sqlite", "--self-test-shrink"],
                ["--net-strace-fault-check"],
                ["--suite", "net", "--steps", "50000", "--self-test-shrink", "--require-ns"],
                ["--suite", "net", "--seed", "11262680905236430927", "--steps", "50000", "--self-test-shrink", "--require-ns"],
                ["--suite", "net", "--steps", "50000", "--random-seed", "--self-test-shrink", "--require-ns"],
            ])
            self.assertEqual(calls[0]["closed"], [0, 1, 2]); self.assertEqual(calls[1]["closed"], [])

            # Light stdio label (passwd), heavy files label (run_files=true), postfork, sandbox, timerand, process.
            rc, _, err, calls, outs = run_gate("pull_request", pr_labels_json=json.dumps(["run-fuzz:passwd"]))
            self.assertEqual((rc, outs, calls), (0, {"run_files": "false"}, [
                {"args": ["--smoke", "--suite", "passwd", "--self-test-shrink"], "closed": [0, 1, 2]},
                {"args": ["--smoke", "--suite", "passwd", "--self-test-shrink"], "closed": []},
            ]), err)
            rc, _, err, calls, outs = run_gate("pull_request", pr_labels_json=json.dumps(["run-fuzz:files"]))
            self.assertEqual((rc, calls, outs), (0, [{"args": ["--smoke", "--suite", "files", "--self-test-shrink"], "closed": [0, 1, 2]}], {"run_files": "true"}), err)
            rc, _, err, calls, outs = run_gate("pull_request", pr_labels_json=json.dumps(["run-fuzz:postfork"]))
            self.assertEqual((rc, outs, calls), (0, {"run_files": "false"}, [
                {"args": ["--suite", "postfork", "--steps", "25000", "--self-test-shrink"], "closed": []},
                {"args": ["--suite", "postfork", "--steps", "25000", "--random-seed", "--self-test-shrink"], "closed": []},
                {"args": ["--suite", "postfork", "--steps", "500", "--self-test-shrink"], "closed": [0]},
            ]), err)
            for suite_name, flag in (("sandbox", "--sandbox-strace-fault-check"), ("timerand", "--timerand-strace-fault-check"), ("process", "--process-strace-fault-check")):
                rc, out, err, calls, outs = run_gate("pull_request", pr_labels_json=json.dumps([f"run-fuzz:{suite_name}"]))
                self.assertEqual((rc, outs), (0, {"run_files": "false"}), (suite_name, err))
                self.assertEqual(calls[0], {"args": ["--smoke", "--suite", suite_name, "--self-test-shrink"], "closed": [0, 1, 2]})
                self.assertEqual(calls[1]["args"], [flag])
                self.assertEqual(len(calls), 4, (suite_name, calls))
                self.assertEqual("vm.memfd_noexec" in out, suite_name == "sandbox")

            # Reject bare run-fuzz, wildcards, empty/unknown labels, bad casing, and malformed JSON (exit 2, 0 calls).
            for bad_lbl in ("run-fuzz", "RUN-FUZZ", " run-fuzz ", "run-fuzz:all", "run-fuzz:ALL", "run-fuzz:*", "run-fuzz:", "run-fuzz: ", "run-fuzz:bogus", "Run-Fuzz:net", " run-fuzz:net", "run-fuzz:net ", "run-fuzz:net,poll", "run-fuzz:$(id)"):
                rc_b, _, err_b, calls_b, outs_b = run_gate("pull_request", pr_labels_json=json.dumps(["run-fuzz:files", bad_lbl]))
                self.assertEqual((rc_b, calls_b, outs_b), (2, [], {}), (bad_lbl, err_b))
                self.assertIn("FUZZ_GATE_ERROR:", err_b)
            for bad_json in ("{not-json", '{"a":1}', "[123]"):
                rc_j, _, err_j, calls_j, _ = run_gate("pull_request", pr_labels_json=bad_json)
                self.assertEqual((rc_j, calls_j), (2, []), (bad_json, err_j))

            # workflow_dispatch: empty skips all fuzzing; explicit CSV runs exact subset; rejects wildcards/empties/dups/unknowns.
            for empty_in in ("", "   "):
                rc, out, err, calls, outs = run_gate("workflow_dispatch", fuzz_suites=empty_in)
                self.assertEqual((rc, calls, outs), (0, [], {"run_files": "false"}), err)
                self.assertIn("selected_suites=none", out)
            rc, out, err, calls, outs = run_gate("workflow_dispatch", fuzz_suites="poll, dns")
            self.assertEqual((rc, outs), (0, {"run_files": "false"}), err)
            self.assertIn("selected_suites=dns,poll", out)
            self.assertEqual(calls, [
                {"args": ["--smoke", "--suite", "dns", "--suite", "poll", "--self-test-shrink"], "closed": [0, 1, 2]},
                {"args": ["--smoke", "--suite", "dns", "--self-test-shrink"], "closed": []},
                {"args": ["--poll-strace-fault-check"], "closed": []},
                {"args": ["--suite", "poll", "--steps", "50000", "--self-test-shrink"], "closed": []},
                {"args": ["--suite", "poll", "--steps", "50000", "--random-seed", "--self-test-shrink"], "closed": []},
            ])
            rc, _, err, calls, outs = run_gate("workflow_dispatch", fuzz_suites="files,sqlite")
            self.assertEqual((rc, outs), (0, {"run_files": "true"}), err)
            self.assertEqual(calls, [
                {"args": ["--smoke", "--suite", "files", "--self-test-shrink"], "closed": [0, 1, 2]},
                {"args": ["--smoke", "--suite", "sqlite", "--self-test-shrink"], "closed": []},
            ])
            for bad_csv in ("all", "ALL", "*", "poll,all", "poll,*", "bogus", "poll,bogus", "poll,,dns", ",poll", "poll,", ",", "poll,poll", "run-fuzz:poll"):
                rc_c, _, err_c, calls_c, outs_c = run_gate("workflow_dispatch", fuzz_suites=bad_csv)
                self.assertEqual((rc_c, calls_c, outs_c), (2, [], {}), (bad_csv, err_c))
                self.assertIn("FUZZ_GATE_ERROR:", err_c)

            # Fail-closed errors: unsupported event and manifest drift abort with exit 2 and 0 fuzz calls.
            for bad_ev in ("", "schedule"):
                rc_e, _, err_e, calls_e, _ = run_gate(bad_ev)
                self.assertEqual((rc_e, calls_e), (2, []), (bad_ev, err_e))
            rc_dr, _, err_dr, calls_dr, _ = run_gate("pull_request", pr_labels_json="[]", suites_out=all_suites[:-1])
            self.assertEqual((rc_dr, calls_dr), (2, []), err_dr)

    def test_audit_yml_parallel_gates_runner(self) -> None:
        audit_blocks = dict(_extract_run_blocks(REPO_ROOT / ".github" / "workflows" / "audit.yml"))
        par_script = audit_blocks["Run post-build audit checks in parallel"]
        hold_hook = "\n".join([
            "if os.environ.get('HOLD_DIR'):",
            "    import pathlib as _pl, subprocess as _s",
            "    _p = _pl.Path(os.environ['HOLD_DIR']) / f'{lane}.json'",
            "    if os.environ.get('IGN_LANE') == lane:",
            "        _c = 'import json,os,pathlib,signal,sys,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); p=pathlib.Path(sys.argv[1]); t=p.with_suffix(\".t\"); t.write_text(json.dumps({\"pids\":[int(sys.argv[2]),int(sys.argv[3]),os.getpid()],\"pgid\":os.getpgrp()})); t.replace(p); time.sleep(60)'",
            "        _s.Popen([sys.executable, '-c', _c, str(_p), str(os.getppid()), str(os.getpid())])",
            "    else:",
            "        _g = _s.Popen(['sleep', '60']); _t = _p.with_suffix('.t'); _t.write_text(json.dumps({'pids': [os.getppid(), os.getpid(), _g.pid], 'pgid': os.getpgrp()})); _t.replace(_p)",
            "    time.sleep(60)",
        ])
        fake_lean_py = "\n".join([
            f"#!{sys.executable}",
            "import json, os, signal, sys, time",
            "args = sys.argv[1:]",
            "script = next((a for a in args if a.endswith('.lean')), '')",
            "tag = os.path.basename(script)",
            "if tag == 'CheckAssumptionsTest.lean': lane = '1'",
            "elif tag == 'CheckPromises.lean': lane = '2'",
            "elif tag == 'CheckAssumptions.lean': lane = '3'",
            "elif tag == 'CheckForeignThinness.lean': lane = '4'",
            "else: lane = '0'",
            hold_hook,
            "t_start = time.monotonic()",
            "if os.environ.get('STUB_DELAY'): time.sleep(float(os.environ['STUB_DELAY']))",
            "log_row = {'cmd': 'lean', 'args': args, 'threads': os.environ.get('LEAN_NUM_THREADS'), 'lake_marker': os.environ.get('LEAN_FAKE_MARKER'), 't': t_start, 't_end': time.monotonic()}",
            "if tag == 'CheckAssumptions.lean':",
            "    lp = args[args.index('--verify-log') + 1]",
            "    nc = args[args.index('--nonce') + 1]",
            "    log_row['log_text'] = open(lp, encoding='utf-8').read()",
            "    log_row['nonce'] = nc",
            "with open(os.environ['CALL_LOG'], 'a', encoding='utf-8') as f:",
            "    f.write(json.dumps(log_row) + '\\n')",
            "sys.stdout.write(f'OUT_LEAN_{tag}')",
            "if tag != 'CheckForeignThinness.lean': sys.stdout.write('\\n')",
            "sys.stdout.flush()",
            "if os.environ.get('KILL_LANE') == lane: os.kill(os.getpid(), signal.SIGKILL)",
            "if os.environ.get('KILL_SUBSHELL_LANE') == lane: os.kill(os.getppid(), signal.SIGKILL)",
            "if os.environ.get('FAIL_LANE') == lane: sys.exit(int(os.environ.get('FAIL_RC', '7')))",
        ])
        fake_test_py = "\n".join([
            f"#!{sys.executable}",
            "import json, os, sys, time",
            "args = sys.argv[1:]",
            "lane = '3'", hold_hook,
            "closed = []",
            "for fd in (0, 1, 2):",
            "    try: os.fstat(fd)",
            "    except OSError: closed.append(fd)",
            "with open(os.environ['CALL_LOG'], 'a', encoding='utf-8') as f:",
            "    f.write(json.dumps({'cmd': 'test', 'args': args, 'closed': closed, 'threads': os.environ.get('LEAN_NUM_THREADS'), 't': time.monotonic()}) + '\\n')",
            "if '--assump-log' in args:",
            "    lp = args[args.index('--assump-log') + 1]",
            "    nc = args[args.index('--assump-nonce') + 1]",
            "    if os.environ.get('EMPTY_ASSUMP_LOG') == '1': open(lp, 'w', encoding='utf-8').close()",
            "    else:",
            "        with open(lp, 'w', encoding='utf-8') as af: af.write(f'{nc}|LOG_INIT\\n{nc}|LOG_CLOSE\\n')",
            "    print('OUT_TEST_FULL')",
            "    if os.environ.get('FAIL_LANE') == '3_test': sys.exit(11)",
        ])
        fake_mut_py = "\n".join([
            f"#!{sys.executable}",
            "import json, os, sys, time",
            "args = sys.argv[1:]",
            "lane = '4'", hold_hook,
            "with open(os.environ['CALL_LOG'], 'a', encoding='utf-8') as f:",
            "    f.write(json.dumps({'cmd': 'mut', 'args': args, 'threads': os.environ.get('LEAN_NUM_THREADS'), 't': time.monotonic()}) + '\\n')",
            "print(f'OUT_MUT_{args[-1]}')",
            "if os.environ.get('FAIL_LANE') == '4_mut' and args[-1] == 'LinuxSyscall.Process': sys.exit(13)",
        ])
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            fake_bin = root / "bin"; fake_bin.mkdir()
            ws = root / "ws"; hbin = ws / "harness/.lake/build/bin"; hbin.mkdir(parents=True)
            _make_script(fake_bin / "bwrap", "exit 0")
            _make_script(fake_bin / "sudo", "exit 1")
            lake_cnt = root / "lake_env_calls"
            _make_script(fake_bin / "lake", f'echo x >> {shlex.quote(str(lake_cnt))}\nshift\nLEAN_FAKE_MARKER=yes exec "$@"')
            for p, body in ((fake_bin / "lean", fake_lean_py), (hbin / "lean-swe-test", fake_test_py), (hbin / "lean-swe-mut-test", fake_mut_py)):
                p.write_text(body + "\n", encoding="utf-8"); p.chmod(p.stat().st_mode | stat.S_IEXEC)

            def run_par(**extra: str) -> tuple[int, str, str, list[dict[str, object]], Path, Path]:
                call_log = root / "calls.jsonl"; call_log.unlink(missing_ok=True)
                lake_cnt.unlink(missing_ok=True)
                rtemp = root / "runner temp"; rtemp.mkdir(exist_ok=True)
                for f in list(rtemp.iterdir()):
                    if f.is_dir(): shutil.rmtree(f)
                    else: f.unlink()
                summary = root / "summary.md"; summary.unlink(missing_ok=True)
                env = {**os.environ, "PATH": f"{fake_bin}:{os.environ.get('PATH', '')}", "RUNNER_TEMP": str(rtemp), "GITHUB_STEP_SUMMARY": str(summary), "CALL_LOG": str(call_log), **extra}
                env.pop("LEAN_NUM_THREADS", None)
                proc = subprocess.run(["bash", "-c", par_script], cwd=ws, env=env, capture_output=True, text=True)
                rows = [json.loads(ln) for ln in call_log.read_text(encoding="utf-8").splitlines() if ln.strip()] if call_log.exists() else []
                return proc.returncode, proc.stdout, proc.stderr, rows, rtemp, summary

            # Happy path: exact 4 lanes, single lake env capture, LEAN_NUM_THREADS=1 only on lean, deterministic replay, no leftover state dir.
            rc, out, err, rows, rtemp, summary = run_par(STUB_DELAY="0.3")
            self.assertEqual(rc, 0, err)
            l1_row = next(r for r in rows if r["cmd"] == "lean" and "scripts/CheckAssumptionsTest.lean" in r["args"])
            l2_row = next(r for r in rows if r["cmd"] == "lean" and "scripts/CheckPromises.lean" in r["args"])
            self.assertLess(max(l1_row["t"], l2_row["t"]), min(l1_row["t_end"], l2_row["t_end"]))
            self.assertEqual(len(lake_cnt.read_text(encoding="utf-8").splitlines()), 1)
            self.assertIn("SANDBOX_PROBE:", summary.read_text(encoding="utf-8"))
            self.assertEqual([r["threads"] for r in rows if r["cmd"] == "lean"], ["1", "1", "1", "1"])
            self.assertTrue(all(r["lake_marker"] == "yes" for r in rows if r["cmd"] == "lean"))
            self.assertTrue(all(r["threads"] is None for r in rows if r["cmd"] in ("test", "mut")))
            assump_row = next(r for r in rows if r["cmd"] == "lean" and "scripts/CheckAssumptions.lean" in r["args"])
            self.assertRegex(str(assump_row["nonce"]), r"^[0-9a-f]{32}$")
            self.assertIn(f"{assump_row['nonce']}|LOG_INIT", str(assump_row["log_text"]))
            test_rows = [r for r in rows if r["cmd"] == "test"]
            self.assertEqual(len(test_rows), 2)
            self.assertEqual(test_rows[0]["closed"], []); self.assertEqual(test_rows[1]["closed"], [0, 1, 2])
            self.assertLess(test_rows[0]["t"], assump_row["t"]); self.assertLess(assump_row["t"], test_rows[1]["t"])
            mut_rows = [r for r in rows if r["cmd"] == "mut"]
            self.assertEqual(len(mut_rows), 4)
            self.assertEqual(mut_rows[0]["args"][-1], "Sqlite.Raw")
            self.assertEqual(mut_rows[1]["args"][-1], "Compress")
            self.assertEqual(mut_rows[3]["args"][-1], "LinuxSyscall.Process")
            for i in (1, 2, 3, 4):
                self.assertTrue((rtemp / f"lane-{i}.log").is_file())
            self.assertEqual(list(rtemp.glob("audit-state.*")), [])
            group_hdrs = [ln for ln in out.splitlines() if ln.startswith("::group::")]
            self.assertEqual(len(group_hdrs), 4)
            self.assertTrue(all(ln.startswith(f"::group::Lane {i}: ") for i, ln in enumerate(group_hdrs, 1)), group_hdrs)
            self.assertEqual(out.splitlines().count("::endgroup::"), 4)
            self.assertIn("OUT_LEAN_CheckForeignThinness.lean\n::endgroup::", out)
            self.assertIn("PARALLEL_AUDIT_GATES:", out)
            self.assertIn("l1_rc=0 l2_rc=0 l3_rc=0 l4_rc=0", out)

            # Every single lane failing individually fails closed with deterministic replay of all 4 groups.
            for lane, fail_rc in (("1", "3"), ("2", "5"), ("3", "7"), ("4", "9")):
                rc, out, _, _, _, _ = run_par(FAIL_LANE=lane, FAIL_RC=fail_rc)
                self.assertEqual(rc, int(fail_rc), (lane, out))
                self.assertEqual(len([ln for ln in out.splitlines() if ln.startswith("::group::Lane ")]), 4)
                self.assertEqual(out.splitlines().count("::endgroup::"), 4)
                self.assertIn(f"::error::Lane {lane}: ", out)
                self.assertIn(f"l{lane}_rc={fail_rc}", out)

            # Signal kill (SIGKILL -> 137) of child or lane subshell is caught and replayed with non-zero exit.
            rc, out, _, _, _, _ = run_par(KILL_LANE="2")
            self.assertEqual(rc, 137, out)
            self.assertIn("FAIL(rc=137,sig=9)", out)
            self.assertEqual(out.splitlines().count("::endgroup::"), 4)
            rc, out, _, _, _, _ = run_par(KILL_SUBSHELL_LANE="2")
            self.assertEqual(rc, 137, out)
            self.assertIn("[FAIL(rc=137,sig=9), unknown]", out)
            self.assertEqual(out.splitlines().count("::endgroup::"), 4)

            # Non-zero exit from Lane 3's lean-swe-test stops Lane 3 before CheckAssumptions.lean.
            rc, out, _, rows, _, _ = run_par(FAIL_LANE="3_test")
            self.assertEqual(rc, 11, out)
            self.assertFalse(any(r["cmd"] == "lean" and "scripts/CheckAssumptions.lean" in r["args"] for r in rows))

            # Empty ASSUMP_LOG aborts Lane 3 before CheckAssumptions.lean and closed-stdio run.
            rc, out, _, rows, _, _ = run_par(EMPTY_ASSUMP_LOG="1")
            self.assertEqual(rc, 1, out)
            self.assertIn("ASSUMP_LOG_ERROR:", out)
            self.assertFalse(any(r["cmd"] == "lean" and "scripts/CheckAssumptions.lean" in r["args"] for r in rows))
            self.assertEqual(len([r for r in rows if r["cmd"] == "test"]), 1)

            # Direct failure in mut-test stops Lane 4 before CheckForeignThinness.lean.
            rc, out, _, rows, _, _ = run_par(FAIL_LANE="4_mut")
            self.assertEqual(rc, 13, out)
            self.assertFalse(any(r["cmd"] == "lean" and "scripts/CheckForeignThinness.lean" in r["args"] for r in rows))

            # TERM / INT reaps lane subshells, children, and grandchild processes (including SIGTERM-ignoring survivor).
            for sig, exp_rc, ign_lane in ((signal.SIGTERM, 143, ""), (signal.SIGINT, 130, "1")):
                hold = root / f"hold_{exp_rc}"; shutil.rmtree(hold, ignore_errors=True); hold.mkdir()
                rtemp = root / f"rt_{exp_rc}"; shutil.rmtree(rtemp, ignore_errors=True); rtemp.mkdir()
                env = {**os.environ, "PATH": f"{fake_bin}:{os.environ.get('PATH', '')}", "RUNNER_TEMP": str(rtemp), "CALL_LOG": str(root / "calls.jsonl"), "HOLD_DIR": str(hold), "IGN_LANE": ign_lane}
                proc = subprocess.Popen(["bash", "-c", par_script], cwd=ws, env=env, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
                pids: list[int] = []; dead: set[int] = set()
                try:
                    t_end = time.monotonic() + 10.0
                    while len(list(hold.glob("[1-4].json"))) < 4:
                        self.assertLess(time.monotonic(), t_end, f"lanes hung before signal (poll={proc.poll()})")
                        time.sleep(0.02)
                    recs = [json.loads((hold / f"{i}.json").read_text(encoding="utf-8")) for i in (1, 2, 3, 4)]
                    pgids = [int(r["pgid"]) for r in recs]
                    self.assertEqual(len(set(pgids)), 4, recs); self.assertNotIn(proc.pid, pgids)
                    pids = [int(x) for r in recs for x in r["pids"]]
                    for pid in pids: os.kill(pid, 0)
                    proc.send_signal(sig); out, err = proc.communicate(timeout=10)
                    self.assertEqual(proc.returncode, exp_rc, (out, err))
                    for pid in pids:
                        dl = time.monotonic() + 0.5
                        while True:
                            try: os.kill(pid, 0)
                            except ProcessLookupError: dead.add(pid); break
                            if time.monotonic() >= dl: self.fail(f"leaked pid={pid} after sig={sig}")
                            time.sleep(0.01)
                    self.assertEqual(list(rtemp.glob("audit-state.*")), [])
                finally:
                    if proc.poll() is None: proc.kill(); proc.wait(timeout=5)
                    for pid in pids:
                        if pid not in dead:
                            try: os.kill(pid, signal.SIGKILL)
                            except OSError: pass

    def test_mutate_and_test_collects_sysbridge_and_relay_targets(self) -> None:
        import importlib.util; s = importlib.util.spec_from_file_location("mutate_and_test", REPO_ROOT / "scripts/mutate_and_test.py"); assert s and s.loader; m = importlib.util.module_from_spec(s); sys.modules["mutate_and_test"] = m; s.loader.exec_module(m)
        ts, _ = m.resolve_targets(REPO_ROOT, "ConnectProxy"); pt, _ = m.resolve_targets(REPO_ROOT, "Process")
        self.assertEqual([t.as_posix() for t in ts], ["LeanSwe/ConnectProxy/Impl.lean", "LeanSwe/ConnectProxy/Relay.lean", "LeanSwe/ConnectProxy/SysBridge/Driver.lean", "LeanSwe/ConnectProxy/SysBridge/SlotSteps.lean", "LeanSwe/ConnectProxy/SysBridge.lean"]); self.assertEqual([t.as_posix() for t in pt], ["LeanSwe/Process/Impl.lean"]); self.assertGreater(sum(len(m.generate_lean_mutants(t, (REPO_ROOT / t).read_text("utf-8"))) for t in ts), 50)

    def test_mutate_and_test_collects_split_impl_submodules(self) -> None:
        import importlib.util
        s = importlib.util.spec_from_file_location("mutate_and_test", REPO_ROOT / "scripts/mutate_and_test.py")
        assert s and s.loader
        m = importlib.util.module_from_spec(s)
        sys.modules["mutate_and_test"] = m
        s.loader.exec_module(m)
        gt, _ = m.resolve_targets(REPO_ROOT, "Git")
        self.assertEqual(
            [t.as_posix() for t in gt],
            [
                "LeanSwe/Git/Impl/Helpers.lean",
                "LeanSwe/Git/Impl/MutOps.lean",
                "LeanSwe/Git/Impl/QueryOps.lean",
                "LeanSwe/Git/Impl.lean",
            ],
        )
        self.assertGreater(
            sum(len(m.generate_lean_mutants(t, (REPO_ROOT / t).read_text("utf-8"))) for t in gt),
            100,
        )
if __name__ == "__main__": unittest.main()
