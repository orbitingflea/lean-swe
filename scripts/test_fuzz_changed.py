#!/usr/bin/env python3
"""Unit and git-integration tests for scripts/fuzz_changed.py and audit workflows."""

from __future__ import annotations

import copy, io, json, os, shlex, stat, subprocess, sys, tempfile, time, unittest
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
        self.assertEqual(fuzz_changed.build_smoke_command(".lake/build/bin/leanswe-fuzz", ["envvars", "cryptohash"], ["--self-test-shrink"]),
                         [".lake/build/bin/leanswe-fuzz", "--smoke", "--suite", "envvars", "--suite", "cryptohash", "--self-test-shrink"])

    def test_real_repo_manifest_and_workflows(self) -> None:
        manifest = fuzz_changed.load_manifest(REPO_ROOT / "Fuzz" / "suites.json")
        self.assertEqual(manifest.version, 1)
        self.assertNotIn("Fuzz/SelfTest.lean", manifest.common_paths)
        self.assertIn(".github/workflows/audit.yml", manifest.common_paths)
        self.assertIn(".github/actions/install-lean/action.yml", manifest.common_paths)
        by_name = {s.name: s for s in manifest.suites}
        self.assertIn("selftest", by_name); self.assertIn("float", by_name); self.assertIn("cmdline", by_name)
        self.assertIn("envvars", by_name); self.assertIn("cryptohash", by_name); self.assertIn("dns", by_name)
        self.assertIn("Core/", manifest.common_paths)
        self.assertIn("passwd", by_name); self.assertIn("sqlite", by_name)
        self.assertIn("LeanSwe/LinuxSyscall/Passwd/", by_name["passwd"].paths)
        self.assertIn("LeanSwe/LinuxSyscall/c/passwd_shim.c", by_name["passwd"].paths)
        self.assertIn("LeanSwe/LinuxSyscall/Common/", by_name["passwd"].paths)
        self.assertIn("postfork", by_name)
        self.assertIn("LeanSwe/LinuxSyscall/Common/", by_name["postfork"].paths)
        self.assertIn("LeanSwe/LinuxSyscall/c/fd_box.h", by_name["postfork"].paths)
        self.assertIn("Fuzz/SelfTest.lean", by_name["selftest"].paths)
        self.assertEqual(by_name["sqlite"].paths, ("LeanSwe/Sqlite/", "Fuzz/Sqlite/"))
        daily = (REPO_ROOT / ".github" / "workflows" / "audit-daily.yml").read_text(encoding="utf-8")
        self.assertIn("scripts/test_fuzz_changed.py", daily); self.assertIn("--check-manifest", daily)
        self.assertIn("leanswe-fuzz --all ", daily); self.assertNotIn("leanswe-fuzz --suite float ", daily)

class FuzzChangedGitIntegrationTests(unittest.TestCase):
    """End-to-end git history, symlink, submodule, locale, drift, and workflow tests."""

    def _init_repo(self, tmp: Path) -> tuple[Path, str]:
        repo = tmp / "repo"; repo.mkdir(); _git(repo, "init", "-b", "main")
        _write_files(repo, {
            "Fuzz/suites.json": json.dumps(SAMPLE_MANIFEST, indent=2) + "\n",
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
            _write_files(repo, {"Fuzz/suites.json": json.dumps(m_add) + "\n", "Fuzz/Sqlite/Suite.lean": "def s := 1\n"})
            add_sha = _commit_all(repo, "add sqlite")

            _git(repo, "checkout", "-b", "rem-common", base)
            m_rem = copy.deepcopy(SAMPLE_MANIFEST); m_rem["common_paths"] = ["Fuzz/Common/"]
            _write_files(repo, {"Fuzz/suites.json": json.dumps(m_rem) + "\n", "Fuzz/Main.lean": "def main := 42\n"})
            rem_sha = _commit_all(repo, "drop main from common")

            _git(repo, "checkout", "-b", "del-suite", base)
            m_del = copy.deepcopy(SAMPLE_MANIFEST); del m_del["suites"]["envvars"]
            _write_files(repo, {"Fuzz/suites.json": json.dumps(m_del) + "\n", "LeanSwe/EnvVars/Impl.lean": "def envImpl := 99\n"})
            del_sha = _commit_all(repo, "delete envvars suite")

            _git(repo, "checkout", base)
            self.assertEqual(self._run_cli(["--repo", str(repo), "--base", base, "--head", add_sha])[:2], (0, "sqlite\n"))
            self.assertEqual(self._run_cli(["--repo", str(repo), "--base", base, "--head", rem_sha])[:2], (0, "envvars\ncryptohash\n"))
            rc_del, _, err_del = self._run_cli(["--repo", str(repo), "--base", base, "--head", del_sha])
            self.assertEqual(rc_del, 2); self.assertIn("deleted from manifest: envvars", err_del)
            rc_ok, out_ok, err_ok = self._run_cli(["--repo", str(repo), "--base", base, "--head", del_sha, "--allow-deleted-suites"])
            self.assertEqual((rc_ok, out_ok.splitlines()), (0, [])); self.assertIn("FUZZ_CHANGED_WARN:", err_ok)

            sub = repo / "Fuzz"
            self.assertEqual(self._run_cli(["--repo", str(sub), "--manifest", str(repo / "Fuzz/suites.json"), "--base", base, "--head", add_sha])[:2], (0, "sqlite\n"))
            (repo / ".lake/build/bin").mkdir(parents=True)
            _make_script(repo / ".lake/build/bin/leanswe-fuzz", 'if [ "$1" = "--list-suites" ]; then printf "envvars\\ncryptohash\\n"; fi')
            self.assertEqual(self._run_cli(["--repo", str(sub), "--manifest", "suites.json", "--base", base, "--head", base, "--check-manifest"])[0], 0)
            self.assertEqual(self._run_cli(["--repo", str(sub), "--manifest", "suites.json", "--base", base, "--head", rem_sha, "--run"])[0], 0)
            link_sub = Path(tmpdir) / "link_to_fuzz"; os.symlink(str(sub), link_sub)
            _write_files(repo, {"Fuzz/suites.json": json.dumps(SAMPLE_MANIFEST) + "\n"})
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
            _write_files(repo, {"Fuzz/suites.json": json.dumps(m) + "\n", "Shared/common.lean": "def c := 1\n", "SharedDir/x.lean": "def x := 1\n", "RealLinked/Inner.lean": "def i := 1\n"})
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
            (repo / "Fuzz/suites.json").unlink(); os.symlink(str(bad_manifest), repo / "Fuzz/suites.json")
            _git(repo, "checkout", "-b", "edit-only", base); _write_files(repo, {"LeanSwe/EnvVars/Impl.lean": "def envImpl := 9\n"})
            _git(repo, "add", "LeanSwe/EnvVars/Impl.lean"); _git(repo, "commit", "-m", "edit env"); edit_sha = _git(repo, "rev-parse", "HEAD")
            self.assertEqual(self._run_cli(["--repo", str(repo), "--base", base, "--head", edit_sha])[:2], (0, "envvars\n"))
            (repo / "Fuzz/suites.json").unlink(); _git(repo, "checkout", "--", "Fuzz/suites.json")

            _git(repo, "checkout", "-b", "symlink-manifest", base); _write_files(repo, {"Fuzz/real_old.json": json.dumps(SAMPLE_MANIFEST) + "\n"})
            (repo / "Fuzz/suites.json").unlink(); os.symlink("real_old.json", repo / "Fuzz/suites.json"); sym_base = _commit_all(repo, "symlink manifest")
            (repo / "Fuzz/suites.json").unlink(); (repo / "Fuzz/real_old.json").unlink()
            _write_files(repo, {"Fuzz/suites.json": json.dumps(SAMPLE_MANIFEST) + "\n"}); sym_head = _commit_all(repo, "regular manifest")
            for co in (sym_base, sym_head):
                _git(repo, "checkout", co)
                rc_s, out_s, err_s = self._run_cli(["--repo", str(repo), "--base", sym_base, "--head", sym_head])
                self.assertEqual((rc_s, out_s.splitlines()), (0, ["envvars", "cryptohash"])); self.assertIn("base manifest unusable", err_s)
            rc_sh, _, err_sh = self._run_cli(["--repo", str(repo), "--base", sym_head, "--head", sym_base])
            self.assertEqual(rc_sh, 2); self.assertIn("not a regular file blob", err_sh)

            _git(repo, "checkout", "-b", "upgrade", base); _write_files(repo, {"Fuzz/suites.json": json.dumps({"version": 0, "suites": {}}) + "\n"})
            old_v0 = _commit_all(repo, "v0")
            m_utf8 = copy.deepcopy(SAMPLE_MANIFEST); m_utf8["suites"]["envvars"]["description"] = "em-dash \u2014 ok"
            _write_files(repo, {"Fuzz/suites.json": json.dumps(m_utf8, ensure_ascii=False) + "\n"}); new_v1 = _commit_all(repo, "v1")
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

if __name__ == "__main__":
    unittest.main()
