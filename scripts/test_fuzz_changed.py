#!/usr/bin/env python3
"""Unit and git-integration tests for scripts/fuzz_changed.py."""

from __future__ import annotations

import copy
from contextlib import redirect_stderr, redirect_stdout
import io
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fuzz_changed


SAMPLE_MANIFEST = {
    "version": 1,
    "common_paths": [
        "Fuzz/Common/",
        "Fuzz/Main.lean",
    ],
    "suites": {
        "envvars": {
            "paths": [
                "LeanSwe/EnvVars/Impl.lean",
                "LeanSwe/EnvVars/Model.lean",
                "LeanSwe/EnvVars/Raw/",
                "Fuzz/EnvVars/",
            ]
        },
        "cryptohash": {
            "paths": [
                "LeanSwe/CryptoHash/Impl.lean",
                "LeanSwe/CryptoHash/Model.lean",
                "LeanSwe/CryptoHash/Raw/",
                "Fuzz/CryptoHash/",
            ]
        },
    },
}


def _git(repo: Path, *args: str) -> str:
    env = os.environ.copy()
    env.update(
        {
            "GIT_AUTHOR_NAME": "Test Author",
            "GIT_AUTHOR_EMAIL": "test@example.com",
            "GIT_COMMITTER_NAME": "Test Author",
            "GIT_COMMITTER_EMAIL": "test@example.com",
        }
    )
    return subprocess.check_output(["git", *args], cwd=repo, env=env, stderr=subprocess.DEVNULL, text=True).strip()


def _write_files(repo: Path, files: dict[str, str]) -> None:
    for rel, content in files.items():
        path = repo / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")


def _commit_all(repo: Path, message: str) -> str:
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", message)
    return _git(repo, "rev-parse", "HEAD")


class FuzzChangedUnitTests(unittest.TestCase):
    """Pure manifest parsing, validation, and path matching tests."""

    def test_parse_manifest_rejects_bad_version_duplicate_keys_and_bad_paths(self) -> None:
        with self.assertRaises(ValueError):
            fuzz_changed.parse_manifest_text('{"version": 2, "suites": {}}')
        with self.assertRaises(ValueError):
            fuzz_changed.parse_manifest_text('{"version": 1, "suites": {}, "suites": {}}')
        with self.assertRaises(ValueError):
            fuzz_changed.parse_manifest_text('{"version": true, "suites": {}}')
        for bad_path in ("./", "/abs/path", "a//b", "a\\b", "../escape", "Fuzz/Common/ ", ""):
            bad = copy.deepcopy(SAMPLE_MANIFEST)
            bad["common_paths"] = [bad_path]
            with self.assertRaises(ValueError):
                fuzz_changed.parse_manifest_text(json.dumps(bad))

    def test_validate_git_rev_rejects_flags_and_whitespace(self) -> None:
        for bad_rev in ("", "-h", "--upload-pack=evil", "HEAD\x00", "main branch", " main"):
            with self.assertRaises(ValueError):
                fuzz_changed.validate_git_rev(bad_rev)

    def test_path_matching_boundary_safety(self) -> None:
        self.assertTrue(fuzz_changed.path_matches_pattern("Fuzz/Common/Rng.lean", "Fuzz/Common/"))
        self.assertFalse(fuzz_changed.path_matches_pattern("Fuzz/CommonExtra/Foo.lean", "Fuzz/Common/"))
        self.assertTrue(fuzz_changed.path_matches_pattern("LeanSwe/EnvVars/Impl.lean", "LeanSwe/EnvVars/Impl.lean"))
        self.assertFalse(fuzz_changed.path_matches_pattern("LeanSwe/EnvVarsExtra/Impl.lean", "LeanSwe/EnvVars"))
        self.assertTrue(fuzz_changed.path_matches_pattern("LeanSwe/LinuxSyscall/c/sandbox_shim.c", "LeanSwe/LinuxSyscall/c/*.c"))

    def test_build_smoke_command(self) -> None:
        cmd = fuzz_changed.build_smoke_command(
            ".lake/build/bin/leanswe-fuzz",
            ["envvars", "cryptohash"],
            ["--self-test-shrink"],
        )
        self.assertEqual(
            cmd,
            [
                ".lake/build/bin/leanswe-fuzz",
                "--smoke",
                "--suite",
                "envvars",
                "--suite",
                "cryptohash",
                "--self-test-shrink",
            ],
        )


class FuzzChangedGitIntegrationTests(unittest.TestCase):
    """End-to-end git history and runner invocation tests."""

    def _init_repo(self, tmp: Path) -> tuple[Path, str]:
        repo = tmp / "repo"
        repo.mkdir()
        _git(repo, "init", "-b", "main")
        _write_files(
            repo,
            {
                "Fuzz/suites.json": json.dumps(SAMPLE_MANIFEST, indent=2) + "\n",
                "Fuzz/Common/Rng.lean": "def rng := 1\n",
                "Fuzz/Main.lean": "def main := 0\n",
                "LeanSwe/EnvVars/Impl.lean": "def envImpl := 1\n",
                "LeanSwe/EnvVars/Model.lean": "def envModel := 1\n",
                "LeanSwe/EnvVars/Proofs.lean": "theorem envProof : True := trivial\n",
                "LeanSwe/EnvVars/Raw/c/envvars_shim.c": "int f(void) { return 0; }\n",
                "Fuzz/EnvVars/Suite.lean": "def envSuite := 1\n",
                "LeanSwe/CryptoHash/Impl.lean": "def chImpl := 1\n",
                "LeanSwe/CryptoHash/Model.lean": "def chModel := 1\n",
                "LeanSwe/CryptoHash/Raw/c/cryptohash_shim.c": "int g(void) { return 0; }\n",
                "Fuzz/CryptoHash/Suite.lean": "def chSuite := 1\n",
                "LeanSwe/Tar/Impl.lean": "def tarImpl := 1\n",
                "README.md": "hello\n",
            },
        )
        base_sha = _commit_all(repo, "initial commit")
        return repo, base_sha

    def _run_cli(self, argv: list[str]) -> tuple[int, str, str]:
        out_buf = io.StringIO()
        err_buf = io.StringIO()
        with redirect_stdout(out_buf), redirect_stderr(err_buf):
            rc = fuzz_changed.main(argv)
        return rc, out_buf.getvalue(), err_buf.getvalue()

    def test_unrelated_changes_yield_empty_and_exit_zero_on_run(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            repo, base_sha = self._init_repo(Path(tmpdir))
            _write_files(
                repo,
                {
                    "README.md": "updated docs\n",
                    "LeanSwe/Tar/Impl.lean": "def tarImpl := 2\n",
                    "LeanSwe/EnvVars/Proofs.lean": "theorem envProof : 1 = 1 := rfl\n",
                },
            )
            head_sha = _commit_all(repo, "unrelated edits")
            rc, out, _ = self._run_cli(["--repo", str(repo), "--base", base_sha, "--head", head_sha])
            self.assertEqual(rc, 0)
            self.assertEqual(out.splitlines(), [])

            rc_run, out_run, _ = self._run_cli(
                [
                    "--repo",
                    str(repo),
                    "--base",
                    base_sha,
                    "--head",
                    head_sha,
                    "--run",
                    "--runner",
                    "/nonexistent/leanswe-fuzz",
                ]
            )
            self.assertEqual(rc_run, 0)
            self.assertIn("FUZZ_CHANGED: none", out_run)

    def test_single_package_change_selects_only_that_suite(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            repo, base_sha = self._init_repo(Path(tmpdir))
            _write_files(
                repo,
                {
                    "LeanSwe/EnvVars/Raw/c/envvars_shim.c": "int f(void) { return 1; }\n",
                },
            )
            head_sha = _commit_all(repo, "edit envvars c shim")

            fake_runner = repo / "fake-fuzz.sh"
            log_path = repo / "runner-args.txt"
            fake_runner.write_text(
                f"#!/bin/sh\nprintf '%s\\n' \"$@\" > {json.dumps(str(log_path))}\n",
                encoding="utf-8",
            )
            fake_runner.chmod(fake_runner.stat().st_mode | stat.S_IEXEC)

            rc, _, _ = self._run_cli(
                [
                    "--repo",
                    str(repo),
                    "--base",
                    base_sha,
                    "--head",
                    head_sha,
                    "--run",
                    "--runner",
                    str(fake_runner),
                ]
            )
            self.assertEqual(rc, 0)
            self.assertEqual(log_path.read_text(encoding="utf-8").splitlines(), ["--smoke", "--suite", "envvars"])

    def test_common_change_selects_all_suites(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            repo, base_sha = self._init_repo(Path(tmpdir))
            _write_files(repo, {"Fuzz/Common/Rng.lean": "def rng := 2\n"})
            head_sha = _commit_all(repo, "edit shared fuzz rng")
            rc, out, _ = self._run_cli(["--repo", str(repo), "--base", base_sha, "--head", head_sha])
            self.assertEqual(rc, 0)
            self.assertEqual(out.splitlines(), ["envvars", "cryptohash"])

    def test_reverted_edit_deduplicates_to_unchanged(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            repo, base_sha = self._init_repo(Path(tmpdir))
            _write_files(repo, {"LeanSwe/CryptoHash/Model.lean": "def chModel := 99\n"})
            _commit_all(repo, "temp edit")
            _write_files(repo, {"LeanSwe/CryptoHash/Model.lean": "def chModel := 1\n"})
            head_sha = _commit_all(repo, "revert edit")
            rc, out, _ = self._run_cli(["--repo", str(repo), "--base", base_sha, "--head", head_sha])
            self.assertEqual(rc, 0)
            self.assertEqual(out.splitlines(), [])

    def test_deleted_and_renamed_watched_files_trigger_only_affected_suite(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            repo, base_sha = self._init_repo(Path(tmpdir))
            _git(repo, "rm", "Fuzz/EnvVars/Suite.lean")
            del_sha = _commit_all(repo, "delete envvars suite file")
            rc_del, out_del, _ = self._run_cli(["--repo", str(repo), "--base", base_sha, "--head", del_sha])
            self.assertEqual(rc_del, 0)
            self.assertEqual(out_del.splitlines(), ["envvars"])

            _git(repo, "checkout", "-b", "rename-test", base_sha)
            _git(repo, "mv", "Fuzz/CryptoHash/Suite.lean", "Fuzz/CryptoHash/SuiteRenamed.lean")
            ren_sha = _commit_all(repo, "rename cryptohash file keeping same blob sha")
            rc_ren, out_ren, _ = self._run_cli(["--repo", str(repo), "--base", base_sha, "--head", ren_sha])
            self.assertEqual(rc_ren, 0)
            self.assertEqual(out_ren.splitlines(), ["cryptohash"])

    def test_head_manifest_used_while_checked_out_at_base_and_common_paths_removal_detected(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            repo, base_sha = self._init_repo(Path(tmpdir))
            _git(repo, "checkout", "-b", "add-suite", base_sha)
            new_manifest = copy.deepcopy(SAMPLE_MANIFEST)
            new_manifest["suites"]["sqlite"] = {"paths": ["LeanSwe/Sqlite/Model.lean", "Fuzz/Sqlite/"]}
            _write_files(
                repo,
                {
                    "Fuzz/suites.json": json.dumps(new_manifest, indent=2) + "\n",
                    "Fuzz/Sqlite/Suite.lean": "def sqliteSuite := 1\n",
                },
            )
            add_sha = _commit_all(repo, "add sqlite suite")

            _git(repo, "checkout", "-b", "remove-common", base_sha)
            shrunk_common = copy.deepcopy(SAMPLE_MANIFEST)
            shrunk_common["common_paths"] = ["Fuzz/Common/"]
            _write_files(
                repo,
                {
                    "Fuzz/suites.json": json.dumps(shrunk_common, indent=2) + "\n",
                    "Fuzz/Main.lean": "def main := 42\n",
                },
            )
            rem_sha = _commit_all(repo, "drop Fuzz/Main.lean from common_paths while editing it")

            _git(repo, "checkout", base_sha)
            rc_add, out_add, _ = self._run_cli(["--repo", str(repo), "--base", base_sha, "--head", add_sha])
            self.assertEqual(rc_add, 0)
            self.assertEqual(out_add.splitlines(), ["sqlite"])

            rc_rem, out_rem, _ = self._run_cli(["--repo", str(repo), "--base", base_sha, "--head", rem_sha])
            self.assertEqual(rc_rem, 0)
            self.assertEqual(out_rem.splitlines(), ["envvars", "cryptohash"])

    def test_missing_runner_and_bad_rev_return_exit_2_cleanly(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            repo, base_sha = self._init_repo(Path(tmpdir))
            _write_files(repo, {"LeanSwe/EnvVars/Impl.lean": "def envImpl := 2\n"})
            head_sha = _commit_all(repo, "edit envvars")

            rc_runner, _, err_runner = self._run_cli(
                [
                    "--repo",
                    str(repo),
                    "--base",
                    base_sha,
                    "--head",
                    head_sha,
                    "--run",
                    "--runner",
                    "/nonexistent/leanswe-fuzz",
                ]
            )
            self.assertEqual(rc_runner, 2)
            self.assertIn("FUZZ_CHANGED_ERROR:", err_runner)

            rc_rev, _, err_rev = self._run_cli(["--repo", str(repo), "--base=-bad", "--head", head_sha])
            self.assertEqual(rc_rev, 2)
            self.assertIn("FUZZ_CHANGED_ERROR:", err_rev)


if __name__ == "__main__":
    unittest.main()
