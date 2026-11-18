#!/usr/bin/env python3
"""Unit and git-integration tests for scripts/fuzz_changed.py."""

from __future__ import annotations

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
    return subprocess.check_output(["git", *args], cwd=repo, env=env, text=True).strip()


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
    """Pure manifest parsing and path matching tests."""

    def test_parse_manifest_rejects_bad_version_and_duplicate_keys(self) -> None:
        with self.assertRaises(ValueError):
            fuzz_changed.parse_manifest_text('{"version": 2, "suites": {}}')
        with self.assertRaises(ValueError):
            fuzz_changed.parse_manifest_text('{"version": 1, "suites": {}, "suites": {}}')
        with self.assertRaises(ValueError):
            fuzz_changed.parse_manifest_text('{"version": true, "suites": {}}')

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
            manifest = fuzz_changed.load_manifest(repo / "Fuzz/suites.json")
            diffs = fuzz_changed.compute_changed_suites(
                repo, base_sha, head_sha, manifest, "Fuzz/suites.json"
            )
            self.assertEqual([d.name for d in diffs if d.changed], [])

            rc = fuzz_changed.main(
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
            self.assertEqual(rc, 0)

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

            rc = fuzz_changed.main(
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
            recorded_args = log_path.read_text(encoding="utf-8").splitlines()
            self.assertEqual(recorded_args, ["--smoke", "--suite", "envvars"])

    def test_common_change_selects_all_suites(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            repo, base_sha = self._init_repo(Path(tmpdir))
            _write_files(
                repo,
                {
                    "Fuzz/Common/Rng.lean": "def rng := 2\n",
                },
            )
            head_sha = _commit_all(repo, "edit shared fuzz rng")
            manifest = fuzz_changed.load_manifest(repo / "Fuzz/suites.json")
            diffs = fuzz_changed.compute_changed_suites(
                repo, base_sha, head_sha, manifest, "Fuzz/suites.json"
            )
            self.assertEqual([d.name for d in diffs if d.changed], ["envvars", "cryptohash"])

    def test_reverted_edit_deduplicates_to_unchanged(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            repo, base_sha = self._init_repo(Path(tmpdir))
            _write_files(repo, {"LeanSwe/CryptoHash/Model.lean": "def chModel := 99\n"})
            _commit_all(repo, "temp edit")
            _write_files(repo, {"LeanSwe/CryptoHash/Model.lean": "def chModel := 1\n"})
            head_sha = _commit_all(repo, "revert edit")
            manifest = fuzz_changed.load_manifest(repo / "Fuzz/suites.json")
            diffs = fuzz_changed.compute_changed_suites(
                repo, base_sha, head_sha, manifest, "Fuzz/suites.json"
            )
            self.assertEqual([d.name for d in diffs if d.changed], [])


if __name__ == "__main__":
    unittest.main()
