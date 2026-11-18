#!/usr/bin/env python3
"""Unit and git-integration tests for the .foreign-budget.json one-way ratchet in check_spec_change.py."""

from __future__ import annotations

import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_spec_change


BASE_BUDGET = {
    "version": 1,
    "files": {
        "LeanSwe/EnvVars/Raw/c/envvars_shim.c": {
            "max_lines": 46,
            "legacy_unmigrated": False,
        },
        "LeanSwe/CryptoHash/Raw/c/cryptohash_shim.c": {
            "max_lines": 190,
            "legacy_unmigrated": False,
        },
        "LeanSwe/Fs/Raw/c/fs_shim.c": {
            "max_lines": 1011,
            "legacy_unmigrated": True,
        },
    },
    "vendored_files": {
        "LeanSwe/Sqlite/Raw/c/sqlite3.c": {
            "sha256": "0c657666d819f261cc4007526ad57e1669de9949df7a8ea847aa284a2bf0ee52",
            "max_lines": 271131,
        }
    },
    "function_overrides": {
        "LeanSwe/EnvVars/Raw/c/envvars_shim.c::leanswe_envvars_environ": {
            "allow_array_copy_loop": True,
        },
        "LeanSwe/CryptoHash/Raw/c/cryptohash_shim.c::leanswe_cryptohash_hmac_sha256": {
            "max_code_lines": 54,
            "max_branches": 10,
        },
    },
    "named_thread_helpers": [
        "LeanSwe/ConnectProxy/Raw/c/cproxy_shim.c::start_dns_worker",
    ],
}


def _dump(obj: dict) -> str:
    return json.dumps(obj, indent=2) + "\n"


def _git(cwd: Path, *args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=cwd, text=True).strip()


class ForeignBudgetRatchetUnitTests(unittest.TestCase):
    """Pure ratchet tests via classify_foreign_budget_texts."""

    def test_unchanged_passes(self) -> None:
        self.assertIsNone(check_spec_change.classify_foreign_budget_texts(_dump(BASE_BUDGET), _dump(BASE_BUDGET)))

    def test_tighten_directions_pass(self) -> None:
        tightened = copy.deepcopy(BASE_BUDGET)
        tightened["files"]["LeanSwe/EnvVars/Raw/c/envvars_shim.c"]["max_lines"] = 40
        del tightened["files"]["LeanSwe/CryptoHash/Raw/c/cryptohash_shim.c"]
        tightened["files"]["LeanSwe/Fs/Raw/c/fs_shim.c"]["legacy_unmigrated"] = False
        tightened["function_overrides"]["LeanSwe/CryptoHash/Raw/c/cryptohash_shim.c::leanswe_cryptohash_hmac_sha256"] = {
            "max_code_lines": 48,
            "max_branches": 8,
        }
        del tightened["function_overrides"]["LeanSwe/EnvVars/Raw/c/envvars_shim.c::leanswe_envvars_environ"]
        tightened["named_thread_helpers"] = []
        self.assertIsNone(check_spec_change.classify_foreign_budget_texts(_dump(BASE_BUDGET), _dump(tightened)))

    def test_add_file_requires_spec_change(self) -> None:
        head = copy.deepcopy(BASE_BUDGET)
        head["files"]["scripts/new_tool.py"] = {"max_lines": 10, "legacy_unmigrated": False}
        err = check_spec_change.classify_foreign_budget_texts(_dump(BASE_BUDGET), _dump(head))
        self.assertIsNotNone(err)
        self.assertIn("added foreign budget entry", err or "")

    def test_raise_max_lines_requires_spec_change(self) -> None:
        head = copy.deepcopy(BASE_BUDGET)
        head["files"]["LeanSwe/EnvVars/Raw/c/envvars_shim.c"]["max_lines"] = 47
        err = check_spec_change.classify_foreign_budget_texts(_dump(BASE_BUDGET), _dump(head))
        self.assertIsNotNone(err)
        self.assertIn("raised max_lines", err or "")

    def test_loosen_legacy_unmigrated_requires_spec_change(self) -> None:
        head = copy.deepcopy(BASE_BUDGET)
        head["files"]["LeanSwe/EnvVars/Raw/c/envvars_shim.c"]["legacy_unmigrated"] = True
        err = check_spec_change.classify_foreign_budget_texts(_dump(BASE_BUDGET), _dump(head))
        self.assertIsNotNone(err)
        self.assertIn("loosened legacy_unmigrated", err or "")

    def test_change_vendored_sha256_requires_spec_change(self) -> None:
        head = copy.deepcopy(BASE_BUDGET)
        head["vendored_files"]["LeanSwe/Sqlite/Raw/c/sqlite3.c"]["sha256"] = "a" * 64
        err = check_spec_change.classify_foreign_budget_texts(_dump(BASE_BUDGET), _dump(head))
        self.assertIsNotNone(err)
        self.assertIn("changed vendored sha256", err or "")

    def test_add_or_loosen_function_override_requires_spec_change(self) -> None:
        head_add = copy.deepcopy(BASE_BUDGET)
        head_add["function_overrides"]["LeanSwe/EnvVars/Raw/c/envvars_shim.c::mk_byte_array"] = {"max_code_lines": 40}
        self.assertIsNotNone(check_spec_change.classify_foreign_budget_texts(_dump(BASE_BUDGET), _dump(head_add)))

        head_raise = copy.deepcopy(BASE_BUDGET)
        head_raise["function_overrides"]["LeanSwe/CryptoHash/Raw/c/cryptohash_shim.c::leanswe_cryptohash_hmac_sha256"][
            "max_branches"
        ] = 11
        self.assertIsNotNone(check_spec_change.classify_foreign_budget_texts(_dump(BASE_BUDGET), _dump(head_raise)))

        head_loop = copy.deepcopy(BASE_BUDGET)
        head_loop["function_overrides"]["LeanSwe/CryptoHash/Raw/c/cryptohash_shim.c::leanswe_cryptohash_hmac_sha256"][
            "allow_array_copy_loop"
        ] = True
        self.assertIsNotNone(check_spec_change.classify_foreign_budget_texts(_dump(BASE_BUDGET), _dump(head_loop)))

    def test_delete_tighter_override_or_max_loops_zero_requires_add_foreign_lang(self) -> None:
        base_tight = copy.deepcopy(BASE_BUDGET)
        base_tight["function_overrides"]["LeanSwe/EnvVars/Raw/c/envvars_shim.c::mk_byte_array"] = {
            "max_code_lines": 20,
        }
        head_del = copy.deepcopy(BASE_BUDGET)
        err_del = check_spec_change.classify_foreign_budget_texts(_dump(base_tight), _dump(head_del))
        self.assertIsNotNone(err_del)
        self.assertIn("raised max_code_lines", err_del or "")

        base_zero = copy.deepcopy(BASE_BUDGET)
        base_zero["function_overrides"]["LeanSwe/EnvVars/Raw/c/envvars_shim.c::leanswe_envvars_environ"] = {
            "allow_array_copy_loop": True,
            "max_loops": 0,
        }
        head_drop_zero = copy.deepcopy(BASE_BUDGET)
        err_loop = check_spec_change.classify_foreign_budget_texts(_dump(base_zero), _dump(head_drop_zero))
        self.assertIsNotNone(err_loop)
        self.assertIn("loosened loop allowance", err_loop or "")

    def test_add_named_thread_helper_requires_spec_change(self) -> None:
        head = copy.deepcopy(BASE_BUDGET)
        head["named_thread_helpers"].append("LeanSwe/ProcessSandbox/Raw/c/psandbox_shim.c::spawn_helper")
        err = check_spec_change.classify_foreign_budget_texts(_dump(BASE_BUDGET), _dump(head))
        self.assertIsNotNone(err)
        self.assertIn("added named_thread_helpers", err or "")

    def test_duplicate_keys_and_non_int_version_rejected(self) -> None:
        base_text = _dump(BASE_BUDGET)
        dup_text = base_text.replace(
            '"max_lines": 46,',
            '"max_lines": 9999,\n      "max_lines": 46,',
            1,
        )
        err_dup = check_spec_change.classify_foreign_budget_texts(base_text, dup_text)
        self.assertIsNotNone(err_dup)
        self.assertIn("duplicate JSON key", err_dup or "")

        nan_text = base_text.replace('"max_lines": 46,', '"max_lines": NaN,', 1)
        err_nan = check_spec_change.classify_foreign_budget_texts(base_text, nan_text)
        self.assertIsNotNone(err_nan)
        self.assertIn("invalid JSON", err_nan or "")

        bool_ver = copy.deepcopy(BASE_BUDGET)
        bool_ver["version"] = True
        err_bool = check_spec_change.classify_foreign_budget_texts(base_text, _dump(bool_ver))
        self.assertIsNotNone(err_bool)
        self.assertIn("version", err_bool or "")

        float_ver = copy.deepcopy(BASE_BUDGET)
        float_ver["version"] = 1.0
        err_float = check_spec_change.classify_foreign_budget_texts(base_text, _dump(float_ver))
        self.assertIsNotNone(err_float)
        self.assertIn("version", err_float or "")

    def test_allow_poll_override_ratchet(self) -> None:
        head_add = copy.deepcopy(BASE_BUDGET)
        head_add["function_overrides"]["LeanSwe/CryptoHash/Raw/c/cryptohash_shim.c::leanswe_cryptohash_hmac_sha256"][
            "allow_poll"
        ] = True
        err_add = check_spec_change.classify_foreign_budget_texts(_dump(BASE_BUDGET), _dump(head_add))
        self.assertIsNotNone(err_add)
        self.assertIn("allow_poll", err_add or "")
        self.assertIsNone(check_spec_change.classify_foreign_budget_texts(_dump(head_add), _dump(BASE_BUDGET)))


class ForeignBudgetRatchetCliTests(unittest.TestCase):
    """End-to-end CLI tests in an isolated git repository."""

    def _run_cli(self, repo: Path, base: str, head: str, *extra_args: str) -> subprocess.CompletedProcess[str]:
        script = Path(__file__).resolve().parent / "check_spec_change.py"
        env = {k: v for k, v in os.environ.items() if k != "GITHUB_EVENT_PATH"}
        return subprocess.run(
            [sys.executable, "-B", str(script), "--base", base, "--head", head, *extra_args],
            cwd=repo,
            env=env,
            capture_output=True,
            text=True,
        )

    def _init_repo(self, tmp: str) -> Path:
        repo = Path(tmp)
        _git(repo, "init")
        _git(repo, "config", "user.name", "Test")
        _git(repo, "config", "user.email", "test@example.com")
        (repo / "LeanSwe" / "Demo").mkdir(parents=True)
        (repo / "LeanSwe" / "Demo" / "Types.lean").write_text("def x : Nat := 1\n", encoding="utf-8")
        (repo / ".foreign-budget.json").write_text(_dump(BASE_BUDGET), encoding="utf-8")
        _git(repo, "add", ".")
        _git(repo, "commit", "-m", "base")
        return repo

    def test_tighten_passes_without_label_and_with_spec_add(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_repo(tmp)
            tightened = copy.deepcopy(BASE_BUDGET)
            tightened["files"]["LeanSwe/EnvVars/Raw/c/envvars_shim.c"]["max_lines"] = 42
            tightened["files"]["LeanSwe/Fs/Raw/c/fs_shim.c"]["legacy_unmigrated"] = False
            (repo / ".foreign-budget.json").write_text(_dump(tightened), encoding="utf-8")
            _git(repo, "add", ".foreign-budget.json")
            _git(repo, "commit", "-m", "tighten")

            res_no_lbl = self._run_cli(repo, "HEAD~1", "HEAD")
            self.assertEqual(res_no_lbl.returncode, 0, res_no_lbl.stderr)
            self.assertIn("foreign-budget tightened", res_no_lbl.stdout)

            (repo / "LeanSwe" / "Demo" / "Types.lean").write_text(
                "def x : Nat := 1\ndef y : Nat := 2\n", encoding="utf-8"
            )
            _git(repo, "add", "LeanSwe/Demo/Types.lean")
            _git(repo, "commit", "-m", "spec-add plus tighten")
            res_add = self._run_cli(repo, "HEAD~2", "HEAD", "--label", "spec-add")
            self.assertEqual(res_add.returncode, 0, res_add.stderr)

    def test_loosen_and_add_file_fail_without_add_foreign_lang_and_pass_with_label(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_repo(tmp)
            loosened = copy.deepcopy(BASE_BUDGET)
            loosened["files"]["LeanSwe/EnvVars/Raw/c/envvars_shim.c"]["max_lines"] = 50
            (repo / ".foreign-budget.json").write_text(_dump(loosened), encoding="utf-8")
            _git(repo, "add", ".foreign-budget.json")
            _git(repo, "commit", "-m", "loosen")

            res_fail = self._run_cli(repo, "HEAD~1", "HEAD")
            self.assertNotEqual(res_fail.returncode, 0)
            self.assertIn("UNMARKED_FOREIGN_BUDGET", res_fail.stderr)

            res_spec_change_fail = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change")
            self.assertNotEqual(res_spec_change_fail.returncode, 0)
            self.assertIn("UNMARKED_FOREIGN_BUDGET", res_spec_change_fail.stderr)

            res_add_fail = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add")
            self.assertNotEqual(res_add_fail.returncode, 0)
            self.assertIn("UNMARKED_FOREIGN_BUDGET", res_add_fail.stderr)

            res_ok = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "add-foreign-lang")
            self.assertEqual(res_ok.returncode, 0, res_ok.stderr)

            added = copy.deepcopy(BASE_BUDGET)
            added["files"]["scripts/extra.sh"] = {"max_lines": 12, "legacy_unmigrated": False}
            (repo / ".foreign-budget.json").write_text(_dump(added), encoding="utf-8")
            _git(repo, "add", ".foreign-budget.json")
            _git(repo, "commit", "-m", "add file")

            res_add_entry_fail = self._run_cli(repo, "HEAD~2", "HEAD")
            self.assertNotEqual(res_add_entry_fail.returncode, 0)
            res_add_entry_ok = self._run_cli(repo, "HEAD~2", "HEAD", "--label", "add-foreign-lang")
            self.assertEqual(res_add_entry_ok.returncode, 0, res_add_entry_ok.stderr)

    def test_orthogonality_between_add_foreign_lang_and_spec_change(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_repo(tmp)
            (repo / "LeanSwe" / "Demo" / "Types.lean").write_text("def x : Nat := 99\n", encoding="utf-8")
            loosened = copy.deepcopy(BASE_BUDGET)
            loosened["files"]["LeanSwe/EnvVars/Raw/c/envvars_shim.c"]["max_lines"] = 50
            (repo / ".foreign-budget.json").write_text(_dump(loosened), encoding="utf-8")
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "modify locked spec and loosen budget")

            res_foreign_only = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "add-foreign-lang")
            self.assertNotEqual(res_foreign_only.returncode, 0)
            self.assertIn("UNMARKED_SPEC_CHANGE", res_foreign_only.stderr)

            res_spec_only = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change")
            self.assertNotEqual(res_spec_only.returncode, 0)
            self.assertIn("UNMARKED_FOREIGN_BUDGET", res_spec_only.stderr)

            res_both = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change,add-foreign-lang")
            self.assertEqual(res_both.returncode, 0, res_both.stderr)

            event_path = repo / "event.json"
            event_path.write_text(
                json.dumps({"pull_request": {"labels": [{"name": "spec-change"}, {"name": "add-foreign-lang"}]}}),
                encoding="utf-8",
            )
            res_event = self._run_cli(repo, "HEAD~1", "HEAD", "--event-path", str(event_path))
            self.assertEqual(res_event.returncode, 0, res_event.stderr)

    def test_delete_or_rename_foreign_budget_requires_add_foreign_lang(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_repo(tmp)
            _git(repo, "mv", ".foreign-budget.json", ".foreign-budget.bak.json")
            _git(repo, "commit", "-m", "rename budget")

            res_mv_fail = self._run_cli(repo, "HEAD~1", "HEAD")
            self.assertNotEqual(res_mv_fail.returncode, 0)
            self.assertIn("UNMARKED_FOREIGN_BUDGET", res_mv_fail.stderr)
            res_mv_ok = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "add-foreign-lang")
            self.assertEqual(res_mv_ok.returncode, 0, res_mv_ok.stderr)

            _git(repo, "mv", ".foreign-budget.bak.json", ".foreign-budget.json")
            _git(repo, "commit", "-m", "restore budget")
            _git(repo, "rm", ".foreign-budget.json")
            _git(repo, "commit", "-m", "delete budget")

            res_del_fail = self._run_cli(repo, "HEAD~1", "HEAD")
            self.assertNotEqual(res_del_fail.returncode, 0)
            self.assertIn("UNMARKED_FOREIGN_BUDGET", res_del_fail.stderr)
            res_del_ok = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "add-foreign-lang")
            self.assertEqual(res_del_ok.returncode, 0, res_del_ok.stderr)


if __name__ == "__main__":
    unittest.main()
