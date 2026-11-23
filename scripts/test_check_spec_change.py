#!/usr/bin/env python3
"""Unit and git-integration tests for spec-lock rules, `.foreign-budget.json` ratchet, and Lean import policy in check_spec_change.py."""

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


REPO_ROOT = Path(__file__).resolve().parent.parent


class ImportHygieneUnitTests(unittest.TestCase):
    """Unit tests for `check_import_hygiene` against the Lean import policy."""

    def test_umbrella_mathlib_rejected(self) -> None:
        cases = [
            "import Mathlib",
            "import Mathlib\n",
            "public import Mathlib\n",
            "meta import Mathlib\n",
            "private import Mathlib\n",
            "public meta import Mathlib\n",
            "import «Mathlib»\n",
            "import Mathlib -- trailing comment\n",
            "import Mathlib--no-space comment\n",
            "import Mathlib /- trailing block -/\n",
            "import /- inline -/ Mathlib\n",
            "import\n  Mathlib\n",
            "import Mathlib import LeanSwe.Json.Types\n",
            "import Aeneas import Mathlib\n",
            "import Mathlib .Data.Nat.Basic\n",
            "import Mathlib. Data.Nat.Basic\n",
            "import Mathlib\n.Data.Nat.Basic\n",
            "import Mathlib/- c -/.Data.Nat.Basic\n",
            "\ufeffimport Mathlib\r\n",
        ]
        for src in cases:
            with self.subTest(src=src):
                errs = check_spec_change.check_import_hygiene(src, "Demo.lean")
                self.assertTrue(errs, f"expected violation for {src!r}")
                self.assertIn("umbrella import 'Mathlib'", errs[0])

    def test_external_import_all_rejected(self) -> None:
        cases = [
            ("import all Mathlib.Data.Nat.Basic\n", "Mathlib.Data.Nat.Basic"),
            ("public import all Batteries.Foo\n", "Batteries.Foo"),
            ("meta import all Std.Data.HashMap\n", "Std.Data.HashMap"),
            ("private import all Init.Core\n", "Init.Core"),
            ("public meta import all Lean.Meta\n", "Lean.Meta"),
            ("import all Aeneas\n", "Aeneas"),
            ("import all Aesop\n", "Aesop"),
            ("import all «Mathlib».Data.Nat.Basic\n", "Mathlib.Data.Nat.Basic"),
            ("import all LeanSweExtra.Foo\n", "LeanSweExtra.Foo"),
            ("import all CoreExtra\n", "CoreExtra"),
            ("import all FuzzExtra.Suite\n", "FuzzExtra.Suite"),
            ("import all TestsExtra.Main\n", "TestsExtra.Main"),
            ("import all «LeanSwe.Foo»\n", "LeanSwe.Foo"),
            ("import /- c -/ all\n  -- comment\n  Batteries.Data.List\n", "Batteries.Data.List"),
        ]
        for src, mod in cases:
            with self.subTest(src=src):
                errs = check_spec_change.check_import_hygiene(src, "Demo.lean")
                self.assertEqual(len(errs), 1, f"unexpected errors for {src!r}: {errs}")
                self.assertIn(f"disallowed external 'import all {mod}'", errs[0])

    def test_import_all_mathlib_reports_both_and_dangling_import_all(self) -> None:
        both = check_spec_change.check_import_hygiene("module\nimport all Mathlib\n", "Demo.lean")
        self.assertEqual(len(both), 2)
        self.assertIn("Demo.lean:2:", both[0])
        self.assertIn("import all Mathlib", both[0])
        self.assertIn("umbrella import 'Mathlib'", both[1])

        dangling = check_spec_change.check_import_hygiene(
            "public import all\npublic import Mathlib\n", "Demo.lean"
        )
        self.assertEqual(len(dangling), 2)
        self.assertIn("Demo.lean:1: disallowed dangling 'import all'", dangling[0])
        self.assertIn("Demo.lean:2: disallowed umbrella import 'Mathlib'", dangling[1])
        self.assertEqual(len(check_spec_change.check_import_hygiene("import all\n", "Demo.lean")), 1)
        self.assertEqual(len(check_spec_change.check_import_hygiene("import all\n.Foo\n", "Demo.lean")), 1)

    def test_allowed_submodules_intra_repo_import_all_and_prefix_collisions(self) -> None:
        allowed_src = "\n".join([
            "module",
            "import Mathlib.Data.Nat.Basic",
            "public import Mathlib.Tactic.Ring",
            "meta import Mathlib.Logic.Basic",
            "import «Mathlib».Data.Nat.Basic",
            "import Mathlib.«Data».Nat.Basic",
            "import Mathlib.all",
            "import MathlibExtra",
            "import Mathlib_Extra",
            "import Mathlib'",
            "import Mathlib1",
            "import Mathlib₁",
            "import My.Mathlib",
            "import LeanSwe.Mathlib",
            "import Aeneas",
            "import Lean",
            "import Lake",
            "import all.Foo",
            "import all.Mathlib",
            "import «all»",
            "import all LeanSwe.Foo.Impl",
            "public import all LeanSwe.Foo.Impl",
            "meta import all LeanSwe.Foo.Impl",
            "private import all LeanSwe.Foo.Impl",
            "import all «LeanSwe».Foo.Impl",
            "import all\n  -- multiline intra-repo import all\n  LeanSwe.Bar.Impl",
            "import all Core.NondetTest",
            "import all Fuzz.Common.Rng",
            "import all Tests.Main",
            "import all LeanSwe",
            "import all Core",
        ])
        self.assertEqual(check_spec_change.check_import_hygiene(allowed_src, "Ok.lean"), [])

    def test_comments_docstrings_strings_and_non_command_tokens_ignored(self) -> None:
        safe_src = '\n'.join([
            "-- never write `import Mathlib` or `import all Mathlib.Foo`",
            "/- block comment: import Mathlib; public import all Batteries.Foo -/",
            "/- outer /- nested comment -/ import Mathlib\n   import all Aeneas -/",
            "/-- Doc comment: never use `import Mathlib` or `import all Std.Time`. -/",
            "/-! Module doc: avoid `import Mathlib` and `meta import all Lean.Meta`. -/",
            "import LeanSwe.PostFork.Types -- don't write import Mathlib",
            'def s1 : String := "import Mathlib\\nimport all Batteries.Foo"',
            'def s2 : String := "\nimport Mathlib\nimport all Mathlib.Foo\n"',
            'def s3 : String := "escaped \\" import Mathlib"',
            'def s4 (x : String) : String := s!"{x} import Mathlib import all Aeneas"',
            'def s5 : String := r#"import Mathlib\nimport all Mathlib.Foo"#',
            'def s6 : String := r##" "import Mathlib" "##',
            "def c1 : Char := '\"'",
            'def s7 : String := "import Mathlib"',
            "def f (x : Nat) := obj.import Mathlib",
            "def n := `import",
            "def q := ``import",
            "def «import» := Mathlib",
            "def quoted := (import Mathlib)",
        ])
        self.assertEqual(check_spec_change.check_import_hygiene(safe_src, "Safe.lean"), [])

        after_esc = '\n'.join([
            "-- comment with unclosed /-",
            'def s := "a\\\\"',
            'def r := r#"import Mathlib"#',
            "import Mathlib",
            "import all Batteries.Foo",
        ])
        errs = check_spec_change.check_import_hygiene(after_esc, "After.lean")
        self.assertEqual(len(errs), 2)
        self.assertIn("After.lean:4:", errs[0])
        self.assertIn("After.lean:5:", errs[1])

    def test_real_repo_imports_clean(self) -> None:
        checked, violations = check_spec_change.check_repo_imports(REPO_ROOT)
        self.assertGreaterEqual(checked, 400)
        self.assertEqual(violations, [])


class ImportHygieneCliTests(unittest.TestCase):
    """Git-integration CLI tests ensuring import lint runs unconditionally and via `--check-imports`."""

    def _run_cli(self, repo: Path, *args: str) -> subprocess.CompletedProcess[str]:
        script = Path(__file__).resolve().parent / "check_spec_change.py"
        env = {k: v for k, v in os.environ.items() if k != "GITHUB_EVENT_PATH"}
        return subprocess.run(
            [sys.executable, "-B", str(script), *args],
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
        (repo / "LeanSwe" / "Demo" / "Impl.lean").write_text("import Core.Types\ndef x := 1\n", encoding="utf-8")
        (repo / "LeanSwe" / "Demo" / "Types.lean").write_text("def t := 1\n", encoding="utf-8")
        _git(repo, "add", ".")
        _git(repo, "commit", "-m", "base")
        return repo

    def test_pr_mode_rejects_disallowed_imports_even_with_all_labels_and_new_package(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_repo(tmp)
            (repo / "LeanSwe" / "Demo" / "Impl.lean").write_text("import Mathlib\ndef x := 1\n", encoding="utf-8")
            (repo / "LeanSwe" / "Fresh").mkdir(parents=True)
            (repo / "LeanSwe" / "Fresh" / "Types.lean").write_text(
                "public import all Batteries.Foo\ndef f := 1\n", encoding="utf-8"
            )
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "bad imports")

            res = self._run_cli(
                repo, "--base", "HEAD~1", "--head", "HEAD", "--label", "spec-add,spec-change,add-foreign-lang"
            )
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("IMPORT_POLICY_VIOLATION: LeanSwe/Demo/Impl.lean:1:", res.stderr)
            self.assertIn("IMPORT_POLICY_VIOLATION: LeanSwe/Fresh/Types.lean:1:", res.stderr)

            res_all = self._run_cli(repo, "--check-imports")
            self.assertNotEqual(res_all.returncode, 0)
            self.assertIn("LeanSwe/Demo/Impl.lean:1:", res_all.stderr)
            self.assertIn("LeanSwe/Fresh/Types.lean:1:", res_all.stderr)

    def test_pr_mode_allows_intra_repo_import_all_submodules_deletes_and_symlinks(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_repo(tmp)
            (repo / "LeanSwe" / "Demo" / "Proofs.lean").write_text(
                "module\nimport Mathlib.Data.Nat.Basic\nimport all LeanSwe.Demo.Impl\n", encoding="utf-8"
            )
            os.symlink("Types.lean", repo / "LeanSwe" / "Demo" / "Link.lean")
            _git(repo, "rm", "LeanSwe/Demo/Impl.lean")
            _git(repo, "add", "LeanSwe/Demo/Proofs.lean", "LeanSwe/Demo/Link.lean")
            _git(repo, "commit", "-m", "valid imports, delete, and symlink")

            res = self._run_cli(repo, "--base", "HEAD~1", "--head", "HEAD")
            self.assertEqual(res.returncode, 0, res.stderr)
            self.assertIn("IMPORT_POLICY_CHECK: ok (checked=1 errors=0)", res.stdout)

            res_all = self._run_cli(repo, "--check-imports")
            self.assertEqual(res_all.returncode, 0, res_all.stderr)
            self.assertIn("IMPORT_POLICY_CHECK: ok (checked=2 errors=0)", res_all.stdout)

    def test_rename_non_checked_out_head_and_missing_base(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_repo(tmp)
            (repo / "note.txt").write_text("import Mathlib\n", encoding="utf-8")
            _git(repo, "add", "note.txt")
            _git(repo, "commit", "-m", "add txt")
            base_sha = _git(repo, "rev-parse", "HEAD")

            _git(repo, "checkout", "-q", "-b", "rename-bad")
            _git(repo, "mv", "note.txt", "Bad.lean")
            _git(repo, "commit", "-m", "rename txt to lean")
            bad_sha = _git(repo, "rev-parse", "HEAD")
            _git(repo, "checkout", "-q", base_sha)

            res_diff = self._run_cli(repo, "--base", base_sha, "--head", bad_sha)
            self.assertNotEqual(res_diff.returncode, 0)
            self.assertIn("IMPORT_POLICY_VIOLATION: Bad.lean:1:", res_diff.stderr)

            res_both = self._run_cli(repo, "--base", base_sha, "--head", bad_sha, "--check-imports")
            self.assertNotEqual(res_both.returncode, 0)
            self.assertIn("IMPORT_POLICY_VIOLATION: Bad.lean:1:", res_both.stderr)

            res_no_base = self._run_cli(repo)
            self.assertEqual(res_no_base.returncode, 2)

    def test_real_repo_cli_check_imports(self) -> None:
        res = self._run_cli(REPO_ROOT, "--check-imports")
        self.assertEqual(res.returncode, 0, res.stderr)
        self.assertIn("IMPORT_POLICY_CHECK: ok", res.stdout)


class SpecSubdirLockTests(unittest.TestCase):
    """Unit and git-integration tests verifying locked spec subdirectory coverage."""

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
        for rel, body in (
            ("LeanSwe/Tar/SpecTests/Helpers.lean", "namespace LeanSwe.Tar\ndef h : Nat := 1\nend LeanSwe.Tar\n"),
            ("LeanSwe/Toml/SpecTests/Cases.lean", "namespace LeanSwe.Toml\ndef c : Nat := 1\nend LeanSwe.Toml\n"),
            ("LeanSwe/LinuxSyscall/Net/Model/Step.lean", "def stepNet : Nat := 1\n"),
            ("LeanSwe/Tar/Impl.lean", "def tarImpl : Nat := 1\n"),
        ):
            p = repo / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(body, encoding="utf-8")
        _git(repo, "add", ".")
        _git(repo, "commit", "-m", "base")
        return repo

    def test_is_spec_file_covers_basenames_and_subdirs(self) -> None:
        locked = [
            "Core/NondetTest.lean",
            "Core/Sub/Helper.lean",
            "LeanSwe/Tar/Types.lean",
            "LeanSwe/Tar/Model.lean",
            "LeanSwe/Tar/SpecTests.lean",
            "LeanSwe/Tar/Interface.lean",
            "LeanSwe/Tar/SpecTests/Helpers.lean",
            "LeanSwe/Toml/SpecTests/Cases.lean",
            "LeanSwe/Toml/SpecTests/Sub/Extra.lean",
            "LeanSwe/LinuxSyscall/Net/Model/Step.lean",
            "LeanSwe/Demo/Types/Sub.lean",
            "LeanSwe/Demo/Interface/Sub.lean",
            "LeanSwe/SpecTests/Helpers.lean",
        ]
        for rel in locked:
            with self.subTest(locked=rel):
                self.assertTrue(check_spec_change.is_spec_file(rel))

        unlocked = [
            "Core/README.md",
            "LeanSwe/Tar/Impl.lean",
            "LeanSwe/Tar/Impl/Helper.lean",
            "LeanSwe/Tar/Proofs/ByteModel.lean",
            "LeanSwe/Toml/Proofs/ModelCheck.lean",
            "LeanSwe/Tar/SpecMutants.lean",
            "LeanSwe/Tar/RuntimeTests.lean",
            "LeanSwe/LinuxSyscall/Files/Seed.lean",
            "LeanSwe/Demo/SpecTestsHelper/Foo.lean",
            "LeanSwe/Demo/ModelExtra/Bar.lean",
            "LeanSwe/Tar/SpecTests/README.md",
            "harness/Fuzz/SpecTests/Foo.lean",
            "scripts/SpecTests/Foo.lean",
            "LeanSwe.lean",
        ]
        for rel in unlocked:
            with self.subTest(unlocked=rel):
                self.assertFalse(check_spec_change.is_spec_file(rel))

    def test_tar_and_toml_spec_subdir_add_and_modify_labels(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_repo(tmp)
            tar_helpers = repo / "LeanSwe/Tar/SpecTests/Helpers.lean"
            toml_cases = repo / "LeanSwe/Toml/SpecTests/Cases.lean"

            tar_helpers.write_text(
                "namespace LeanSwe.Tar\ndef h : Nat := 1\ndef h2 : Nat := 2\nend LeanSwe.Tar\n",
                encoding="utf-8",
            )
            toml_cases.write_text(
                "namespace LeanSwe.Toml\ndef c : Nat := 1\ndef c2 : Nat := 2\nend LeanSwe.Toml\n",
                encoding="utf-8",
            )
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "append pure spec helpers")

            res_none = self._run_cli(repo, "HEAD~1", "HEAD")
            self.assertNotEqual(res_none.returncode, 0)
            self.assertIn("UNMARKED_SPEC_ADD", res_none.stderr)
            self.assertIn("LeanSwe/Tar/SpecTests/Helpers.lean", res_none.stderr)
            self.assertIn("LeanSwe/Toml/SpecTests/Cases.lean", res_none.stderr)

            res_add = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add")
            self.assertEqual(res_add.returncode, 0, res_add.stderr)

            tar_helpers.write_text(
                "namespace LeanSwe.Tar\ndef h : Nat := 99\ndef h2 : Nat := 2\nend LeanSwe.Tar\n",
                encoding="utf-8",
            )
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "edit existing helper")

            res_mod_none = self._run_cli(repo, "HEAD~1", "HEAD")
            self.assertNotEqual(res_mod_none.returncode, 0)
            self.assertIn("UNMARKED_SPEC_CHANGE", res_mod_none.stderr)

            res_mod_add = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add")
            self.assertNotEqual(res_mod_add.returncode, 0)
            self.assertIn("SPEC_CHANGE_REQUIRED", res_mod_add.stderr)

            res_mod_change = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change")
            self.assertEqual(res_mod_change.returncode, 0, res_mod_change.stderr)

            toml_cases.write_text(
                "namespace LeanSwe.Toml\ndef c : Nat := 42\ndef c2 : Nat := 2\nend LeanSwe.Toml\n",
                encoding="utf-8",
            )
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "edit existing toml case")

            res_toml_add = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add")
            self.assertNotEqual(res_toml_add.returncode, 0)
            self.assertIn("LeanSwe/Toml/SpecTests/Cases.lean", res_toml_add.stderr)

            res_toml_change = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change")
            self.assertEqual(res_toml_change.returncode, 0, res_toml_change.stderr)

    def test_new_and_moved_spec_subdir_files_and_interface_subdir(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_repo(tmp)

            extra = repo / "LeanSwe/Tar/SpecTests/Extra.lean"
            extra.write_text("namespace LeanSwe.Tar\ndef e : Nat := 1\nend LeanSwe.Tar\n", encoding="utf-8")
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "add pure spec submodule")
            self.assertNotEqual(self._run_cli(repo, "HEAD~1", "HEAD").returncode, 0)
            res_extra_add = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add")
            self.assertEqual(res_extra_add.returncode, 0, res_extra_add.stderr)

            iface_sub = repo / "LeanSwe/Tar/Interface/Extra.lean"
            iface_sub.parent.mkdir(parents=True, exist_ok=True)
            iface_sub.write_text("namespace LeanSwe.Tar\ndef i : Nat := 1\nend LeanSwe.Tar\n", encoding="utf-8")
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "add interface submodule")
            res_iface_add = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add")
            self.assertNotEqual(res_iface_add.returncode, 0)
            self.assertIn("expands Core or Interface boundary", res_iface_add.stderr)
            res_iface_chg = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change")
            self.assertEqual(res_iface_chg.returncode, 0, res_iface_chg.stderr)

            net_step = repo / "LeanSwe/LinuxSyscall/Net/Model/Step.lean"
            net_step.write_text("def stepNet : Nat := 2\n", encoding="utf-8")
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "edit model submodule")
            self.assertNotEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add").returncode, 0)
            self.assertEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change").returncode, 0)

            _git(repo, "mv", "LeanSwe/Tar/Impl.lean", "LeanSwe/Tar/SpecTests/Sneaky.lean")
            _git(repo, "commit", "-m", "rename impl into spectests")
            self.assertNotEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add").returncode, 0)
            self.assertEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change").returncode, 0)

            _git(repo, "mv", "LeanSwe/Tar/SpecTests/Sneaky.lean", "LeanSwe/Tar/MovedOut.lean")
            _git(repo, "commit", "-m", "rename out of spectests")
            self.assertNotEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add").returncode, 0)
            self.assertEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change").returncode, 0)

            _git(repo, "rm", "LeanSwe/Tar/SpecTests/Extra.lean")
            _git(repo, "commit", "-m", "delete spectests submodule")
            self.assertNotEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add").returncode, 0)
            self.assertEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change").returncode, 0)

            fresh = repo / "LeanSwe/FreshPkg/SpecTests/Helpers.lean"
            fresh.parent.mkdir(parents=True, exist_ok=True)
            fresh.write_text("def fresh : Nat := 1\n", encoding="utf-8")
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "brand new package spectests submodule")
            res_fresh = self._run_cli(repo, "HEAD~1", "HEAD")
            self.assertEqual(res_fresh.returncode, 0, res_fresh.stderr)


if __name__ == "__main__":
    unittest.main()
