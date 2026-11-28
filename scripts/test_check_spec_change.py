#!/usr/bin/env python3
"""Unit and git-integration tests for spec-lock rules and package manifest checks in check_spec_change.py."""

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


def _dump(obj: dict) -> str:
    return json.dumps(obj, indent=2) + "\n"


def _git(cwd: Path, *args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=cwd, text=True).strip()


class SpecSubdirLockTests(unittest.TestCase):
    """Unit and git-integration tests verifying locked spec subdirectory coverage and CLI flags."""

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
            ("LeanSwe/Tar/Properties/Helpers.lean", "namespace LeanSwe.Tar\ndef h : Nat := 1\nend LeanSwe.Tar\n"),
            ("LeanSwe/Toml/ModelChecks/Cases.lean", "namespace LeanSwe.Toml\ndef c : Nat := 1\nend LeanSwe.Toml\n"),
            ("LeanSwe/Tar/SpecTests.lean", "namespace LeanSwe.Tar\ndef st : Nat := 1\nend LeanSwe.Tar\n"),
            ("LeanSwe/Tar/SpecTests/Helpers.lean", "namespace LeanSwe.Tar\ndef sth : Nat := 1\nend LeanSwe.Tar\n"),
            ("LeanSwe/LinuxSyscall/Net/Model/Step.lean", "def stepNet : Nat := 1\n"),
            ("LeanSwe/Tar/Impl.lean", "def tarImpl : Nat := 1\n"),
        ):
            p = repo / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(body, encoding="utf-8")
        _git(repo, "add", ".")
        _git(repo, "commit", "-m", "base")
        return repo

    def test_cli_requires_base_rejects_unknown_flags_and_reads_event_path(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_repo(tmp)
            script = Path(__file__).resolve().parent / "check_spec_change.py"
            env = {k: v for k, v in os.environ.items() if k != "GITHUB_EVENT_PATH"}
            for args in ([], ["--check-imports"], ["--base", "HEAD", "--label", "unknown-label"]):
                res = subprocess.run(
                    [sys.executable, "-B", str(script), *args],
                    cwd=repo,
                    env=env,
                    capture_output=True,
                    text=True,
                )
                self.assertEqual(res.returncode, 2)

            (repo / "LeanSwe/Tar/Properties/Helpers.lean").write_text(
                "namespace LeanSwe.Tar\ndef h : Nat := 99\nend LeanSwe.Tar\n",
                encoding="utf-8",
            )
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "modify locked spec")

            event_path = repo / "event.json"
            event_path.write_text(
                json.dumps({"pull_request": {"labels": [{"name": "bug"}]}}),
                encoding="utf-8",
            )
            res_unrelated = self._run_cli(repo, "HEAD~1", "HEAD", "--event-path", str(event_path))
            self.assertNotEqual(res_unrelated.returncode, 0)
            self.assertIn("UNMARKED_SPEC_CHANGE", res_unrelated.stderr)

            event_path.write_text(
                json.dumps({"pull_request": {"labels": [{"name": "bug"}, {"name": "spec-change"}]}}),
                encoding="utf-8",
            )
            res_event = self._run_cli(repo, "HEAD~1", "HEAD", "--event-path", str(event_path))
            self.assertEqual(res_event.returncode, 0, res_event.stderr)

    def test_is_spec_file_covers_basenames_subdirs_and_metadata_json(self) -> None:
        locked = [
            "Core/NondetTest.lean",
            "Core/Sub/Helper.lean",
            "LeanSwe/Tar/Types.lean",
            "LeanSwe/Tar/Model.lean",
            "LeanSwe/Tar/Interface.lean",
            "LeanSwe/Tar/Properties.lean",
            "LeanSwe/Tar/ModelChecks.lean",
            "LeanSwe/Tar/Properties/Helpers.lean",
            "LeanSwe/Toml/ModelChecks/Cases.lean",
            "LeanSwe/Toml/ModelChecks/Sub/Extra.lean",
            "LeanSwe/LinuxSyscall/Net/Model/Step.lean",
            "LeanSwe/LinuxSyscall/Files/Model/Seed.lean",
            "LeanSwe/Demo/Types/Sub.lean",
            "LeanSwe/Demo/Interface/Sub.lean",
            "proofs/LeanSweProofs/Tar/Model.lean",
            "proofs/LeanSweProofs/Tar/Properties.lean",
            "proofs/LeanSweProofs/Tar/Properties/Helpers.lean",
            "proofs/LeanSweProofs/LinuxSyscall/Net/Model/Step.lean",
            "proofs/LeanSweProofs/PostFork/Aeneas/Types.lean",
            "proofs/LeanSweProofs/PostFork/Aeneas/Funs.lean",
            "proofs/LeanSweProofs/PostFork/Aeneas/Api.lean",
            "scripts/package_manifest.json",
            "scripts/external_assumptions.json",
        ]
        for rel in locked:
            with self.subTest(locked=rel):
                self.assertTrue(check_spec_change.is_spec_file(rel))

        unlocked = [
            "Core/README.md",
            "LeanSwe/Tar/SpecTests.lean",
            "LeanSwe/Tar/SpecTests/Helpers.lean",
            "LeanSwe/Toml/SpecTests/Cases.lean",
            "LeanSwe/Toml/SpecTests/Sub/Extra.lean",
            "LeanSwe/SpecTests/Helpers.lean",
            "LeanSwe/Tar/Impl.lean",
            "LeanSwe/Tar/Impl/Helper.lean",
            "LeanSwe/Tar/Proofs/ByteModel.lean",
            "LeanSwe/Toml/Proofs/ModelCheck.lean",
            "LeanSwe/Tar/SpecMutants.lean",
            "LeanSwe/Tar/RuntimeTests.lean",
            "LeanSwe/LinuxSyscall/Files/Seed.lean",
            "LeanSwe/Demo/PropertiesHelper/Foo.lean",
            "LeanSwe/Demo/ModelChecksExtra/Bar.lean",
            "LeanSwe/Demo/ModelExtra/Bar.lean",
            "LeanSwe/Tar/Properties/README.md",
            "harness/Fuzz/Properties/Foo.lean",
            "scripts/Properties/Foo.lean",
            "proofs/LeanSweProofs/Tar/SpecTests.lean",
            "proofs/LeanSweProofs/Tar/SpecTests/Helpers.lean",
            "proofs/LeanSweProofs/Tar/SpecMutants.lean",
            "proofs/LeanSweProofs/Tar/Proofs/ByteModel.lean",
            "proofs/LeanSweProofs.lean",
            "scripts/other.json",
            "LeanSwe.lean",
        ]
        for rel in unlocked:
            with self.subTest(unlocked=rel):
                self.assertFalse(check_spec_change.is_spec_file(rel))

    def test_spectests_edits_are_unlocked_without_labels(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_repo(tmp)
            (repo / "LeanSwe/Tar/SpecTests.lean").write_text(
                "namespace LeanSwe.Tar\ndef st : Nat := 999\nend LeanSwe.Tar\n",
                encoding="utf-8",
            )
            (repo / "LeanSwe/Tar/SpecTests/Helpers.lean").write_text(
                "namespace LeanSwe.Tar\ndef sth : Nat := 999\nend LeanSwe.Tar\n",
                encoding="utf-8",
            )
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "edit spectests")

            res = self._run_cli(repo, "HEAD~1", "HEAD")
            self.assertEqual(res.returncode, 0, res.stderr)
            self.assertIn("spec files touched=0", res.stdout)

    def test_properties_and_modelchecks_subdir_add_and_modify_labels(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_repo(tmp)
            tar_helpers = repo / "LeanSwe/Tar/Properties/Helpers.lean"
            toml_cases = repo / "LeanSwe/Toml/ModelChecks/Cases.lean"

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
            self.assertIn("LeanSwe/Tar/Properties/Helpers.lean", res_none.stderr)
            self.assertIn("LeanSwe/Toml/ModelChecks/Cases.lean", res_none.stderr)

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
            _git(repo, "commit", "-m", "edit existing toml model check")

            res_toml_add = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add")
            self.assertNotEqual(res_toml_add.returncode, 0)
            self.assertIn("LeanSwe/Toml/ModelChecks/Cases.lean", res_toml_add.stderr)

            res_toml_change = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change")
            self.assertEqual(res_toml_change.returncode, 0, res_toml_change.stderr)

    def test_new_and_moved_spec_subdir_files_and_interface_subdir(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_repo(tmp)

            extra = repo / "LeanSwe/Tar/Properties/Extra.lean"
            extra.write_text("namespace LeanSwe.Tar\ndef e : Nat := 1\nend LeanSwe.Tar\n", encoding="utf-8")
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "add pure properties submodule")
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

            _git(repo, "mv", "LeanSwe/Tar/Impl.lean", "LeanSwe/Tar/Properties/Sneaky.lean")
            _git(repo, "commit", "-m", "rename impl into properties")
            self.assertNotEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add").returncode, 0)
            self.assertEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change").returncode, 0)

            _git(repo, "mv", "LeanSwe/Tar/Properties/Sneaky.lean", "LeanSwe/Tar/MovedOut.lean")
            _git(repo, "commit", "-m", "rename out of properties")
            self.assertNotEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add").returncode, 0)
            self.assertEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change").returncode, 0)

            _git(repo, "rm", "LeanSwe/Tar/Properties/Extra.lean")
            _git(repo, "commit", "-m", "delete properties submodule")
            self.assertNotEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add").returncode, 0)
            self.assertEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change").returncode, 0)

            fresh = repo / "LeanSwe/FreshPkg/Properties/Helpers.lean"
            fresh.parent.mkdir(parents=True, exist_ok=True)
            fresh.write_text("def fresh : Nat := 1\n", encoding="utf-8")
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "brand new package properties submodule")
            res_fresh = self._run_cli(repo, "HEAD~1", "HEAD")
            self.assertEqual(res_fresh.returncode, 0, res_fresh.stderr)

            proof_model = repo / "proofs/LeanSweProofs/Tar/Model.lean"
            proof_model.parent.mkdir(parents=True, exist_ok=True)
            proof_model.write_text("namespace LeanSwe.Tar.Model\ndef m : Nat := 1\nend LeanSwe.Tar.Model\n", encoding="utf-8")
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "add proofs model for existing package")
            self.assertNotEqual(self._run_cli(repo, "HEAD~1", "HEAD").returncode, 0)
            self.assertEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add").returncode, 0)

            proof_model.write_text("namespace LeanSwe.Tar.Model\ndef m : Nat := 2\nend LeanSwe.Tar.Model\n", encoding="utf-8")
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "modify proofs model")
            self.assertNotEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add").returncode, 0)
            self.assertEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change").returncode, 0)

            proof_aeneas = repo / "proofs/LeanSweProofs/Tar/Aeneas/Funs.lean"
            proof_aeneas.parent.mkdir(parents=True, exist_ok=True)
            proof_aeneas.write_text("namespace LeanSwe.Tar.Aeneas\ndef f : Nat := 1\nend LeanSwe.Tar.Aeneas\n", encoding="utf-8")
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "add proofs aeneas file")
            self.assertNotEqual(self._run_cli(repo, "HEAD~1", "HEAD").returncode, 0)
            self.assertEqual(self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add").returncode, 0)


class PackageManifestTests(unittest.TestCase):
    """Unit and git-integration tests for `scripts/package_manifest.json` integrity and non-downgrade ratchet."""

    BASE_SUITES = {
        "version": 1,
        "common_paths": [],
        "suites": {
            "demo_raw": {"paths": ["LeanSwe/Demo/Raw/"]},
            "float": {"paths": ["LeanSwe/PurePkg/"]},
        },
    }

    BASE_MANIFEST = {
        "version": 1,
        "packages": {
            "LeanSwe.Demo": {
                "kind": "model",
                "purity": "mixed",
                "deps": ["LeanSwe.Demo.Raw"],
                "external_boundary": False,
                "spec_style": "state_step",
            },
            "LeanSwe.Demo.Raw": {
                "kind": "model",
                "purity": "nondet_io",
                "deps": [],
                "fuzz_suite": "demo_raw",
                "external_boundary": True,
                "spec_style": "state_step",
            },
            "LeanSwe.PurePkg": {
                "kind": "model",
                "purity": "pure",
                "deps": [],
                "fuzz_suite": "float",
                "external_boundary": False,
                "spec_style": "inverse_render",
            },
            "LeanSwe.SupportDir": {
                "kind": "support",
                "purity": "types_only",
                "deps": [],
                "external_boundary": False,
            },
        },
    }

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

    def _init_manifest_repo(self, tmp: str) -> Path:
        repo = Path(tmp)
        _git(repo, "init")
        _git(repo, "config", "user.name", "Test")
        _git(repo, "config", "user.email", "test@example.com")
        files = {
            "LeanSwe/Demo/Types.lean": "def demoType : Nat := 1\n",
            "LeanSwe/Demo/Interface.lean": "def demoFn : Nat := 1\n",
            "LeanSwe/Demo/Impl.lean": "/-- Doc comment mentioning @[extern] is not an attribute. -/\ndef demoImpl : Nat := 1\n",
            "LeanSwe/Demo/Raw/Types.lean": "def rawType : Nat := 1\n",
            "LeanSwe/Demo/Raw/Interface.lean": '@[extern "demo_raw_call"] opaque rawCall : IO Unit\n',
            "LeanSwe/PurePkg/Types.lean": "def pureType : Nat := 1\n",
            "LeanSwe/PurePkg/Interface.lean": "def pureFn : Nat := 1\n",
            "LeanSwe/SupportDir/Types.lean": "def supportType : Nat := 1\n",
            "harness/Fuzz/suites.json": _dump(self.BASE_SUITES),
            "scripts/package_manifest.json": _dump(self.BASE_MANIFEST),
        }
        for rel, body in files.items():
            p = repo / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(body, encoding="utf-8")
        _git(repo, "add", ".")
        _git(repo, "commit", "-m", "base with manifest")
        return repo

    def test_real_repo_manifest_is_valid(self) -> None:
        repo_root = Path(__file__).resolve().parent.parent
        errs = check_spec_change.validate_package_manifest(repo_root)
        self.assertEqual(errs, [], f"unexpected manifest errors: {errs}")

    def test_standalone_valid_manifest_passes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_manifest_repo(tmp)
            self.assertEqual(check_spec_change.validate_package_manifest(repo), [])

    def test_missing_package_and_orphan_entry_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_manifest_repo(tmp)
            (repo / "LeanSwe/ExtraPkg").mkdir(parents=True)
            (repo / "LeanSwe/ExtraPkg/Types.lean").write_text("def e : Nat := 1\n", encoding="utf-8")
            errs_missing = check_spec_change.validate_package_manifest(repo)
            self.assertTrue(any("missing package 'LeanSwe.ExtraPkg'" in e for e in errs_missing), errs_missing)

            manifest = copy.deepcopy(self.BASE_MANIFEST)
            manifest["packages"]["LeanSwe.ExtraPkg"] = {
                "kind": "model",
                "purity": "pure",
                "deps": [],
                "external_boundary": False,
            }
            manifest["packages"]["LeanSwe.GhostPkg"] = {
                "kind": "model",
                "purity": "pure",
                "deps": [],
                "external_boundary": False,
            }
            (repo / "scripts/package_manifest.json").write_text(_dump(manifest), encoding="utf-8")
            errs_orphan = check_spec_change.validate_package_manifest(repo)
            self.assertTrue(any("orphan manifest entry 'LeanSwe.GhostPkg'" in e for e in errs_orphan), errs_orphan)

    def test_property_rejected_for_external_boundary_and_extern_attr(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_manifest_repo(tmp)
            manifest = copy.deepcopy(self.BASE_MANIFEST)
            manifest["packages"]["LeanSwe.Demo.Raw"]["kind"] = "property"
            (repo / "scripts/package_manifest.json").write_text(_dump(manifest), encoding="utf-8")
            errs_ext_flag = check_spec_change.validate_package_manifest(repo)
            self.assertTrue(
                any("external_boundary=true and cannot use kind='property'" in e for e in errs_ext_flag),
                errs_ext_flag,
            )
            self.assertTrue(
                any("contains @[extern] declarations and cannot use kind='property'" in e for e in errs_ext_flag),
                errs_ext_flag,
            )

            # Even if external_boundary is falsely set to false, @[extern] on disk is still caught.
            manifest["packages"]["LeanSwe.Demo.Raw"]["external_boundary"] = False
            (repo / "scripts/package_manifest.json").write_text(_dump(manifest), encoding="utf-8")
            errs_extern_only = check_spec_change.validate_package_manifest(repo)
            self.assertTrue(
                any("contains @[extern] declarations and cannot use kind='property'" in e for e in errs_extern_only),
                errs_extern_only,
            )
            self.assertTrue(
                any("declares external_boundary=false" in e for e in errs_extern_only),
                errs_extern_only,
            )

    def test_unknown_fuzz_suite_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_manifest_repo(tmp)
            manifest = copy.deepcopy(self.BASE_MANIFEST)
            manifest["packages"]["LeanSwe.PurePkg"]["fuzz_suite"] = "nonexistent_suite"
            (repo / "scripts/package_manifest.json").write_text(_dump(manifest), encoding="utf-8")
            errs = check_spec_change.validate_package_manifest(repo)
            self.assertTrue(any("unknown fuzz_suite 'nonexistent_suite'" in e for e in errs), errs)

    def test_model_to_property_downgrade_requires_spec_change_label(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_manifest_repo(tmp)
            downgraded = copy.deepcopy(self.BASE_MANIFEST)
            downgraded["packages"]["LeanSwe.PurePkg"]["kind"] = "property"
            (repo / "scripts/package_manifest.json").write_text(_dump(downgraded), encoding="utf-8")
            _git(repo, "add", "scripts/package_manifest.json")
            _git(repo, "commit", "-m", "downgrade PurePkg to property")

            res_none = self._run_cli(repo, "HEAD~1", "HEAD")
            self.assertNotEqual(res_none.returncode, 0)
            self.assertIn("UNMARKED_SPEC_CHANGE", res_none.stderr)
            self.assertIn("LeanSwe.PurePkg", res_none.stderr)
            self.assertIn("'model' -> 'property'", res_none.stderr)

            res_add = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add")
            self.assertNotEqual(res_add.returncode, 0)
            self.assertIn("SPEC_CHANGE_REQUIRED", res_add.stderr)
            self.assertIn("LeanSwe.PurePkg", res_add.stderr)

            res_change = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change")
            self.assertEqual(res_change.returncode, 0, res_change.stderr)
            self.assertIn("MANIFEST_CHECK: ok", res_change.stdout)
            self.assertIn("LeanSwe.PurePkg", res_change.stdout)

    def test_cli_blocks_manifest_integrity_failure_even_with_spec_change(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_manifest_repo(tmp)
            broken = copy.deepcopy(self.BASE_MANIFEST)
            broken["packages"]["LeanSwe.PurePkg"]["fuzz_suite"] = "bogus_suite"
            (repo / "scripts/package_manifest.json").write_text(_dump(broken), encoding="utf-8")
            _git(repo, "add", "scripts/package_manifest.json")
            _git(repo, "commit", "-m", "bogus fuzz suite")

            res = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change")
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("MANIFEST_CHECK: failed", res.stderr)
            self.assertIn("bogus_suite", res.stderr)

    def test_cli_blocks_unlisted_new_package_and_deleted_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_manifest_repo(tmp)
            (repo / "LeanSwe/UnlistedPkg").mkdir(parents=True)
            (repo / "LeanSwe/UnlistedPkg/Types.lean").write_text("def u : Nat := 1\n", encoding="utf-8")
            _git(repo, "add", "LeanSwe/UnlistedPkg/Types.lean")
            _git(repo, "commit", "-m", "add unlisted package")

            res_unlisted = self._run_cli(repo, "HEAD~1", "HEAD")
            self.assertNotEqual(res_unlisted.returncode, 0)
            self.assertIn("MANIFEST_CHECK: failed", res_unlisted.stderr)
            self.assertIn("LeanSwe.UnlistedPkg", res_unlisted.stderr)

            _git(repo, "rm", "LeanSwe/UnlistedPkg/Types.lean")
            _git(repo, "rm", "scripts/package_manifest.json")
            _git(repo, "commit", "-m", "delete manifest")
            res_del = self._run_cli(repo, "HEAD~2", "HEAD", "--label", "spec-change")
            self.assertNotEqual(res_del.returncode, 0)
            self.assertIn("MANIFEST_CHECK: failed", res_del.stderr)
            self.assertIn("missing package manifest", res_del.stderr)

    def test_has_extern_attribute_variants_and_non_false_positives(self) -> None:
        positives = [
            '@[extern "f"] opaque f : IO Unit\n',
            '@[ extern "f"] opaque f : IO Unit\n',
            '@[inline, extern "f"] opaque f : IO Unit\n',
            '@[export x, extern "y"] opaque f : IO Unit\n',
            '@[local extern "f"] opaque f : IO Unit\n',
            'attribute [extern "f"] foo\n',
            'attribute [inline, extern "f"] foo\n',
            'local attribute [extern "f"] foo\n',
            'attribute /- c -/ [ extern "f" ] foo\n',
        ]
        for src in positives:
            with self.subTest(positive=src.strip()):
                self.assertTrue(check_spec_change.has_extern_attribute(src))

        negatives = [
            '-- @[extern "f"]\ndef x : Nat := 1\n',
            '/-- Doc comment: @[extern "f"] and attribute [extern "f"] foo -/\ndef x : Nat := 1\n',
            'def s : String := "@[extern \\"f\\"] attribute [extern \\"f\\"] foo"\n',
            'def extern : Nat := 1\n',
            'def useExtern (x : Nat) : Nat := x.extern\n',
            'attribute [inline] extern\n',
        ]
        for src in negatives:
            with self.subTest(negative=src.strip()):
                self.assertFalse(check_spec_change.has_extern_attribute(src))

    def test_extern_variants_rejected_with_property_in_cli(self) -> None:
        for variant_name, lean_src in (
            ("inline_extern", '@[inline, extern "f"] opaque f : IO Unit\n'),
            ("spaced_extern", '@[ extern "f"] opaque f : IO Unit\n'),
            ("attribute_cmd", 'opaque f : IO Unit\nattribute [extern "f"] f\n'),
        ):
            with self.subTest(variant=variant_name), tempfile.TemporaryDirectory() as tmp:
                repo = self._init_manifest_repo(tmp)
                (repo / "LeanSwe/PurePkg/Impl.lean").write_text(lean_src, encoding="utf-8")
                manifest = copy.deepcopy(self.BASE_MANIFEST)
                manifest["packages"]["LeanSwe.PurePkg"]["kind"] = "property"
                (repo / "scripts/package_manifest.json").write_text(_dump(manifest), encoding="utf-8")
                _git(repo, "add", ".")
                _git(repo, "commit", "-m", f"add {variant_name} on property pkg")

                res = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change")
                self.assertNotEqual(res.returncode, 0)
                self.assertIn("MANIFEST_CHECK: failed", res.stderr)
                self.assertIn("contains @[extern] declarations and cannot use kind='property'", res.stderr)

    def test_manifest_three_tier_label_classification(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_manifest_repo(tmp)

            # Tier 1: brand-new package + its manifest entry -> exempt under ALLOW_NEW_PACKAGES (no label needed).
            (repo / "LeanSwe/FreshPkg").mkdir(parents=True)
            (repo / "LeanSwe/FreshPkg/Types.lean").write_text("def freshType : Nat := 1\n", encoding="utf-8")
            (repo / "LeanSwe/FreshPkg/Interface.lean").write_text("def freshFn : Nat := 1\n", encoding="utf-8")
            m1 = copy.deepcopy(self.BASE_MANIFEST)
            m1["packages"]["LeanSwe.FreshPkg"] = {
                "kind": "property",
                "purity": "pure",
                "deps": [],
                "external_boundary": False,
            }
            (repo / "scripts/package_manifest.json").write_text(_dump(m1), encoding="utf-8")
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "add brand-new package and manifest entry")

            res_new_pkg = self._run_cli(repo, "HEAD~1", "HEAD")
            self.assertEqual(res_new_pkg.returncode, 0, res_new_pkg.stderr)
            self.assertIn("MANIFEST_CHECK: ok", res_new_pkg.stdout)
            self.assertIn("locked spec files touched=0", res_new_pkg.stdout)

            # Tier 2: pure strengthening (property -> model + add fuzz_suite + add dep) -> spec-add suffices.
            m2 = copy.deepcopy(m1)
            m2["packages"]["LeanSwe.FreshPkg"]["kind"] = "model"
            m2["packages"]["LeanSwe.FreshPkg"]["fuzz_suite"] = "float"
            m2["packages"]["LeanSwe.FreshPkg"]["deps"] = ["LeanSwe.PurePkg"]
            (repo / "scripts/package_manifest.json").write_text(_dump(m2), encoding="utf-8")
            _git(repo, "add", "scripts/package_manifest.json")
            _git(repo, "commit", "-m", "strengthen FreshPkg to model with fuzz_suite and dep")

            res_str_none = self._run_cli(repo, "HEAD~1", "HEAD")
            self.assertNotEqual(res_str_none.returncode, 0)
            self.assertIn("UNMARKED_SPEC_ADD", res_str_none.stderr)

            res_str_add = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add")
            self.assertEqual(res_str_add.returncode, 0, res_str_add.stderr)
            self.assertIn("MANIFEST_CHECK: ok", res_str_add.stdout)

            # Tier 3a: loosening external_boundary (true -> false) requires spec-change (even without @[extern]).
            (repo / "LeanSwe/Demo/Raw/Interface.lean").write_text("def rawCall : Nat := 1\n", encoding="utf-8")
            m3 = copy.deepcopy(m2)
            m3["packages"]["LeanSwe.Demo.Raw"]["external_boundary"] = False
            (repo / "scripts/package_manifest.json").write_text(_dump(m3), encoding="utf-8")
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "loosen external_boundary")

            res_ext_add = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add")
            self.assertNotEqual(res_ext_add.returncode, 0)
            self.assertIn("SPEC_CHANGE_REQUIRED", res_ext_add.stderr)
            self.assertIn("external_boundary", res_ext_add.stderr)

            res_ext_chg = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change")
            self.assertEqual(res_ext_chg.returncode, 0, res_ext_chg.stderr)

            # Tier 3b: removing fuzz_suite requires spec-change.
            m4 = copy.deepcopy(m3)
            del m4["packages"]["LeanSwe.FreshPkg"]["fuzz_suite"]
            (repo / "scripts/package_manifest.json").write_text(_dump(m4), encoding="utf-8")
            _git(repo, "add", "scripts/package_manifest.json")
            _git(repo, "commit", "-m", "remove fuzz_suite")

            res_rm_suite_add = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add")
            self.assertNotEqual(res_rm_suite_add.returncode, 0)
            self.assertIn("SPEC_CHANGE_REQUIRED", res_rm_suite_add.stderr)
            self.assertIn("removed fuzz_suite", res_rm_suite_add.stderr)

            res_rm_suite_chg = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change")
            self.assertEqual(res_rm_suite_chg.returncode, 0, res_rm_suite_chg.stderr)

    def test_locked_spec_json_files_require_spec_change(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_manifest_repo(tmp)
            for rel in ("scripts/external_assumptions.json",):
                (repo / rel).write_text('{"version": 1, "entries": []}\n', encoding="utf-8")
                _git(repo, "add", rel)
                _git(repo, "commit", "-m", f"add {rel}")

                res_none = self._run_cli(repo, "HEAD~1", "HEAD")
                self.assertNotEqual(res_none.returncode, 0)
                self.assertIn("UNMARKED_SPEC_CHANGE", res_none.stderr)
                self.assertIn(rel, res_none.stderr)

                res_add = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-add")
                self.assertNotEqual(res_add.returncode, 0)
                self.assertIn("SPEC_CHANGE_REQUIRED", res_add.stderr)

                res_chg = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change")
                self.assertEqual(res_chg.returncode, 0, res_chg.stderr)

    def test_extern_in_proofs_tree_caught_by_manifest_check(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self._init_manifest_repo(tmp)
            p = repo / "proofs/LeanSweProofs/PurePkg/Model.lean"
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text('@[extern "sneaky"] opaque sneaky : IO Unit\n', encoding="utf-8")
            errs = check_spec_change.validate_package_manifest(repo)
            self.assertTrue(any("declares external_boundary=false" in e for e in errs), errs)
            _git(repo, "add", ".")
            _git(repo, "commit", "-m", "sneaky extern in proofs")
            res = self._run_cli(repo, "HEAD~1", "HEAD", "--label", "spec-change")
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("MANIFEST_CHECK: failed", res.stderr)

    def test_removing_retired_manifest_key_with_strengthening_requires_spec_change(self) -> None:
        base = copy.deepcopy(self.BASE_MANIFEST)
        base["packages"]["LeanSwe.PurePkg"]["err_msg_opaque"] = True
        head = copy.deepcopy(self.BASE_MANIFEST)
        head["packages"]["LeanSwe.PurePkg"]["external_boundary"] = True
        head["packages"]["LeanSwe.PurePkg"]["deps"] = ["LeanSwe.SupportDir"]
        label, reason = check_spec_change.classify_package_manifest_texts(
            _dump(base),
            _dump(head),
            {"LeanSwe.Demo", "LeanSwe.PurePkg", "LeanSwe.SupportDir"},
        )
        self.assertEqual(label, check_spec_change.LABEL_CHANGE)
        self.assertIn("removed unknown key(s)", reason)
        self.assertIn("err_msg_opaque", reason)


if __name__ == "__main__":
    unittest.main()
