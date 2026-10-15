"""Trust-policy failures must be observable without a Lean build."""

import copy
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("check_trust", Path(__file__).resolve().parents[1] / "check_trust.py")
trust = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(trust)


class TrustPolicyTests(unittest.TestCase):
    def setUp(self):
        self.policy = trust.load_policy()

    def test_standard_and_existing_exceptions(self):
        for name in trust.STANDARD:
            self.assertEqual(trust.classify(name, "main", self.policy), "logical")
        for name in self.policy["sail"]["names"]:
            self.assertEqual(trust.classify(name, "main", self.policy), "sail")
        for name in self.policy["bvDecide"]["names"]:
            self.assertEqual(trust.classify(name, "main", self.policy), "approved-bv")

    def test_no_admissions_or_unknown_axioms_in_either_scope(self):
        for scope in ("main", "test"):
            for name in ("sorryAx", "Unreviewed.axiom", "Lean.trustCompiler", "Lean.ofReduceBool"):
                self.assertEqual(trust.classify(name, scope, self.policy), "forbidden")

    def test_native_computation_is_quarantined(self):
        for tactic in ("native_decide", "bv_decide"):
            name = f"FreshProof._native.{tactic}"
            self.assertEqual(trust.classify(name, "main", self.policy), "forbidden")
            self.assertEqual(trust.classify(name, "test", self.policy), "test-native")

    def test_lookalike_native_names_are_not_exceptions(self):
        for suffix in (".ax_1_extra", ".ax_x_34", ".ax_1_2.extra", ".ax_1", ".axiom"):
            self.assertEqual(trust.classify("Foo._native.native_decide" + suffix, "test", self.policy), "forbidden")
        self.assertEqual(trust.classify("Foo._native.unknownTactic", "test", self.policy), "forbidden")

    def test_policy_cannot_disguise_admissions_as_standard(self):
        for mutate in (
            lambda p: p["standard"].append("sorryAx"),
            lambda p: p["sail"]["names"].append("sorryAx"),
            lambda p: p["bvDecide"]["names"].append("Foo._native.native_decide"),
            lambda p: p["testNativeTactics"].append("unreviewed"),
            lambda p: p["sail"].update(reason=""),
        ):
            policy = copy.deepcopy(self.policy)
            mutate(policy)
            with tempfile.TemporaryDirectory() as tmp:
                path = Path(tmp) / "policy.json"
                path.write_text(json.dumps(policy))
                with self.assertRaises(ValueError):
                    trust.load_policy(path)

    def test_new_ordinary_declaration_needs_no_registration(self):
        entries = [{"name": "BrandNew.theorem", "module": "SP1Clean.Example", "axioms": ["propext"]}]
        self.assertEqual(trust.evaluate(entries, "main", self.policy)[1], [])
        entries[0]["axioms"].append("Indirect.bad")
        self.assertEqual(trust.evaluate(entries, "main", self.policy)[1][0]["declaration"], "BrandNew.theorem")

    def test_scope_discovery_uses_files_not_namespaces(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(trust, "ROOT", Path(tmp)):
            directory = Path(tmp) / "SP1CleanTest"
            directory.mkdir()
            for file in ("A", "B"):
                (directory / f"{file}.lean").write_text("namespace Unrelated\nend Unrelated\n")
            self.assertEqual(trust.scope_modules("test"), (["SP1CleanTest.A", "SP1CleanTest.B"],) * 2)

    def test_coverage_empty_duplicate_and_malformed_reports_fail(self):
        entry = {"name": "OtherNamespace.fact", "module": "SP1Clean.Example", "axioms": []}
        report = {"roots": ["SP1Clean"], "declarationCount": 1, "declarations": [entry]}
        output = "axiomsweep: 1 declarations across 2 modules under #[SP1Clean]\n"
        modules = ["SP1Clean", "SP1Clean.Example"]
        self.assertEqual(trust.validate_report(report, ["SP1Clean"], modules, output), [entry])
        for bad, stdout in (
            ({**report, "roots": ["Wrong"]}, output),
            ({**report, "declarationCount": 0, "declarations": []}, output),
            ({**report, "declarationCount": 2, "declarations": [entry, entry]}, output.replace("1 declarations", "2 declarations")),
            ({**report, "declarations": [{**entry, "axioms": "sorryAx"}]}, output),
            (report, output.replace("2 modules", "1 modules")),
            (report, ""),
        ):
            with self.assertRaises(ValueError):
                trust.validate_report(bad, ["SP1Clean"], modules, stdout)

    def test_scanner_failure_replaces_stale_success_report(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            (directory / "test.json").write_text('{"status":"pass"}')
            with patch.object(trust, "metadata", return_value={}), \
                 patch.object(trust, "scanner_path", side_effect=ValueError("scanner unavailable")), \
                 contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(trust.scan("test", self.policy, trust.POLICY, directory), 2)
            self.assertEqual(json.loads((directory / "test.json").read_text())["status"], "error")

    def test_retired_update_and_conflicting_scopes_fail_before_work(self):
        before = trust.POLICY.read_bytes()
        for args in (["--update"], ["--main-only", "--test-only"], ["--unknown"]):
            run = subprocess.run([str(trust.ROOT / "scripts/run_audit.sh"), *args],
                                 text=True, capture_output=True)
            self.assertEqual(run.returncode, 2)
            self.assertNotIn("== A0 pins ==", run.stdout)
        self.assertEqual(trust.POLICY.read_bytes(), before)


if __name__ == "__main__":
    unittest.main()
