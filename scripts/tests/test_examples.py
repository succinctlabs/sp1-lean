"""Exercise the shared process boundary, including Lean's zero-exit diagnostic failures."""

import json
from pathlib import Path
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_examples


class ExampleTests(unittest.TestCase):
    def report(self):
        return {"revision": "test", "dirty": False,
                "assembly": "SP1Clean.Soundness.HostFinalMemory.ensemble", "table_count": 93,
                "cases": [{"id": name, "actual": value, "expected": value} for name, value in [
                    ("active-add", True), ("missing-ram-validator", False),
                    ("duplicate-ram-validator", False), ("wrong-final-record-clock", False),
                    ("missing-unchanged-register-validators", False), ("changed-untouched-x31", False),
                    ("changed-untouched-ram", False), ("missing-bank-terminal", False),
                    ("empty-identity", True)]]}

    def validate(self, report=None, stdout=None, stderr="", code=0):
        result = subprocess.CompletedProcess([], code, stdout if stdout is not None else
                                             json.dumps(report or self.report()), stderr)
        return check_examples.validate_report("add", result, "test", False)

    def test_valid_complete_output(self):
        self.assertEqual(self.validate(), self.report())

    def test_zero_exit_diagnostics(self):
        with self.assertRaises(ValueError):
            self.validate(stderr="error: stack overflow")
        with self.assertRaises(ValueError):
            self.validate(stdout=json.dumps(self.report()) + "\nerror: stack overflow")

    def test_failed_process_with_valid_output(self):
        with self.assertRaises(ValueError):
            self.validate(code=1)

    def test_partial_output(self):
        with self.assertRaises(ValueError):
            self.validate(stdout='{"cases": [')
        report = self.report()
        report["cases"].pop()
        with self.assertRaises(ValueError):
            self.validate(report)

    def test_forged_expectation_is_not_authoritative(self):
        report = self.report()
        report["cases"][1].update(expected=True, actual=True)
        with self.assertRaises(ValueError):
            self.validate(report)

    def test_truthy_values_and_stale_provenance(self):
        for value in [1, "true"]:
            report = self.report()
            report["cases"][0]["actual"] = value
            with self.assertRaises(ValueError):
                self.validate(report)
        report = self.report()
        report["revision"] = "stale"
        with self.assertRaises(ValueError):
            self.validate(report)

    def test_unknown_option_fails_without_output(self):
        result = subprocess.run([sys.executable, str(check_examples.ROOT / "scripts/check_examples.py"),
                                 "--unknown"], capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertFalse(result.stdout)


if __name__ == "__main__":
    unittest.main()
