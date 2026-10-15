"""The built-in Rust comparison must retain every supported instruction family."""

from pathlib import Path
import copy
import json
import re
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_release_surface import ROOT, instruction_export_errors, coverage_errors


class InstructionExportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lean = (ROOT / "SP1CleanTest/Core/InstructionExport.lean").read_text()
        cls.rust = (ROOT / "rust/sp1-comparison/tests/instruction_export.rs").read_text()

    def test_current_sources_cover_release(self):
        self.assertEqual(instruction_export_errors(self.lean, self.rust), [])

    def test_missing_export_is_rejected(self):
        lean = self.lean.replace('"jal_instruction.rs"', '"missing.rs"')
        self.assertIn("built-in instruction exporter inventory/order differs",
                      instruction_export_errors(lean, self.rust))

    def test_duplicate_export_is_rejected(self):
        lean = self.lean + '\n("jal_instruction.rs", ignored)'
        self.assertTrue(instruction_export_errors(lean, self.rust))

    def test_missing_rust_comparison_is_rejected(self):
        rust, count = re.subn(
            r'generated_instruction!\(\s*generated_jal,.*?\);', '', self.rust, flags=re.S)
        self.assertEqual(count, 1)
        self.assertIn("Rust instruction comparison registrations differ",
                      instruction_export_errors(self.lean, rust))

    def test_wrong_program_or_air_is_rejected(self):
        for name in ("JalInstruction", "JalInstructionAirSpec"):
            with self.subTest(name=name):
                rust = self.rust.replace(name + "\n", "OtherProgram\n", 1)
                rust = rust.replace(name + ",\n", "OtherProgram,\n", 1)
                self.assertNotEqual(rust, self.rust)
                self.assertTrue(instruction_export_errors(self.lean, rust))


class ReleaseCoverageTests(unittest.TestCase):
    def setUp(self):
        directory = ROOT / "rust/sp1-comparison/inventory"
        self.record = json.loads((directory / "coverage.json").read_text())
        self.inventories = {mode: json.loads((directory / (mode + ".json")).read_text())
                            for mode in ("supervisor", "mprotect")}
        self.revision = json.loads((ROOT / "scripts/provenance.json").read_text())["sp1"]["revision"]
        self.native = {"publicWidth": self.record["publicWidth"], "tables": [
            {key: value for key, value in table.items() if key != "group"} | {"slot": index}
            for index, table in enumerate(self.record["native"])]}

    def check(self):
        return coverage_errors(self.record, self.inventories, self.revision, self.native)

    def test_review_is_complete(self):
        self.assertEqual(self.check(), [])

    def test_stale_review_fails(self):
        self.record["revision"] = "0" * 40
        self.assertIn("coverage review belongs to a different SP1 revision", self.check())

    def test_new_source_layout_requires_review(self):
        self.inventories["mprotect"]["layouts"].append({"name": "NewUserLayout"})
        self.assertIn("released coverage has missing or stale layouts", self.check())

    def test_source_width_and_cluster_occurrences_require_review(self):
        original = copy.deepcopy(self.inventories["supervisor"])
        for variant in ("width", "cluster"):
            with self.subTest(variant=variant):
                inventory = self.inventories["supervisor"] = copy.deepcopy(original)
                if variant == "width":
                    inventory["layouts"][0]["main_width"] += 1
                else:
                    inventory["clusters"][0].append(inventory["clusters"][0][0])
                self.assertIn("supervisor: released inventory differs from the coverage review", self.check())

    def test_removed_source_layout_fails(self):
        self.record["released"]["DeletedChip"] = "instructions"
        self.assertIn("released coverage has missing or stale layouts", self.check())

    def test_unknown_status_and_missing_evidence_fail(self):
        self.record["groups"]["instructions"]["export"] = "proved-everything"
        self.record["groups"]["instructions"]["comparison"] = ["missing.rs"]
        self.assertEqual(len(self.check()), 2)

    def test_native_width_order_and_repeated_occurrence_drift_fail(self):
        original = copy.deepcopy(self.native["tables"])
        for variant in ("width", "order", "repeat", "lookup"):
            with self.subTest(variant=variant):
                self.native["tables"] = copy.deepcopy(original)
                tables = self.native["tables"]
                if variant == "width":
                    tables[0]["width"] += 1
                elif variant == "order":
                    tables[0], tables[1] = tables[1], tables[0]
                elif variant == "repeat":
                    tables.append(copy.deepcopy(tables[0]))
                else:
                    tables[0]["lookups"].append("unreviewed.lookup")
                self.assertIn(
                    "native coverage differs from installed component order, widths or lookups",
                    self.check())

    def test_legacy_lookup_cannot_claim_builtin_export(self):
        self.record["groups"]["program"]["export"] = "component"
        self.assertTrue(any("legacy lookup" in error for error in self.check()))

    def test_public_width_drift_fails(self):
        self.native["publicWidth"] += 1
        self.assertIn("native public-input width differs", self.check())


if __name__ == "__main__":
    unittest.main()
