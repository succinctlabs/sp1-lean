"""Fresh exports must preserve independent coverage and reject incomplete/stale evidence."""

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_witgen_export as export
import run_sp1_conformance as sp1


class WitnessExportTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        names = patch.object(export, "NAMES", ["Add"])
        names.start()
        self.addCleanup(names.stop)
        self.dump = {"schemaVersion": 1, "chip": "Add", "width": 1, "height": 2,
                     "events": [{"opcode": 1}], "rows": [[7], [0]]}
        self.dump_files()
        self.put("witgen/index.json", {"wireVersion": 1, "chips": [{
            "name": "Add", "witgenFile": "Add.witgen.json", "manifestFile": "Add.manifest.json",
            "inputWidth": 1, "localLength": 1}]})
        self.put("witgen/Add.witgen.json", {"version": 1, "localLength": 1, "operations": []})
        self.put("witgen/Add.manifest.json", {"wireVersion": 1, "name": "Add",
                 "witgenFile": "Add.witgen.json", "inputWidth": 1, "localLength": 1})
        self.put("witgen/Add.rowmap.json", {"wireVersion": 1, "name": "Add", "rustWidth": 1, "row": [0]})
        self.fixture = {"wireVersion": 1, "chip": "Add", "inputWidth": 1, "localLength": 1,
                        "rows": [{"kind": "event", "anchored": True, "inputs": [7],
                                  "expectedWitness": [7], "expectedRow": [7]}] + [
                            {"kind": "padding" if i == 0 else "synthetic", "anchored": False,
                             "inputs": [0], "expectedWitness": [0]} for i in range(6)]}
        self.save_fixture()

    def put(self, path, data):
        dest = self.root / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(json.dumps(data) + "\n")

    def dump_files(self):
        self.put("export/sp1dump/Add.dump.json", self.dump)
        self.put("export/sp1dump/index.json", {"schemaVersion": 1, "chips": ["Add"], "sp1Commit": "pin"})
        self.put("scripts/provenance.json", {"sp1": {"legacy": {"extractorRevision": "pin"}}})

    def save_fixture(self):
        self.put("testdata/Add.trace.json", self.fixture)

    def validate(self):
        return export.validate_generated(self.root, export.source_dumps(self.root))

    def test_complete_source_anchored_export(self):
        self.assertEqual(self.validate(), {"Add": 7})

    def test_self_consistent_counterfeit_anchor(self):
        self.fixture["rows"][0].update(inputs=[8], expectedWitness=[8], expectedRow=[8])
        self.save_fixture()
        with self.assertRaisesRegex(ValueError, "differs from SP1"):
            self.validate()

    def test_event_replaced_by_synthetic_preserving_count(self):
        self.fixture["rows"][0] = copy.deepcopy(self.fixture["rows"][-1])
        self.save_fixture()
        with self.assertRaisesRegex(ValueError, "row kind/anchor"):
            self.validate()

    def test_missing_padding(self):
        self.fixture["rows"].pop(1)
        self.save_fixture()
        with self.assertRaisesRegex(ValueError, "missing event, padding"):
            self.validate()

    def test_width_mismatch(self):
        self.fixture["rows"][0]["expectedWitness"].append(0)
        self.save_fixture()
        with self.assertRaisesRegex(ValueError, "row widths"):
            self.validate()

    def test_missing_and_extra_artifacts(self):
        (self.root / "witgen/Add.rowmap.json").rename(self.root / "witgen/Unknown.rowmap.json")
        with self.assertRaisesRegex(ValueError, "missing=.*Add.rowmap.*extra=.*Unknown"):
            self.validate()

    def test_dump_pin_mismatch(self):
        self.put("scripts/provenance.json", {"sp1": {"legacy": {"extractorRevision": "other"}}})
        with self.assertRaisesRegex(ValueError, "inventory/pin"):
            self.validate()

    def test_dump_padding_is_independent(self):
        self.dump["rows"][1] = [9]
        self.dump_files()
        with self.assertRaisesRegex(ValueError, "nonzero zero-fill"):
            self.validate()

    def test_completed_run_rejects_changed_sources_and_artifacts(self):
        record = {"sources": {"src": "first"}, "artifacts": export.hashes(self.root),
                  "rows": {"Add": 7}, "deterministic": True, "rustComparison": True}
        self.put("provenance.json", record)
        with patch.object(export, "source_dumps", return_value={"Add": self.dump}), \
                patch.object(export, "source_hashes", return_value={"src": "first"}):
            self.assertEqual(export.check_completed(self.root), self.root.resolve())
            self.fixture["rows"][-1]["inputs"] = [2]
            self.save_fixture()
            with self.assertRaisesRegex(ValueError, "artifacts changed"):
                export.check_completed(self.root)
        with patch.object(export, "source_dumps", return_value={"Add": self.dump}), \
                patch.object(export, "source_hashes", return_value={"src": "second"}):
            with self.assertRaisesRegex(ValueError, "sources changed"):
                export.check_completed(self.root)


class CompletionTests(unittest.TestCase):
    def test_zero_exit_partial_and_diagnostic_output_rejected(self):
        for testdata in (False, True):
            suffix = ": testdata 1 ms, 7 rows\n" if testdata else ": 1 ms, 12 bytes\n"
            end = "total: 25 chips (testdata), 1 ms\n" if testdata else "total: 25 chips, 1 ms\n"
            complete = "".join(name + suffix for name in export.NAMES) + end
            export.export_log_complete(complete, testdata)
            for broken in ("", complete.removesuffix(end), "Stack overflow\n", complete + "warning: test\n"):
                with self.subTest(testdata=testdata, output=broken[-80:]):
                    with self.assertRaisesRegex(ValueError, "incomplete or unexpected"):
                        export.export_log_complete(broken, testdata)


class StagingTests(unittest.TestCase):
    def test_checker_sources_and_lockfile_are_unmodified(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            package = root / "sp1/crates/core/compiler/conformance-check"
            (package / "src").mkdir(parents=True)
            (package / "src/main.rs").write_text("fn main() {}\n")
            (package / "Cargo.lock").write_text("# pinned lock\n")
            original = '\n'.join(f'dep{i} = {{ path = "{path}" }}' for i, path in
                                 enumerate(["..", "../../executor", "../witgen-interp"]))
            (package / "Cargo.toml").write_text(original)
            (root / "exports/witgen").mkdir(parents=True)
            (root / "exports/witgen/Add.witgen.json").write_text('{}\n')
            (root / "exports/provenance.json").write_text('{}\n')
            manifest = sp1.stage_checker(root / "sp1", root / "out", root / "exports")
            for name in ("src/main.rs", "Cargo.lock"):
                self.assertEqual((manifest.parent / name).read_bytes(), (package / name).read_bytes())
            self.assertEqual((package / "Cargo.toml").read_text(), original)
            self.assertIn(str(root / "sp1/crates/core/executor"), manifest.read_text())
            self.assertEqual((root / "out/testdata/lean-witgen/Add.witgen.json").read_text(), '{}\n')


if __name__ == "__main__":
    unittest.main()
