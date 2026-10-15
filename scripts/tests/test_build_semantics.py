"""Regressions for the build-log analysis in scripts/build_semantics.py (critical path, timeline,
timestamped log parsing, touched-module lists)."""

import importlib.util
from pathlib import Path
import tempfile
import unittest


SPEC = importlib.util.spec_from_file_location(
    "build_semantics", Path(__file__).resolve().parents[1] / "build_semantics.py"
)
bsem = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(bsem)


class CriticalPathTests(unittest.TestCase):
    def test_longest_weighted_path_follows_imports(self):
        # D imports B and C; B and C import A. Weights make A -> C -> D the heaviest chain.
        imports = {"A": [], "B": ["A"], "C": ["A"], "D": ["B", "C"]}
        secs = {"A": 1.0, "B": 2.0, "C": 5.0, "D": 1.0}
        length, path = bsem.critical_path(imports, secs)
        self.assertEqual(length, 7.0)
        self.assertEqual(path, ["A", "C", "D"])

    def test_modules_without_times_are_skipped(self):
        # X was not rebuilt (no time), so D does not chain through it to A: A alone is longest.
        imports = {"A": [], "X": ["A"], "D": ["X"]}
        secs = {"A": 3.0, "D": 2.0}
        length, path = bsem.critical_path(imports, secs)
        self.assertEqual((length, path), (3.0, ["A"]))

    def test_empty(self):
        self.assertEqual(bsem.critical_path({}, {}), (0.0, []))


class LogParsingTests(unittest.TestCase):
    def test_timestamped_and_plain_built_lines(self):
        with tempfile.TemporaryDirectory() as tmp:
            log = Path(tmp) / "lake.log"
            log.write_text(
                "﻿2026-09-21T20:30:00.1234567Z ✔ [1/3] Built Foo.Bar (12s)\n"
                "2026-09-21T20:30:02.0000000Z ✔ [2/3] Built Foo.Baz (500ms)\n"
                "✔ [3/3] Built Foo.Local (2.5s)\n"
            )
            events = bsem.read_lake_log_events(str(log))
        self.assertEqual(events["Foo.Bar"][0], 12.0)
        self.assertEqual(events["Foo.Baz"][0], 0.5)
        self.assertAlmostEqual(events["Foo.Baz"][1] - events["Foo.Bar"][1], 2.0)
        self.assertEqual(events["Foo.Local"], (2.5, None))

    def test_timeline_reports_solo_tail(self):
        # One 300 s job alone after two 60 s jobs that overlapped it at the start.
        t = 1_000_000.0
        events = {"long": (300.0, t + 300), "a": (60.0, t + 60), "b": (60.0, t + 60), "tiny": (0.2, t + 1)}
        tl = bsem.timeline(events, bucket=60)
        self.assertEqual(tl["solo"][0], "long")
        self.assertGreaterEqual(tl["le1"], 180)
        self.assertNotIn("tiny", [tl["solo"][0]])  # sub-second jobs are excluded from the histogram
        self.assertIsNone(bsem.timeline({"x": (1.0, None)}))


class TouchedTests(unittest.TestCase):
    def test_paths_and_names(self):
        with tempfile.TemporaryDirectory() as tmp:
            f = Path(tmp) / "touched.txt"
            f.write_text("SP1Clean/Math/Word.lean\nSP1Clean.Model.Register\nscripts/foo.py\n\n")
            touched = bsem.read_touched(str(f), {"SP1Clean.Math.Word", "SP1Clean.Model.Register"})
        self.assertEqual(touched, {"SP1Clean.Math.Word", "SP1Clean.Model.Register"})


if __name__ == "__main__":
    unittest.main()
