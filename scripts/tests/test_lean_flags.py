"""Regressions for scripts/lean_flags.py: the package flags a direct `lean` invocation must
replicate, read from lakefile.toml (with the minimal-TOML fallback used on Python < 3.11)."""

import importlib.util
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "lean_flags", Path(__file__).resolve().parents[1] / "lean_flags.py"
)
lean_flags = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(lean_flags)

SAMPLE = '''
name = "demo"            # comment with "quotes"
moreLeanArgs = ["--tstack=400000"]

[leanOptions]
pp.unicode.fun = true
autoImplicit = false
weak.linter.style.header = false     # 950 files

[[lean_lib]]
name = "Gen"
leanOptions.autoImplicit = true
moreLeancArgs = ["-fbracket-depth=500"]

[[lean_lib]]
name = "Tests"
leanOptions.weak.linter.hashCommand = false
'''


class MinimalTomlTests(unittest.TestCase):
    def test_subset_parses(self):
        cfg = lean_flags.parse_minimal_toml(SAMPLE)
        self.assertEqual(cfg["name"], "demo")
        self.assertEqual(cfg["moreLeanArgs"], ["--tstack=400000"])
        self.assertEqual(cfg["leanOptions"]["weak"]["linter"]["style"]["header"], False)
        self.assertEqual([lib["name"] for lib in cfg["lean_lib"]], ["Gen", "Tests"])

    def test_rejects_unsupported_lines(self):
        with self.assertRaises(ValueError):
            lean_flags.parse_minimal_toml("x = { a = 1 }\n")


class FlagsTests(unittest.TestCase):
    def test_package_and_library_flags(self):
        cfg = lean_flags.parse_minimal_toml(SAMPLE)
        self.assertEqual(
            lean_flags.flags_for(cfg),
            ["--tstack=400000", "-Dpp.unicode.fun=true", "-DautoImplicit=false",
             "-Dweak.linter.style.header=false"])
        gen = lean_flags.flags_for(cfg, "Gen")
        self.assertIn("-DautoImplicit=true", gen)
        self.assertNotIn("-DautoImplicit=false", gen)
        self.assertIn("-Dweak.linter.hashCommand=false", lean_flags.flags_for(cfg, "Tests"))
        with self.assertRaises(KeyError):
            lean_flags.flags_for(cfg, "Nope")

    def test_real_lakefile(self):
        cfg = lean_flags.load_lakefile(str(Path(__file__).resolve().parents[2] / "lakefile.toml"))
        flags = lean_flags.flags_for(cfg)
        self.assertIn("--tstack=400000", flags)
        self.assertIn("-DautoImplicit=false", flags)
        # both readers must agree on the real file
        text = (Path(__file__).resolve().parents[2] / "lakefile.toml").read_text()
        self.assertEqual(lean_flags.flags_for(lean_flags.parse_minimal_toml(text)), flags)


if __name__ == "__main__":
    unittest.main()
