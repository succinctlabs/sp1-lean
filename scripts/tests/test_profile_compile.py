"""Exercise the profiling shell runner without compiling Lean or touching other processes."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]


class ProfileRunnerTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="sp1-profile-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "scripts").mkdir()
        for name in ("profile_compile.sh", "profile_aggregate.py", "lean_flags.py"):
            shutil.copy2(ROOT / "scripts" / name, self.root / "scripts" / name)
        shutil.copy2(ROOT / "lakefile.toml", self.root / "lakefile.toml")
        for tree in ("SP1Clean", "ToPolyFun"):
            (self.root / tree).mkdir()
            (self.root / tree / "Example.lean").write_text("-- process fixture\n")
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.executable("lake", '''
import json, os, sys
with open(os.environ["CALLS"], "a") as output:
    output.write(json.dumps(sys.argv[1:]) + "\\n")
if sys.argv[1] == "build":
    sys.exit(int(os.environ.get("FAIL_BUILD", "0")))
if sys.argv[1] == "env":
    if os.environ.get("FAIL_ENV"):
        sys.exit(1)
    print("LEAN_PATH=fixture")
''')
        self.executable("lean", '''
import os, sys
if "--version" in sys.argv:
    print("Lean process fixture")
    sys.exit(0)
case = os.environ.get("PROFILE_CASE", "ok")
if sys.argv[-1].startswith("ToPolyFun/"):
    case = "ok"
if case == "exit":
    sys.exit(7)
if case == "empty":
    sys.exit(0)
if case == "overflow":
    print("error: stack overflow", file=sys.stderr)
    sys.exit(0)
print("cumulative profiling times:", file=sys.stderr)
print("\\timport " + ("1e+03ms" if case == "scientific" else "2ms"), file=sys.stderr)
if case != "partial":
    print("\\tmodule linting " + ("6.25e-4ms" if case == "scientific" else "0.1ms"), file=sys.stderr)
if case in ("error", "warning"):
    print(f"Example.lean:1:0: {case}: unexpected diagnostic")
''')
        self.executable("pkill", '''
import os
from pathlib import Path
Path(os.environ["KILL_MARKER"]).touch()
raise SystemExit("profiling must not signal unrelated processes")
''')
        self.out = self.root / "results"
        self.calls = self.root / "calls.jsonl"
        self.kill_marker = self.root / "kill-called"

    def executable(self, name, source):
        path = self.bin / name
        path.write_text(f"#!{sys.executable}\n" + source)
        path.chmod(0o755)

    def run_profile(self, *args, **environment):
        env = dict(os.environ)
        for name in ("SKIP_BUILD", "TREES", "EXCLUDE_RE", "LEAN", "TOP"):
            env.pop(name, None)
        env.update(PATH=str(self.bin) + os.pathsep + env["PATH"], OUTDIR=str(self.out),
                   CALLS=str(self.calls), KILL_MARKER=str(self.kill_marker), **environment)
        return subprocess.run(["bash", "scripts/profile_compile.sh", *args], cwd=self.root,
                              env=env, capture_output=True, text=True, timeout=20)

    def measurements(self):
        return [json.loads(line) for line in (self.out / "measurements.jsonl").read_text().splitlines()]

    def test_default_warms_full_closure_without_signalling_processes(self):
        result = self.run_profile()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        calls = [json.loads(line) for line in self.calls.read_text().splitlines()]
        self.assertEqual(calls, [["build", "--wfail", "--iofail", "SP1Clean", "SP1CleanTest",
                                  "ToClean", "ToMathlib", "ToPolyFun"], ["env"]])
        self.assertFalse(self.kill_marker.exists())
        records = self.measurements()
        self.assertEqual({r["metric"] for r in records},
                         {"compile//SP1Clean.Example", "compile//ToPolyFun.Example"})
        self.assertTrue(all(r["exit"] == 0 for r in records))
        self.assertTrue((self.out / "profile.json").is_file())

    def test_failed_warmup_or_environment_never_starts_measurement(self):
        for failure in ("FAIL_BUILD", "FAIL_ENV"):
            with self.subTest(failure=failure):
                result = self.run_profile(**{failure: "1"})
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(self.measurements(), [])

    def test_empty_selection_fails(self):
        result = self.run_profile("SP1Clean/Missing", SKIP_BUILD="1")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("no modules selected", result.stderr)

    def test_scientific_notation_is_a_complete_report(self):
        # Lean prints e.g. `import 1e+03ms` on real, successful compiler runs.
        result = self.run_profile(SKIP_BUILD="1", PROFILE_CASE="scientific")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue(all(r["exit"] == 0 for r in self.measurements()))

    def test_failed_and_zero_exit_incomplete_runs_fail_the_sweep(self):
        for case in ("exit", "empty", "overflow", "partial", "error", "warning"):
            with self.subTest(case=case):
                result = self.run_profile(SKIP_BUILD="1", PROFILE_CASE=case)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                records = {r["metric"]: r for r in self.measurements()}
                self.assertNotEqual(records["compile//SP1Clean.Example"]["exit"], 0)
                # Finish the sweep and retain diagnostics for every module after a failure.
                self.assertEqual(records["compile//ToPolyFun.Example"]["exit"], 0)
                self.assertTrue((self.out / "profile.json").is_file())


if __name__ == "__main__":
    unittest.main()
