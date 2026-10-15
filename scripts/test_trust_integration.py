#!/usr/bin/env python3
"""Executable adversarial fixtures, kept outside every released library.

Run with `lake env python3 scripts/test_trust_integration.py`. Temporary Lean modules
deliberately contain admissions/axioms; neither they nor their oleans enter the project roots.
"""

import json
import os
from pathlib import Path
import subprocess
import tempfile

import check_trust as trust


def main():
    policy = trust.load_policy()
    scanner = trust.scanner_path()
    fixtures = {
        "Clean": """import Lean
namespace NamesDoNotOwnModules
theorem ordinary : 1 = 1 := rfl
theorem addedWithoutRegistration : True := True.intro
end NamesDoNotOwnModules
""",
        "Tainted": """import Lean
namespace TrustFixture
private theorem hidden : False := by sorry
theorem inherited : False := hidden
axiom unknown : False
theorem transitive : 1 = 2 := False.elim unknown
axiom index : Nat
axiom inType : Fin (index + 1)
axiom mutualProof : True
mutual
  inductive Left : Type where
    | fromRight : Right → Left
    | tainted : True.intro = mutualProof → Left
  inductive Right : Type where
    | fromLeft : Left → Right
end
axiom Fake._native.native_decide.ax_1_extra : True
theorem fakeNative : True := Fake._native.native_decide.ax_1_extra
end TrustFixture
""",
        "Native": """import Lean
namespace TrustFixture
theorem computed : 1 = 1 := by native_decide
end TrustFixture
""",
        "NativeAgain": """import Lean
namespace TrustFixtureAgain
theorem computed : True ∧ True := by
  have first : True := by native_decide
  have second : True := by native_decide
  exact ⟨first, second⟩
end TrustFixtureAgain
""",
    }
    with tempfile.TemporaryDirectory(prefix="sp1-trust-fixtures-") as tmp:
        root = Path(tmp)
        directory = root / "TrustFixtures"
        directory.mkdir()
        env = {**os.environ, "LEAN_PATH": str(root) + os.pathsep + os.environ.get("LEAN_PATH", "")}
        for name, source in fixtures.items():
            path = directory / f"{name}.lean"
            path.write_text(source)
            subprocess.run(["lean", "-R", str(root), "-o", str(path.with_suffix(".olean")), str(path)],
                           env=env, text=True, capture_output=True, check=True)
        roots = [f"TrustFixtures.{name}" for name in fixtures]
        args = ["lean", "--run", str(scanner)]
        for module in roots:
            args.extend(["--root", module])
        raw = root / "report.json"
        run = subprocess.run(args + ["--out", str(raw)], env=env, text=True, capture_output=True, check=True)
        entries = trust.validate_report(json.loads(raw.read_text()), roots, roots, run.stdout)
        by_name = {e["name"]: e for e in entries}
        assert "sorryAx" in by_name["TrustFixture.inherited"]["axioms"]
        assert any("hidden" in e["name"] and "sorryAx" in e["axioms"] for e in entries)
        assert "TrustFixture.unknown" in by_name["TrustFixture.transitive"]["axioms"]
        assert "TrustFixture.index" in by_name["TrustFixture.inType"]["axioms"]
        assert "TrustFixture.mutualProof" in by_name["TrustFixture.Right"]["axioms"]
        assert "TrustFixture.Fake._native.native_decide.ax_1_extra" in by_name["TrustFixture.fakeNative"]["axioms"]
        assert any(v["declaration"] == "TrustFixture.fakeNative"
                   for v in trust.evaluate(entries, "test", policy)[1])
        clean = [e for e in entries if e["module"] == "TrustFixtures.Clean"]
        assert len(clean) >= 2 and not trust.evaluate(clean, "main", policy)[1]
        for name in ("TrustFixture.computed", "TrustFixtureAgain.computed"):
            native = [by_name[name]]
            assert native[0]["axioms"] == [name + "._native.native_decide"]
            assert trust.evaluate(native, "main", policy)[1]
            assert not trust.evaluate(native, "test", policy)[1]
        missing = subprocess.run(["lean", "--run", str(scanner), "--root", "TrustFixtures.Missing"],
                                 env=env, text=True, capture_output=True)
        assert missing.returncode != 0
    print("PASS: compiled trust fixtures (private/transitive/type/mutual/native/coverage)")


if __name__ == "__main__":
    main()
