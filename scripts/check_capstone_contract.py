#!/usr/bin/env python3
"""Check compiled capstone target types and their definition-dependency manifest.

Default builds the target first. --no-build is for the release harness after its full build.
--update explicitly refreshes the manifest after reviewing the semantic/type delta; it never
changes Lean source or the allowed axioms. A fresh output file is required even on exit zero
because the Lean frontend can return zero after a stack overflow.
"""

import argparse
import difflib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
SNAPSHOT = ROOT / "docs/snapshots/capstone-contract.json"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-build", action="store_true")
    parser.add_argument("--update", action="store_true")
    args = parser.parse_args()
    if not args.no_build:
        subprocess.run(
            ["lake", "build", "--wfail", "--iofail", "SP1Clean.Soundness.Shard.Machine"],
            cwd=ROOT, check=True,
        )
    with tempfile.TemporaryDirectory(prefix="sp1-capstone-contract-") as temporary:
        output = Path(temporary) / "contract.json"
        environment = {**os.environ, "CAPSTONE_SURFACE_OUT": str(output)}
        result = subprocess.run(
            ["lake", "env", "lean", "scripts/capstoneContract.lean"],
            cwd=ROOT, env=environment, capture_output=True, text=True,
        )
        diagnostics = result.stdout + result.stderr
        if result.returncode or diagnostics.strip() or not output.is_file():
            print(diagnostics, end="")
            print("FAIL: compiled capstone contract check did not complete cleanly")
            return 1
        data = json.loads(output.read_text())
        if data.get("version") != 1 or len(data.get("roots", [])) != 8 or not data.get("declarations"):
            print("FAIL: incomplete capstone contract manifest")
            return 1
        fresh = json.dumps(data, indent=2, sort_keys=True) + "\n"
    if args.update:
        SNAPSHOT.write_text(fresh)
        print(f"Updated {SNAPSHOT.relative_to(ROOT)}; review all semantic/type changes")
    elif not SNAPSHOT.is_file() or SNAPSHOT.read_text() != fresh:
        old = SNAPSHOT.read_text() if SNAPSHOT.is_file() else ""
        sys.stdout.writelines(difflib.unified_diff(
            old.splitlines(keepends=True), fresh.splitlines(keepends=True),
            fromfile=str(SNAPSHOT.relative_to(ROOT)), tofile="compiled contract",
        ))
        print("FAIL: capstone contract drift; review before an explicit --update")
        return 1
    print(f"PASS: capstone target types and {len(data['declarations'])} definition dependencies")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
