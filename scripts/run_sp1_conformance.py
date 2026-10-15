#!/usr/bin/env python3
"""Run the pinned SP1 checker against fresh exports, without modifying its checkout.

Pass --export-dir to reuse a completed check_witgen_export.py run with identical sources;
otherwise regenerate and validate first. The pinned checker source/lockfile are staged
under .lake, with only Cargo path dependencies relocated. Its runtime artifact path then
resolves to the fresh native exports. No fork patch or vendored generated files are needed.
"""

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from check_witgen_export import ROOT, NAMES, check_completed, generate, read_json, require, run


def stage_checker(sp1, out, exports):
    package = sp1 / "crates/core/compiler/conformance-check"
    dest = out / "conformance-check"
    shutil.copytree(package / "src", dest / "src")
    shutil.copyfile(package / "Cargo.lock", dest / "Cargo.lock")
    manifest = (package / "Cargo.toml").read_text()
    # Preserve every dependency/version/feature; only move the three relative paths.
    paths = re.findall(r'path = "([^"]+)"', manifest)
    require(paths == ["..", "../../executor", "../witgen-interp"],
            "pinned conformance checker layout changed; review its dependencies")
    manifest = re.sub(r'path = "([^"]+)"',
                      lambda match: "path = " + json.dumps(str((package / match[1]).resolve())), manifest)
    (dest / "Cargo.toml").write_text(manifest)
    shutil.copytree(exports / "witgen", out / "testdata/lean-witgen")
    shutil.copyfile(exports / "provenance.json", out / "provenance.json")
    return dest / "Cargo.toml"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sp1-dir", type=Path, default=Path(os.environ.get("SP1_DIR", "../sp1")))
    parser.add_argument("--export-dir", type=Path)
    args = parser.parse_args()
    try:
        sp1 = args.sp1_dir.resolve()
        pin = read_json(ROOT / "scripts/provenance.json")["sp1"]["legacy"]["extractorRevision"]
        revision = subprocess.check_output(["git", "-C", str(sp1), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(sp1), "status", "--porcelain",
                                         "--untracked-files=no"], text=True)
        require(revision == pin and not dirty, f"{sp1}: require clean pinned extraction checkout {pin}")
        exports = check_completed(args.export_dir) if args.export_dir else generate()
        out = Path(tempfile.mkdtemp(prefix="sp1.", dir=exports.parent))
        manifest = stage_checker(sp1, out, exports)
        env = dict(os.environ, CARGO_BUILD_JOBS=os.environ.get("CARGO_BUILD_JOBS", "2"))
        env.setdefault("CARGO_TARGET_DIR", str(ROOT / ".lake/sp1-conformance-target"))
        output = run(["cargo", "run", "--locked", "--release", "--quiet", "--manifest-path", str(manifest)],
                     out / "rust.log", env, cwd=sp1)
        require(all(f"{name}: ok\n" in output for name in NAMES) and
                output.endswith(f"witgen conformance: all {len(NAMES)} chips reproduce generate_trace\n"),
                f"incomplete live SP1 comparison: {out}/rust.log")
        check_completed(exports)
        print(f"PASS: all {len(NAMES)} chips reproduce pinned SP1 generate_trace; evidence: {out}")
    except (ValueError, OSError, KeyError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"FAIL: {error}\n")


if __name__ == "__main__":
    main()
