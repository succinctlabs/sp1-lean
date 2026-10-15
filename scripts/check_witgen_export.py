#!/usr/bin/env python3
"""Generate deterministic native witnesses with Clean and compare every row in Rust.

Default: build the full Lean closure, export twice into a fresh ignored directory,
check source-anchored coverage and byte agreement, then run locked Rust tests.
--source-only checks the committed SP1 inputs without Lean or Cargo (CI guards/audit).
--check-dir DIR verifies a completed run against current sources before external reuse.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from check_pins import check as check_pins
from check_release_surface import CHIPS
from lean_flags import flags_for, load_lakefile

ROOT = Path(__file__).resolve().parents[1]
NAMES = [name for _, name, _ in CHIPS]
DERIVED_PADDING = {"ShiftLeft", "ShiftRight", "DivRem"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    raw = path.read_bytes()
    require(raw.endswith(b"\n"), f"{path}: missing trailing newline")
    return json.loads(raw)


def inventory(directory, expected):
    actual = {p.name for p in directory.iterdir()}
    require(actual == set(expected),
            f"{directory}: missing={sorted(set(expected) - actual)}, extra={sorted(actual - set(expected))}")


def source_dumps(root=ROOT):
    directory = root / "export/sp1dump"
    inventory(directory, ["index.json", *(f"{n}.dump.json" for n in NAMES)])
    index = read_json(directory / "index.json")
    pin = read_json(root / "scripts/provenance.json")["sp1"]["legacy"]["extractorRevision"]
    require(index["schemaVersion"] == 1 and index["chips"] == sorted(NAMES)
            and index["sp1Commit"] == pin, "SP1 dump index differs from the independent inventory/pin")
    dumps = {}
    for name in NAMES:
        d = read_json(directory / f"{name}.dump.json")
        require(d["schemaVersion"] == 1 and d["chip"] == name, f"{name}: dump identity")
        require(d["events"] and len(d["events"]) < d["height"] == len(d["rows"])
                and all(len(row) == d["width"] for row in d["rows"]), f"{name}: dump dimensions")
        padding = d["rows"][len(d["events"]):]
        require(all(row == padding[0] for row in padding), f"{name}: nonuniform padding")
        if name not in DERIVED_PADDING:
            require(all(cell == 0 for cell in padding[0]), f"{name}: nonzero zero-fill padding")
        dumps[name] = d
    return dumps


def validate_generated(directory, dumps):
    """Check all native outputs against the independently generated SP1 inputs."""
    wg, td = directory / "witgen", directory / "testdata"
    inventory(wg, ["index.json", *(f"{n}.{s}.json" for n in NAMES
                                 for s in ("witgen", "manifest", "rowmap"))])
    inventory(td, [f"{n}.trace.json" for n in NAMES])
    index = read_json(wg / "index.json")
    require(index["wireVersion"] == 1 and [c["name"] for c in index["chips"]] == NAMES,
            "native index order/coverage differs from the independent release inventory")
    counts = {}
    for name, entry in zip(NAMES, index["chips"]):
        payload = read_json(wg / f"{name}.witgen.json")
        manifest = read_json(wg / f"{name}.manifest.json")
        rowmap = read_json(wg / f"{name}.rowmap.json")
        fixture = read_json(td / f"{name}.trace.json")
        dump = dumps[name]
        require(payload["version"] == manifest["wireVersion"] == rowmap["wireVersion"]
                == fixture["wireVersion"] == 1, f"{name}: wire version")
        require(manifest["name"] == rowmap["name"] == fixture["chip"] == name,
                f"{name}: artifact identity")
        require(entry["witgenFile"] == manifest["witgenFile"] == f"{name}.witgen.json"
                and entry["manifestFile"] == f"{name}.manifest.json", f"{name}: filenames")
        require(isinstance(payload["operations"], list), f"{name}: operations")
        require(payload["localLength"] == manifest["localLength"], f"{name}: witness width")
        require(rowmap["rustWidth"] == len(rowmap["row"]) == dump["width"], f"{name}: Rust width")
        for key in ("inputWidth", "localLength"):
            require(entry[key] == manifest[key] == fixture[key], f"{name}: {key}")
        rows, events = fixture["rows"], len(dump["events"])
        require(len(rows) == events + 6, f"{name}: missing event, padding or synthetic rows")
        for i, row in enumerate(rows):
            require(len(row["inputs"]) == manifest["inputWidth"] and
                    len(row["expectedWitness"]) == manifest["localLength"], f"{name}/{i}: row widths")
            kind = "event" if i < events else "padding" if i == events else "synthetic"
            anchored = i < events or (i == events and name in DERIVED_PADDING)
            require(row["kind"] == kind and row["anchored"] is anchored, f"{name}/{i}: row kind/anchor")
            if anchored:
                require(row["expectedRow"] == dump["rows"][i], f"{name}/{i}: differs from SP1 dump")
            else:
                require(row.get("expectedRow") is None, f"{name}/{i}: unexpected SP1 anchor")
        counts[name] = len(rows)
    return counts


def hashes(directory):
    return {p.relative_to(directory).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for folder in ("witgen", "testdata") for p in sorted((directory / folder).iterdir())}


def source_hashes():
    paths = subprocess.check_output(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"], cwd=ROOT).split(b"\0")
    return {os.fsdecode(p): hashlib.sha256((ROOT / os.fsdecode(p)).read_bytes()).hexdigest()
            for p in sorted(set(paths)) if p and (ROOT / os.fsdecode(p)).is_file()}


def run(command, log, env=None, cwd=ROOT):
    print(f"Running {' '.join(map(str, command))}; log: {log}", flush=True)
    with log.open("w") as handle:
        result = subprocess.run(command, cwd=cwd, env=env, stdout=handle, stderr=subprocess.STDOUT)
    output = log.read_text()
    require(result.returncode == 0, f"command failed ({result.returncode}); see {log}")
    require(not re.search(r"(?im)\b(warning:|error:|stack overflow|PANIC|segmentation fault)", output),
            f"command emitted a diagnostic; see {log}")
    return output


def export_log_complete(output, testdata):
    """A successful Lean exit alone does not establish that #eval completed."""
    lines = output.splitlines()
    suffix = r": testdata \d+ ms, \d+ rows" if testdata else r": \d+ ms, \d+ bytes"
    total = r"total: 25 chips \(testdata\), \d+ ms" if testdata else r"total: 25 chips, \d+ ms"
    require(len(lines) == len(NAMES) + 1 and
            all(re.fullmatch(re.escape(name) + suffix, line) for name, line in zip(NAMES, lines))
            and re.fullmatch(total, lines[-1]), "incomplete or unexpected Lean export output")


def check_completed(directory):
    directory = directory.resolve()
    counts = validate_generated(directory, source_dumps())
    record = read_json(directory / "provenance.json")
    require(record["sources"] == source_hashes(), "export sources changed; regenerate witnesses")
    require(record["artifacts"] == hashes(directory) and record["rows"] == counts,
            "completed export artifacts changed")
    require(record["deterministic"] is True and record["rustComparison"] is True,
            "export validation did not complete")
    return directory


def generate(out=None):
    dumps = source_dumps()
    errors = check_pins(ROOT)
    require(not errors, "\n".join(errors))
    manifest = read_json(ROOT / "lake-manifest.json")
    clean = next(p for p in manifest["packages"] if p["name"] == "Clean")
    checkout = ROOT / manifest["packagesDir"] / "Clean"
    revision = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(["git", "-C", str(checkout), "status", "--porcelain",
                                     "--untracked-files=no"], text=True)
    require(revision == clean["rev"] and not dirty, "Clean checkout differs from the pinned serializer")
    base = ROOT / ".lake/witgen-export"
    base.mkdir(parents=True, exist_ok=True)
    if out is None:
        out = Path(tempfile.mkdtemp(prefix="run.", dir=base))
    else:
        out = out.resolve()
        require(out.is_relative_to(base.resolve()), f"--out must be under {base}")
        out.mkdir()  # Never mix fresh output with a previous or partial run.
    sources = source_hashes()
    env = dict(os.environ, LEAN_NUM_THREADS=os.environ.get("LEAN_NUM_THREADS", "2"))
    build = run(["lake", "build", "--wfail", "--iofail", "SP1Clean", "SP1CleanTest",
                 "ToClean", "ToMathlib", "ToPolyFun"], out / "build.log", env)
    require("Build completed successfully" in build, f"incomplete dependency build: {out}/build.log")
    command = ["lake", "env", "lean", *flags_for(load_lakefile(ROOT / "lakefile.toml"), "SP1CleanTest"),
               "scripts/witgenExport.lean"]
    repeat = out / "repeat"
    for directory in (out, repeat):
        directory.mkdir(exist_ok=True)
        for testdata in (False, True):
            env.update(WITGEN_EXPORT_OUT=str(directory), WITGEN_ARGS="--testdata" if testdata else "")
            output = run(command, directory / ("fixtures.log" if testdata else "export.log"), env)
            export_log_complete(output, testdata)
        counts = validate_generated(directory, dumps)
    artifact_hashes = hashes(out)
    require(artifact_hashes == hashes(repeat), f"nondeterministic witness export: {out}")
    shutil.rmtree(repeat)  # Retain one complete copy, with its logs and fingerprints.
    env.update(WITGEN_EXPORT_DIR=str(out), CARGO_BUILD_JOBS=os.environ.get("CARGO_BUILD_JOBS", "2"))
    rust = run(["cargo", "test", "--locked", "--release", "--manifest-path",
                "rust/witgen-interp/Cargo.toml", "--", "--nocapture"], out / "rust.log", env)
    require("test all_fixture_rows_reproduce ... ok" in rust and
            all(re.search(rf"(?m)^{re.escape(name)}: {count} rows ok \(", rust)
                for name, count in counts.items()), f"incomplete Rust comparison: {out}/rust.log")
    require(sources == source_hashes(), "sources changed during export; regenerate witnesses")
    (out / "provenance.json").write_text(json.dumps({
        "sourceRevision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "cleanRevision": revision, "sources": sources, "artifacts": artifact_hashes,
        "rows": counts, "deterministic": True, "rustComparison": True,
    }, indent=2) + "\n")
    print(f"PASS: {len(NAMES)} chips, {sum(counts.values())} rows; deterministic Clean export and Rust comparison")
    print(f"Fresh witness artifacts: {out}")
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--source-only", action="store_true")
    mode.add_argument("--check-dir", type=Path)
    mode.add_argument("--out", type=Path, help="new directory under .lake/witgen-export")
    args = parser.parse_args()
    try:
        if args.source_only:
            source_dumps()
            print(f"PASS: {len(NAMES)} independent SP1 dumps match their inventory, dimensions and pin")
        elif args.check_dir:
            print(f"PASS: completed witness export matches current sources: {check_completed(args.check_dir)}")
        else:
            generate(args.out)
    except (ValueError, OSError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"FAIL: {error}\n")


if __name__ == "__main__":
    main()
