#!/usr/bin/env python3
"""Run the library examples and reject incomplete or mismatching Lean output."""

from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys

import check_pins

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = {
    "add": ("SP1CleanTest.Alignment.Examples.AddEnsemble", "scripts/examples/Add.lean"),
    "branch": ("SP1CleanTest.Alignment.Audit.BranchEnsembleRoundTrip", "scripts/examples/Branch.lean"),
    "loadbyte": ("SP1CleanTest.Alignment.Examples.LoadByteStatic", "scripts/examples/LoadByte.lean"),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def validate_report(name, result, revision, dirty):
    """Expectations are independent of the values emitted by the Lean runner."""
    require(result.returncode == 0 and not result.stderr, "Lean failed or emitted diagnostics")
    report = json.loads(result.stdout)
    if name == "add":
        identifiers = ["active-add", "missing-ram-validator", "duplicate-ram-validator",
                       "wrong-final-record-clock", "missing-unchanged-register-validators",
                       "changed-untouched-x31", "changed-untouched-ram", "missing-bank-terminal",
                       "empty-identity"]
        values = [True] + [False] * 7 + [True]
        require(report["table_count"] == 93, "ADD inventory mismatch")
    elif name == "branch":
        identifiers = ["active-branch", "wrong-public-next-pc", "missing-authentication-row",
                       "duplicate-authentication-row", "changed-untouched-register", "empty-identity",
                       "malformed-seed-index", "malformed-seed-length"]
        values = [True, False, False, False, False, True, False, False]
        expected = {"instruction": "BEQ x1,x2,+4092", "instructionWord": 0x7e208ee3,
                    "sourcePc": 65536, "targetPc": 69628, "sourceClock": 1, "targetClock": 9,
                    "tableCount": 93, "uniqueChannels": 29, "registeredChannelOccurrences": 269,
                    "verifierInteractions": 19 + 2 * 8 + (2 + 2 + 2 + 1) + 2 * 2}
        require(all(report[key] == value for key, value in expected.items()), "branch metadata mismatch")
        require(report["tableCount"] == len(report["tables"]) and
                report["tableRows"] == sum(table["rows"] for table in report["tables"]) and
                report["interactions"] == report["physicalInteractions"] + report["verifierInteractions"],
                "branch physical-row or ledger accounting mismatch")
    else:
        identifiers = [f"{op}/offset-{offset}/byte-{value}" for op in ["LB", "LBU"]
                       for offset in range(8) for value in [0, 127, 128, 255]]
        identifiers += ["inactive-byte-300", "same-key-reader-demand", "wrong-low-byte",
                        "wrong-selectors", "active-out-of-range"]
        values = [True] * 66 + [False] * 3
        require(report["oldByteBalanced"] is True and report["newByteBalanced"] is True,
                "LoadByte provider balance mismatch")
        expected = {"fixedTableRows": 256, "activeRows": 64, "inactiveRows": 1,
                    "oldDedicatedProviderRows": 65, "newDedicatedProviderRows": 0}
        require(all(report[key] == value for key, value in expected.items()), "LoadByte inventory mismatch")
        require(all(case["passed"] is True for case in report["cases"]), "LoadByte case failed")
    require([case["id"] for case in report["cases"]] == identifiers,
            "missing, extra or reordered regression cases")
    for case, expected in zip(report["cases"], values):
        require(case["expected"] is expected and case["actual"] is expected,
                f"regression mismatch: {case['id']}")
    if name != "loadbyte":
        require(report["revision"] == revision and report["dirty"] is dirty,
                "revision or working-tree status mismatch")
        require(report["assembly"] == "SP1Clean.Soundness.HostFinalMemory.ensemble",
                "wrong assembly")
    return report


def source_digest():
    paths = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd=ROOT).split(b"\0")
    digest = hashlib.sha256()
    for name in sorted(set(paths) - {b""}):
        path = ROOT / os.fsdecode(name)
        digest.update(name + b"\0")
        if path.is_symlink():
            digest.update(b"link\0" + os.fsencode(os.readlink(path)))
        elif path.is_file():
            digest.update(str(path.stat().st_mode & 0o777).encode() + b"\0" + path.read_bytes())
        else:
            digest.update(b"<missing>")
        digest.update(b"\0")
    return digest.hexdigest()


def execute(names):
    out = ROOT / ".lake/build/examples"
    out.mkdir(parents=True, exist_ok=True)
    for name in ("results.json", "commands.log", "provenance.json"):
        (out / name).unlink(missing_ok=True)
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", "2")
    provenance = {"status": "started", "examples": names,
                  "startedUtc": datetime.now(timezone.utc).isoformat(),
                  "cacheNote": "Uses prepared dependencies and available oleans; no cold-build claim."}
    (out / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")

    def run(command):
        with (out / "commands.log").open("a") as log:
            log.write(f"$ {shlex.join(command)}\n")
        result = subprocess.run(command, cwd=ROOT, env=env, text=True, capture_output=True)
        with (out / "commands.log").open("a") as log:
            log.write(f"{result.stdout}{result.stderr}\n[exit {result.returncode}]\n")
        require(result.returncode == 0, f"{shlex.join(command)} failed; see {out}/commands.log")
        return result

    def git(*args):
        return run(["git", *args]).stdout.strip()

    try:
        require(not (errors := check_pins.check(ROOT)), "\n".join(errors))
        toolchain = (ROOT / "lean-toolchain").read_text().strip()
        run(["elan", "run", toolchain, "lean", "--version"])
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        for package in manifest["packages"]:
            directory = ROOT / manifest["packagesDir"] / package["name"]
            require((directory / ".git").exists(), f"prepare the pinned {package['name']} checkout")
            require(git("-C", str(directory), "rev-parse", "HEAD") == package["rev"],
                    f"{package['name']}: checkout differs from the resolved pin")
            require(not git("-C", str(directory), "status", "--porcelain", "--untracked-files=no"),
                    f"{package['name']}: tracked dependency edits")
        revision = git("rev-parse", "HEAD")
        dirty = bool(git("status", "--porcelain", "--untracked-files=normal"))
        before = source_digest()
        provenance.update(revision=revision, dirty=dirty, workingSourceSha256=before,
                          toolchain=toolchain, dependencies=manifest["packages"],
                          ci={key: env.get(key) for key in ("GITHUB_SHA", "GITHUB_RUN_ID",
                              "GITHUB_RUN_ATTEMPT", "GITHUB_REPOSITORY", "SP1_PR_HEAD")})
        (out / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
        env.update(SP1_EXAMPLE_REVISION=revision, SP1_EXAMPLE_STATUS="dirty" if dirty else "clean")
        run(["elan", "run", toolchain, "lake", "--no-cache", "build", "--wfail", "--iofail",
             *(EXAMPLES[name][0] for name in names)])
        reports = {}
        for name in names:
            result = run(["elan", "run", toolchain, "lake", "env", "lean", EXAMPLES[name][1]])
            reports[name] = validate_report(name, result, revision, dirty)
        require(source_digest() == before and git("rev-parse", "HEAD") == revision,
                "sources changed during the run; repeat on a stable checkout")
        (out / "results.json").write_text(json.dumps(reports, indent=2) + "\n")
        provenance["status"] = "passed"
        return reports
    except Exception as error:
        provenance.update(status="failed", error=str(error))
        raise
    finally:
        (out / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("examples", nargs="*", metavar="EXAMPLE", help="add, branch, loadbyte (default: all)")
    parser.add_argument("--json", action="store_true", help="emit only checked reports on stdout")
    args = parser.parse_args()
    names = args.examples or list(EXAMPLES)
    if len(set(names)) != len(names) or any(name not in EXAMPLES for name in names):
        parser.error("choose distinct examples from add, branch, loadbyte")
    try:
        reports = execute(names)
        if args.json:
            print(json.dumps(reports, indent=2))
        else:
            for name, report in reports.items():
                print(f"PASS {name}: {len(report['cases'])} cases")
            print("Reports and provenance: .lake/build/examples/")
        return 0
    except Exception as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
