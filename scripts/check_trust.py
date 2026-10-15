#!/usr/bin/env python3
"""Enforce the trust policy on built libraries; reports are disposable build artifacts.

Uses the scanner from the immutable PolyFun pin, without modifying or copying it. Build
SP1Clean and the To* libraries before the main scan, and SP1CleanTest before the test scan.
The scanner follows private declarations and transitive dependencies, including axiom types
and mutual families. Source guards separately cover anonymous examples and unused defaults.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
POLICY = ROOT / "scripts/trust_policy.json"
MAIN_ROOTS = ["SP1Clean", "ToClean", "ToMathlib", "ToPolyFun"]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
SCANNER = Path("scripts/PolyFunAxiomSweep.lean")
NATIVE = re.compile(r"^(.+)\._native\.(native_decide|bv_decide)$")


def string_set(value: object, label: str) -> set[str]:
    if not isinstance(value, list) or not value or any(
        not isinstance(x, str) or not x or any(c.isspace() for c in x) for x in value
    ):
        raise ValueError(f"{label}: expected a nonempty list of names")
    if len(set(value)) != len(value):
        raise ValueError(f"{label}: duplicate names")
    return set(value)


def load_policy(path: Path = POLICY) -> dict:
    policy = json.loads(path.read_text())
    expected = {"version", "standard", "sail", "bvDecide", "testNativeTactics"}
    if not isinstance(policy, dict) or set(policy) != expected or policy["version"] != 1:
        raise ValueError("unsupported trust policy schema")
    if string_set(policy["standard"], "standard") != STANDARD:
        raise ValueError("standard must be exactly Lean's three logical axioms")
    for key in ("sail", "bvDecide"):
        group = policy[key]
        if not isinstance(group, dict) or set(group) != {"reason", "names"}:
            raise ValueError(f"{key}: expected reason and names")
        if not isinstance(group["reason"], str) or not group["reason"].strip():
            raise ValueError(f"{key}: missing explanation")
        names = string_set(group["names"], key)
        if names & (STANDARD | {"sorryAx", "Lean.trustCompiler", "Lean.ofReduceBool"}):
            raise ValueError(f"{key}: forbidden exception")
        if key == "sail" and any(not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", n) for n in names):
            raise ValueError("sail: expected exact generated interface names")
        if key == "bvDecide" and any(
            not NATIVE.fullmatch(n) or not n.endswith("._native.bv_decide") for n in names
        ):
            raise ValueError("bvDecide: expected exact normalized proof owners")
    if string_set(policy["testNativeTactics"], "testNativeTactics") != {"native_decide", "bv_decide"}:
        raise ValueError("testNativeTactics must be native_decide and bv_decide")
    return policy


def classify(axiom: str, scope: str, policy: dict) -> str:
    if axiom == "sorryAx":
        return "forbidden"
    if axiom in policy["standard"]:
        return "logical"
    if axiom in policy["sail"]["names"]:
        return "sail"
    if axiom in policy["bvDecide"]["names"]:
        return "approved-bv"
    native = NATIVE.fullmatch(axiom)
    if scope == "test" and native and native[2] in policy["testNativeTactics"]:
        return "test-native"
    return "forbidden"


def modules_below(root: str) -> list[str]:
    files = sorted((ROOT / root).rglob("*.lean"))
    if (ROOT / (root + ".lean")).is_file():
        files.append(ROOT / (root + ".lean"))
    return sorted(".".join(p.relative_to(ROOT).with_suffix("").parts) for p in files)


def scope_modules(scope: str) -> tuple[list[str], list[str]]:
    modules = sorted({m for root in (MAIN_ROOTS if scope == "main" else ["SP1CleanTest"])
                      for m in modules_below(root)})
    if not modules:
        raise ValueError(f"{scope}: empty source module inventory")
    # The tests are glob libraries without an umbrella; import every discovered module.
    return (MAIN_ROOTS if scope == "main" else modules), modules


def validate_report(report: dict, roots: list[str], modules: list[str], output: str) -> list[dict]:
    if not isinstance(report, dict) or report.get("roots") != roots:
        raise ValueError("scanner root inventory mismatch")
    entries = report.get("declarations")
    if not isinstance(entries, list) or not entries or report.get("declarationCount") != len(entries):
        raise ValueError("scanner returned an empty or inconsistent declaration inventory")
    # PolyFun's JSON lacks a module inventory. Its independently computed module count,
    # together with root-index completeness and explicit test imports, closes this check.
    counts = re.findall(r"^axiomsweep: (\d+) declarations across (\d+) modules under ", output, re.M)
    if counts != [(str(len(entries)), str(len(modules)))]:
        raise ValueError("scanner module coverage differs from the source inventory")
    seen = set()
    for entry in entries:
        if not isinstance(entry, dict) or not isinstance(entry.get("name"), str) or not entry["name"]:
            raise ValueError("malformed scanner declaration")
        if entry["name"] in seen or entry.get("module") not in modules:
            raise ValueError("duplicate declaration or unexpected owning module")
        seen.add(entry["name"])
        axioms = entry.get("axioms")
        if not isinstance(axioms, list) or any(not isinstance(a, str) or not a for a in axioms):
            raise ValueError("malformed scanner axiom list")
    return entries


def evaluate(entries: list[dict], scope: str, policy: dict) -> tuple[dict, list[dict]]:
    classes: dict[str, set[str]] = {}
    violations = []
    for entry in entries:
        for axiom in entry["axioms"]:
            category = classify(axiom, scope, policy)
            classes.setdefault(category, set()).add(axiom)
            if category == "forbidden":
                violations.append({"declaration": entry["name"], "module": entry["module"], "axiom": axiom})
    return {k: sorted(v) for k, v in sorted(classes.items())}, violations


def command(args: list[str], **kwargs) -> subprocess.CompletedProcess:
    return subprocess.run(args, cwd=ROOT, text=True, capture_output=True, check=True, **kwargs)


def scanner_path() -> Path:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    pin = next(p["rev"] for p in manifest["packages"] if p["name"] == "PolyFun")
    package = ROOT / ".lake/packages/PolyFun"
    head = command(["git", "-C", str(package), "rev-parse", "HEAD"]).stdout.strip()
    pinned = command(["git", "-C", str(package), "show", f"{pin}:{SCANNER}"]).stdout
    path = package / SCANNER
    if head != pin or path.read_text() != pinned:
        raise ValueError("PolyFun scanner differs from the immutable dependency pin")
    return path


def metadata(scope: str, policy_path: Path) -> dict:
    return {
        "scope": scope,
        "revision": command(["git", "rev-parse", "HEAD"]).stdout.strip(),
        "trackedChanges": bool(command(["git", "status", "--porcelain", "--untracked-files=no"]).stdout),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "dependencies": json.loads((ROOT / "lake-manifest.json").read_text())["packages"],
        "policySha256": hashlib.sha256(policy_path.read_bytes()).hexdigest(),
    }


def scan(scope: str, policy: dict, policy_path: Path, report_dir: Path) -> int:
    report_dir.mkdir(parents=True, exist_ok=True)
    destination = report_dir / f"{scope}.json"
    result = {"status": "error", "metadata": {"scope": scope}}
    try:
        result["metadata"] = metadata(scope, policy_path)
        roots, modules = scope_modules(scope)
        scanner = scanner_path()
        if scope == "main":
            command(["scripts/check_root_index.sh"])
        with tempfile.TemporaryDirectory(prefix=f"{scope}-", dir=report_dir) as temporary:
            raw = Path(temporary) / "scanner.json"
            args = ["lake", "env", "lean", "--run", str(scanner)]
            for root in roots:
                args.extend(["--root", root])
            run = subprocess.run(args + ["--out", str(raw)], cwd=ROOT, text=True, capture_output=True)
            (report_dir / f"{scope}-scanner.log").write_text(run.stdout + run.stderr)
            if run.returncode != 0:
                raise ValueError(f"scanner exited {run.returncode}; see {scope}-scanner.log")
            entries = validate_report(json.loads(raw.read_text()), roots, modules, run.stdout)
        classes, violations = evaluate(entries, scope, policy)
        result.update(status="fail" if violations else "pass", roots=roots, modules=modules,
                      declarationCount=len(entries), classes=classes, violations=violations, declarations=entries)
        print(f"trust ({scope}): {len(entries)} declarations / {len(modules)} modules; "
              f"{len(violations)} forbidden dependencies")
        for axiom, count in sorted(Counter(v["axiom"] for v in violations).items()):
            example = next(v for v in violations if v["axiom"] == axiom)
            print(f"  FORBIDDEN {axiom}: {count} declarations, including {example['declaration']}")
        return 1 if violations else 0
    except (OSError, ValueError, KeyError, StopIteration, subprocess.CalledProcessError) as error:
        result["error"] = str(error)
        print(f"trust ({scope}): ERROR: {error}", file=sys.stderr)
        return 2
    finally:
        destination.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
        print(f"  report: {destination.relative_to(ROOT) if destination.is_relative_to(ROOT) else destination}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scope", choices=["main", "test", "all"], default="all")
    parser.add_argument("--report-dir", type=Path, default=ROOT / ".lake/build/trust")
    parser.add_argument("--validate-policy-only", action="store_true")
    args = parser.parse_args()
    try:
        policy = load_policy()
    except (OSError, ValueError) as error:
        print(f"trust policy: ERROR: {error}", file=sys.stderr)
        return 2
    if args.validate_policy_only:
        print("PASS: trust policy schema and fixed logical baseline")
        return 0
    scopes = ["main", "test"] if args.scope == "all" else [args.scope]
    return max(scan(s, policy, POLICY, args.report_dir.resolve()) for s in scopes)


if __name__ == "__main__":
    sys.exit(main())
