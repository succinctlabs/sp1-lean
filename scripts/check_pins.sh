#!/usr/bin/env bash
# Gate: every recorded pin value must match reality. Cross-checks, in order:
#   1. `lakefile.toml` `[[require]]` revs against `lake-manifest.json` (resolved graph);
#   2. the pin table in `docs/release-audit.md` against the manifest + `lean-toolchain`;
#   3. the SP1 semantic revision quoted in README/report against the single authoritative
#      source, `SP1Clean.FormalModel.CoreProfile.sp1SemanticRevision` (itself `rfl`-checked
#      against the extracted provenance);
#   4. the census declaration count cited in docs against `scripts/axiom_probe.lean`.
#
# This is the gate whose absence let a wrong recorded PolyFun pin survive the 2026-08
# migration: `check_report_citations.sh` validates that cited paths resolve, not that
# recorded pin VALUES match the build graph. Run from anywhere; part of
# `scripts/run_audit.sh` and the CI `guards` job. Exit 0 = all recorded values match.
set -uo pipefail
cd "$(dirname "$0")/.."

python3 - <<'EOF'
import json, re, sys

fail = 0
def err(msg):
    global fail
    print(f"FAIL: {msg}")
    fail = 1

# -- 1. lakefile.toml requires vs lake-manifest.json ------------------------------------
lakefile = open("lakefile.toml").read()
requires = {}  # name -> rev as written in lakefile
for block in re.split(r"\[\[require\]\]", lakefile)[1:]:
    # a require block ends at the next [[...]] table header
    body = re.split(r"\n\[\[", block)[0]
    name = re.search(r'^name = "([^"]+)"', body, re.M)
    rev = re.search(r'^rev = "([^"]+)"', body, re.M)
    if name and rev:
        requires[name.group(1)] = rev.group(1)

manifest = {p["name"]: p for p in json.load(open("lake-manifest.json"))["packages"]}

for name, rev in requires.items():
    if name not in manifest:
        err(f"lakefile requires '{name}' but lake-manifest.json has no such package")
        continue
    entry = manifest[name]
    if re.fullmatch(r"[0-9a-f]{40}", rev):
        if entry.get("rev") != rev:
            err(f"{name}: lakefile rev {rev} != manifest rev {entry.get('rev')}")
    else:  # tag or branch pin: the manifest records it as inputRev
        if entry.get("inputRev") != rev:
            err(f"{name}: lakefile rev '{rev}' != manifest inputRev '{entry.get('inputRev')}'")
for name, entry in manifest.items():
    # Transitive dependencies (mathlib's own graph) are marked inherited; only direct
    # packages must have a matching [[require]].
    if not entry.get("inherited", False) and name not in requires:
        err(f"lake-manifest.json direct package '{name}' has no [[require]] in lakefile.toml")

# -- 2. docs/release-audit.md pin table vs the resolved graph ---------------------------
audit = open("docs/release-audit.md").read()
def table_value(row_label):
    m = re.search(rf"^\| {re.escape(row_label)} \| `([^`]+)`", audit, re.M)
    return m.group(1) if m else None

toolchain = open("lean-toolchain").read().strip()
core_profile = open("SP1Clean/FormalModel/CoreProfile.lean").read()
semantic = re.search(r'def sp1SemanticRevision : String := "([0-9a-f]{40})"', core_profile)
if not semantic:
    err("sp1SemanticRevision not found in SP1Clean/FormalModel/CoreProfile.lean")
    sys.exit(1)
semantic = semantic.group(1)

expected_rows = {
    "Lean toolchain": toolchain,
    "SP1 semantic source": semantic,
    "mathlib pin": manifest.get("mathlib", {}).get("rev"),
    "Clean pin": manifest.get("Clean", {}).get("rev"),
    "Lean_RV64D pin": manifest.get("Lean_RV64D", {}).get("rev"),
    "RISCV pin": manifest.get("RISCV", {}).get("rev"),
    "lean-sail pin": manifest.get("Sail", {}).get("rev"),
    "PolyFun pin": manifest.get("PolyFun", {}).get("rev"),
}
for label, expected in expected_rows.items():
    recorded = table_value(label)
    if recorded is None:
        err(f"docs/release-audit.md pin table has no row '| {label} |'")
    elif recorded != expected:
        err(f"docs/release-audit.md row '{label}' records `{recorded}` but the source of truth is `{expected}`")

# -- 3. the semantic hash quoted outside the table --------------------------------------
for path in ("README.md", "docs/verification-report.md", "docs/overview.md"):
    text = open(path).read()
    for quoted in set(re.findall(r"`([0-9a-f]{40})`", text)):
        # Any bare 40-hex quote in the reader docs must be a pin this script knows about.
        known = {semantic, *(e for e in expected_rows.values() if e and re.fullmatch(r"[0-9a-f]{40}", e))}
        known |= {p.get("rev") for p in manifest.values()}
        known |= set(re.findall(r"\| [^|]+ \| `([0-9a-f]{40})`", audit))  # e.g. extractor overlay
        if quoted not in known:
            err(f"{path} quotes commit `{quoted}` which matches no recorded pin")

# -- 4. census declaration count cited in docs vs the generated probe -------------------
probe_count = sum(1 for line in open("scripts/axiom_probe.lean")
                  if line.startswith("#print axioms "))
for path, pattern in (("README.md", r"(\d+)-declaration"),
                      ("docs/snapshots/axiom-ledger.md", r"(\d+) released declarations are probed")):
    text = open(path).read()
    for m in re.finditer(pattern, text):
        if int(m.group(1)) != probe_count:
            err(f"{path} cites a {m.group(1)}-declaration census; scripts/axiom_probe.lean has {probe_count} probes")

if fail == 0:
    print(f"PASS: lakefile/manifest/audit-table/toolchain pins agree; census count {probe_count} matches cited values")
sys.exit(fail)
EOF
