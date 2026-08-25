#!/usr/bin/env bash
# Gate: every recorded pin value must match reality. Cross-checks, in order:
#   1. `lakefile.toml` `[[require]]` revs against `lake-manifest.json` (resolved graph);
#   2. the pin table in `docs/release-audit.md` against the manifest + `lean-toolchain`;
#  2b. the Sail generation pins + config hash in `scripts/sail-config/` against that same
#      table (they are generator inputs, so the build graph does not constrain them);
#   3. the SP1 semantic revision quoted in README/report against the single authoritative
#      source, `SP1Clean.FormalModel.CoreProfile.sp1SemanticRevision` (itself `rfl`-checked
#      against the extracted provenance);
#   4. the authoritative census ledger and committed raw snapshots against the
#      generated probes (`scripts/axiom_probe.lean` + `scripts/axiom_probe_test.lean`).
#
# This is the gate whose absence let a wrong recorded PolyFun pin survive the 2026-08
# migration: `check_report_citations.sh` validates that cited paths resolve, not that
# recorded pin VALUES match the build graph. Run from anywhere; part of
# `scripts/run_audit.sh` and the CI `guards` job. Exit 0 = all recorded values match.
set -uo pipefail
cd "$(dirname "$0")/.."

allow_census_snapshot_drift=0
if [ "${1:-}" = "--census-update" ]; then
  allow_census_snapshot_drift=1
  shift
fi
if [ "$#" -ne 0 ]; then
  echo "usage: scripts/check_pins.sh [--census-update]" >&2
  exit 2
fi

python3 - "$allow_census_snapshot_drift" <<'EOF'
import hashlib, json, re, sys

fail = 0
allow_census_snapshot_drift = sys.argv[1] == "1"
census_update_pending = False
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

# AGENTS.md is the operational authority agents load before touching the dependency graph.  A stale
# fork revision there is more dangerous than stale prose because it can directly steer a future pin
# update, so gate it against the same resolved Clean revision.
agents = open("AGENTS.md").read()
agents_clean = re.search(
    r"Clean pin is currently a fork.*?\(`([0-9a-f]{40})`\)", agents, re.S)
if not agents_clean:
    err("AGENTS.md does not record the current Clean fork revision as a full 40-hex commit")
elif agents_clean.group(1) != expected_rows["Clean pin"]:
    err(f"AGENTS.md records Clean fork `{agents_clean.group(1)}` but the resolved pin is "
        f"`{expected_rows['Clean pin']}`")

# -- 2b. the Sail generation pins, which live in a script rather than the build graph ----
# `SAIL_SHA` / `SAIL_RISCV_SHA` / the config hash are inputs to the GENERATED `Lean_RV64D`
# snapshot, so nothing in the manifest constrains them: without this check all three can
# drift from the table with the build fully green.
gen = open("scripts/sail-config/generate_lean_rv64d.sh").read()
def script_pin(name):
    m = re.search(rf"^{name}=([0-9a-f]{{40}})\b", gen, re.M)
    if not m:
        err(f"scripts/sail-config/generate_lean_rv64d.sh has no {name}=<40-hex> constant")
        return None
    return m.group(1)

for label, value in (("Sail compiler source", script_pin("SAIL_SHA")),
                     ("sail-riscv model source", script_pin("SAIL_RISCV_SHA"))):
    if value is None:
        continue
    recorded = table_value(label)
    if recorded is None:
        err(f"docs/release-audit.md pin table has no row '| {label} |'")
    elif recorded != value:
        err(f"docs/release-audit.md row '{label}' records `{recorded}` but "
            f"generate_lean_rv64d.sh pins `{value}`")

cfg_path = "scripts/sail-config/sp1_rv64d_cfg.json"
cfg_sha = hashlib.sha256(open(cfg_path, "rb").read()).hexdigest()
m = re.search(r"^\| SP1 Sail config \| sha256 `([0-9a-f]{64})`", audit, re.M)
if not m:
    err("docs/release-audit.md pin table has no row '| SP1 Sail config | sha256 `<64-hex>`'")
elif m.group(1) != cfg_sha:
    err(f"docs/release-audit.md records SP1 Sail config sha256 `{m.group(1)}` "
        f"but {cfg_path} hashes to `{cfg_sha}`")

# -- 3. the semantic hash quoted outside the table --------------------------------------
for path in ("README.md", "docs/verification-report.md", "docs/overview.md"):
    text = open(path).read()
    for quoted in set(re.findall(r"`([0-9a-f]{40})`", text)):
        # Any bare 40-hex quote in the reader docs must be a pin this script knows about.
        known = {semantic, *(e for e in expected_rows.values() if e and re.fullmatch(r"[0-9a-f]{40}", e))}
        known |= {p.get("rev") for p in manifest.values()}
        known |= set(re.findall(r"\| [^|]+ \| `([0-9a-f]{40})`", audit))  # e.g. extraction branch
        if quoted not in known:
            err(f"{path} quotes commit `{quoted}` which matches no recorded pin")

# -- 3b. the committed SP1 trace dumps vs the extraction pin ----------------------------
# `export/sp1dump/index.json` records the sp1 commit its dumps were generated at
# (`scripts/update_sp1_dumps.sh` is the sole writer); it must be the same extraction
# pin `update_extracted.py` enforces, or the dumps and the extracted AIR describe
# different Rust trees.
pinned = re.search(r'SP1_PINNED_COMMIT = "([0-9a-f]{40})"', open("update_extracted.py").read())
if not pinned:
    err("SP1_PINNED_COMMIT not found in update_extracted.py")
else:
    dump_index = json.load(open("export/sp1dump/index.json"))
    if dump_index.get("sp1Commit") != pinned.group(1):
        err(f"export/sp1dump/index.json sp1Commit {dump_index.get('sp1Commit')} != "
            f"update_extracted.py SP1_PINNED_COMMIT {pinned.group(1)}")

# -- 4. authoritative census ledger + raw snapshots vs generated probes ----------------
# Numeric census claims live in one place: docs/snapshots/axiom-ledger.md. Reader docs link
# there instead of copying a count that can drift. Gate the main/test split independently,
# the ledger total, and the number of entries in each committed raw snapshot.
scopes = {
    "main": ("scripts/axiom_probe.lean", "docs/snapshots/axiom-census.txt"),
    "test": ("scripts/axiom_probe_test.lean", "docs/snapshots/axiom-census-test.txt"),
}
probe_counts = {}
for scope, (probe, snapshot) in scopes.items():
    probe_counts[scope] = sum(1 for line in open(probe)
                              if line.startswith("#print axioms "))
    snapshot_count = sum(1 for line in open(snapshot) if line.startswith("'"))
    if snapshot_count != probe_counts[scope]:
        census_update_pending = True
        message = (f"{snapshot} has {snapshot_count} entries but {probe} has "
                   f"{probe_counts[scope]} probes")
        if allow_census_snapshot_drift:
            print(f"UPDATE-PENDING: {message}")
        else:
            err(message)

ledger_path = "docs/snapshots/axiom-ledger.md"
ledger = open(ledger_path).read()
ledger_patterns = {
    "main": (r"\[`axiom-census\.txt`\]\(axiom-census\.txt\).*?"
             r"`SP1Clean` library,\s*(\d+) declarations"),
    "test": (r"\[`axiom-census-test\.txt`\]\(axiom-census-test\.txt\).*?"
             r"(\d+) declarations"),
}
for scope, pattern in ledger_patterns.items():
    match = re.search(pattern, ledger, re.S)
    if not match:
        err(f"{ledger_path} does not state the authoritative {scope} census count")
    elif int(match.group(1)) != probe_counts[scope]:
        err(f"{ledger_path} cites {match.group(1)} {scope} declarations; "
            f"{scopes[scope][0]} has {probe_counts[scope]} probes")

probe_count = sum(probe_counts.values())
total = re.search(r"(\d+) released declarations are probed", ledger)
if not total:
    err(f"{ledger_path} does not state the authoritative total census count")
elif int(total.group(1)) != probe_count:
    err(f"{ledger_path} cites {total.group(1)} released declarations; "
        f"the generated probes contain {probe_count}")

if fail == 0:
    if census_update_pending:
        print(f"PASS: pins and census ledger match {probe_count} generated probes; "
              "raw census restamp remains update-pending")
    else:
        print(f"PASS: pins agree; census ledger and raw snapshots match "
              f"{probe_count} generated probes")
sys.exit(fail)
EOF
