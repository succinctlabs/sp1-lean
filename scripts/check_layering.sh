#!/usr/bin/env bash
# Gate: the layering contract in docs/layering.md.
#
# Two checks over one stratum map (scripts/layering.txt):
#
#   1. DIRECTION — a module may import only from a strictly lower stratum, or its own. An upward
#      import is a bug. This is the check that would have caught
#      `Proofs/Completeness/Closure.lean` importing `Faithful/Transport/Table`: the only
#      Proofs -> Faithful edge in the tree, against 30 going the other way, which compiled and passed
#      every other gate.
#
#   2. NAMESPACE AGREEMENT — a file's first `namespace SP1Clean.<Root>` must name the pillar its
#      stratum expects. Nearly free, and high-signal: `Faithful/ExtractedInteractionModel.lean`
#      declares `namespace SP1Clean.Extracted`, i.e. the source recorded the file's correct home and
#      nothing checked. AGENTS.md's "namespaces are decoupled from directory paths" stays true for
#      SUB-namespaces; the pillar root is what must agree.
#
# Both fail closed: a module matching no stratum prefix is an error, so a new top-level directory
# cannot silently escape the map.
#
# Exceptions live in scripts/layering_allowlist.txt with a stated reason. That is a prohibition with
# a bar, not a ratchet — see AGENTS.md on scripts/option_escapes_allowlist.txt.
#
# Run from the repo root. Part of scripts/run_audit.sh and the CI `guards` job. Exit 0 = contract holds.
set -uo pipefail

cd "$(dirname "$0")/.." || exit 1

python3 - <<'PYEOF'
import os, re, sys, fnmatch

MAP = "scripts/layering.txt"
ALLOW = "scripts/layering_allowlist.txt"

# ---- the stratum map -------------------------------------------------------
strata = []          # (prefix, level, pillar)
for raw in open(MAP, encoding="utf-8"):
    line = raw.split("#", 1)[0].strip()
    if not line:
        continue
    parts = line.split()
    if len(parts) != 3:
        print(f"FAIL: {MAP}: expected '<stratum> <pillar> <prefix>', got: {raw.rstrip()}")
        sys.exit(1)
    level, pillar, prefix = parts
    strata.append((prefix, int(level), pillar))
# Longest prefix wins, so a straddling directory is fixed by a more specific line.
strata.sort(key=lambda e: -len(e[0]))

def classify(path):
    # A rule matches by prefix, or as a glob when it contains '*'. Rules are tried most-specific
    # first (longest pattern), so a straddling directory is fixed by adding a narrower rule rather
    # than by an allowlist entry.
    for prefix, level, pillar in strata:
        if "*" in prefix:
            if fnmatch.fnmatch(path, prefix):
                return level, pillar, prefix
        elif path.startswith(prefix):
            return level, pillar, prefix
    return None, None, None

# ---- the allowlist --------------------------------------------------------
allowed_edges, allowed_ns = set(), set()
if os.path.exists(ALLOW):
    for raw in open(ALLOW, encoding="utf-8"):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        kind, rest = line.split(None, 1)
        if kind == "import":
            src, dst = rest.split()
            allowed_edges.add((src, dst))
        elif kind == "namespace":
            allowed_ns.add(rest.strip())
        else:
            print(f"FAIL: {ALLOW}: unknown entry kind {kind!r}")
            sys.exit(1)

# ---- walk the hand-written trees ------------------------------------------
def module_to_path(mod):
    return mod.replace(".", "/") + ".lean"

files = []
for root in ("SP1Clean", "ToClean", "ToMathlib"):
    for dp, _, fs in os.walk(root):
        for f in fs:
            if f.endswith(".lean"):
                files.append(os.path.join(dp, f))
for extra in ("SP1Clean.lean", "ToClean.lean", "ToMathlib.lean"):
    if os.path.exists(extra):
        files.append(extra)
files.sort()

fail = 0
unmapped, upward, nsbad = [], [], []

# Root index modules import the whole world by design; they are the umbrella, not a layer.
ROOT_INDEX = {"SP1Clean.lean", "ToClean.lean", "ToMathlib.lean"}

for path in files:
    if path in ROOT_INDEX:
        continue
    level, pillar, _ = classify(path)
    if level is None:
        unmapped.append(path)
        continue

    src_lines, ns_root = [], None
    for line in open(path, encoding="utf-8", errors="replace"):
        s = line.strip()
        if s.startswith("import "):
            src_lines.append(s.split()[1])
            continue
        m = re.match(r"^namespace\s+SP1Clean\.([A-Za-z0-9_]+)", line)
        if m and ns_root is None:
            ns_root = m.group(1)

    # 1. direction
    for mod in src_lines:
        if not mod.startswith(("SP1Clean", "ToClean", "ToMathlib")):
            continue          # Mathlib / Clean / Std / Sail are all below everything
        target = module_to_path(mod)
        if not os.path.exists(target):
            continue          # check_root_index.sh owns dangling-import detection
        tlevel, _, _ = classify(target)
        if tlevel is None:
            unmapped.append(target)
            continue
        if tlevel > level and (path, target) not in allowed_edges:
            upward.append((path, level, target, tlevel))

    # 2. namespace agreement
    PILLARS = {"Math", "Model", "Extracted", "FormalModel", "Native", "Proofs", "Faithful",
               "Soundness", "Composition"}
    if pillar != "-" and ns_root in PILLARS and ns_root != pillar and path not in allowed_ns:
        nsbad.append((path, ns_root, pillar))

if unmapped:
    fail = 1
    print(f"FAIL: {len(set(unmapped))} module(s) match no stratum prefix in {MAP}:")
    for p in sorted(set(unmapped))[:20]:
        print(f"  {p}")
    print("  (add a line to the map — a new directory must not default into a layer)")

if upward:
    fail = 1
    print(f"FAIL: {len(upward)} upward import(s) — a module may import only strictly lower strata:")
    for src, sl, dst, dl in sorted(upward):
        print(f"  {src} (stratum {sl})")
        print(f"    imports {dst} (stratum {dl})")

if nsbad:
    fail = 1
    print(f"FAIL: {len(nsbad)} file(s) whose namespace pillar disagrees with their path:")
    for p, got, want in sorted(nsbad):
        print(f"  {p}: declares SP1Clean.{got}, path stratum expects {want}")
    print("  (one of the two is wrong — usually the path; the namespace is the author's intent)")

if fail == 0:
    print(f"check_layering: PASS ({len(files)} modules, {len(strata)} stratum rules, "
          f"{len(allowed_edges)} import + {len(allowed_ns)} namespace exception(s))")
sys.exit(fail)
PYEOF
