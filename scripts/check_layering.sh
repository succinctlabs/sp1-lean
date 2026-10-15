#!/usr/bin/env bash
# Gate: the layering contract in docs/layering.md.
#
# Import, namespace and root-index checks over one stratum map (scripts/layering.txt):
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
#   3. CORE INDEX — `SP1Clean/Core.lean` (the `SP1Core` library root, i.e. the PR-CI build) imports
#      exactly the hand-written modules of strata 0-6. The core set is derived from the map, never
#      listed by hand a second time; a module missing from the index silently drops out of PR CI.
#
# All fail closed: a module matching no stratum prefix is an error, so a new top-level directory
# cannot silently escape the map.
# Native circuits additionally have no transitive dependency on legacy Rust extraction.
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
for root in ("SP1Clean", "ToClean", "ToMathlib", "ToPolyFun"):
    for dp, _, fs in os.walk(root):
        for f in fs:
            if f.endswith(".lean"):
                files.append(os.path.join(dp, f))
for extra in ("SP1Clean.lean", "ToClean.lean", "ToMathlib.lean", "ToPolyFun.lean"):
    if os.path.exists(extra):
        files.append(extra)
files.sort()

fail = 0
unmapped, upward, nsbad = [], [], []
imports_by_file = {}

# Root index modules import the whole world by design; they are the umbrella, not a layer.
# `SP1Clean/Core.lean` is the sub-index of strata 0-6 (the `SP1Core` library root); check 3 below
# pins its contents to the map.
ROOT_INDEX = {"SP1Clean.lean", "SP1Clean/Core.lean", "ToClean.lean", "ToMathlib.lean", "ToPolyFun.lean"}
CORE_INDEX = "SP1Clean/Core.lean"
CORE_MAX_STRATUM = 6

# An import line, with or without the module-system modifiers (`public`, `meta`, `all`).
IMPORT_RE = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.\u00C0-\uFFFF«»]+)")

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
        im = IMPORT_RE.match(s)
        if im:
            src_lines.append(im.group(1))
            continue
        m = re.match(r"^namespace\s+SP1Clean\.([A-Za-z0-9_]+)", line)
        if m and ns_root is None:
            ns_root = m.group(1)

    # 1. direction
    imports_by_file[path] = [module_to_path(mod) for mod in src_lines]
    for mod in src_lines:
        if not mod.startswith(("SP1Clean", "ToClean", "ToMathlib", "ToPolyFun")):
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
    PILLARS = {"Math", "Model", "Semantics", "Circuits", "Extracted", "FormalModel", "Native", "Proofs", "Faithful",
               "Soundness", "Composition"}
    if pillar != "-" and ns_root in PILLARS and ns_root != pillar and path not in allowed_ns:
        nsbad.append((path, ns_root, pillar))

native_roots = [p for p in files if p.startswith(("SP1Clean/Native/", "SP1Clean/Circuits/"))]
pending = [(p, [p]) for p in native_roots]
seen = set()
for path, trail in pending:
    if path in seen:
        continue
    seen.add(path)
    if path.startswith("SP1Clean/Extracted/"):
        fail = 1
        print("FAIL: native circuits depend on legacy extraction: " + " -> ".join(trail))
        continue
    pending.extend((dep, trail + [dep]) for dep in imports_by_file.get(path, []))

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

# 3. the core index: exactly the hand-written modules of strata 0..CORE_MAX_STRATUM under
#    SP1Clean/, generated `Extracted/` modules excluded (they enter the core build as imports).
#    The index is what `lake build SP1Core` builds, so a stale entry silently moves a module in or
#    out of PR CI.
expected_core = set()
for path in files:
    if path in ROOT_INDEX or not path.startswith("SP1Clean/") or path.startswith("SP1Clean/Extracted/"):
        continue
    level, _, _ = classify(path)
    if level is not None and level <= CORE_MAX_STRATUM:
        expected_core.add(path[:-5].replace("/", "."))
indexed_core = set()
if os.path.exists(CORE_INDEX):
    for line in open(CORE_INDEX, encoding="utf-8"):
        im = IMPORT_RE.match(line.strip())
        if im:
            indexed_core.add(im.group(1))
else:
    fail = 1
    print(f"FAIL: {CORE_INDEX} is missing")
missing_core = sorted(expected_core - indexed_core)
extra_core = sorted(indexed_core - expected_core)
if missing_core:
    fail = 1
    print(f"FAIL: {len(missing_core)} core module(s) (strata 0-{CORE_MAX_STRATUM}) not imported by {CORE_INDEX}:")
    for m in missing_core[:20]:
        print(f"  {m}")
if extra_core:
    fail = 1
    print(f"FAIL: {len(extra_core)} import(s) in {CORE_INDEX} that are not core modules "
          f"(stratum > {CORE_MAX_STRATUM}, generated, or missing):")
    for m in extra_core[:20]:
        print(f"  {m}")

if fail == 0:
    print(f"check_layering: PASS ({len(files)} modules, {len(strata)} stratum rules, "
          f"{len(allowed_edges)} import + {len(allowed_ns)} namespace exception(s); "
          f"core index = {len(indexed_core)} modules)")
sys.exit(fail)
PYEOF
