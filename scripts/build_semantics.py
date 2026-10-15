#!/usr/bin/env python3
"""build_semantics.py — join the build's cost to its claims.

Reads the import graph of the five source trees (`SP1Clean/`, `ToClean/`, `ToMathlib/`,
`ToPolyFun/`, `SP1CleanTest/`) plus the generated `LeanRV64D/` model, classifies every module by
stratum (`scripts/layering.txt`, longest prefix — the same rule as `scripts/check_layering.sh`) and
by semantic layer (L1 ISA semantics, L2 native gadgets/chips, L3 native machine, L4 SP1 alignment,
L5 tests, G generated model), joins per-module seconds from a Lake build log (`Built <module> (<t>)`
lines) and optionally the per-module category split of a `scripts/profile_compile.sh` sweep, and
computes the transitive import closure of each headline declaration's module.

Outputs (under --out): `modules.tsv` (one row per module: layer, stratum, seconds, lines, one
membership column per headline), `layers.md` (layer x stratum cost), `claims.md` (per headline:
closure size, seconds, strata/layers touched), `unreached.md` (modules in no headline closure),
`chips.md` (per chip and per file kind), `critical_path.md` (the longest import-weighted path
through the built modules and the P-processor bound `max(CP, total/P)` — what a build with that
many parallel jobs can never beat), and, when the log carries GitHub Actions timestamps,
`timeline.md` (concurrency over the build and the single-job tail). The audit
`docs/audits/2026-09-build-semantics.md` is regenerated from these; numbers never get edited by
hand.

`--compare <head log>` joins a second log to the first (the base) and writes `compare.md` instead:
totals and critical paths of both, the touched modules' deltas (`--touched` = a file of module
names or repo paths, one per line), the largest regressions/improvements among common modules, and
a noise check (untouched modules should stay within ±15 %).

Usage:
  scripts/build_semantics.py --lake-log <log> --out <dir> [--profile-dir <sweep dir>] [--processors 4]
  scripts/build_semantics.py --lake-log <base log> --compare <head log> --out <dir> [--touched <file>]
"""
import argparse
import collections
import csv
import fnmatch
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TREES = ["SP1Clean", "ToClean", "ToMathlib", "ToPolyFun", "SP1CleanTest", "LeanRV64D"]
IMPORT_RE = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.«»]+)")
BUILT_RE = re.compile(r"Built (\S+) \((\d+(?:\.\d+)?)(ms|s)\)")

# ---- semantic layers (path prefix -> layer; first match wins, most specific first) --------------
LAYERS = [
    # L4 SP1 alignment: the Rust extraction, faithfulness, and the exact-upstream relation.
    ("SP1Clean/Extracted/", "L4"),
    ("SP1Clean/Faithful/", "L4"),
    ("SP1Clean/Composition/", "L4"),
    ("SP1Clean/Soundness/CoreAIR", "L4"),
    ("SP1Clean/Soundness/SyscallRowSemantics.lean", "L4"),
    ("SP1Clean/FormalModel/CoreAIRRelation.lean", "L4"),
    ("SP1Clean/FormalModel/CoreProfile.lean", "L4"),
    ("SP1Clean/FormalModel/OpcodeTable.lean", "L4"),
    # L1 ISA semantics: the Sail model, its wrappers, the execution model, decode, bridges.
    ("LeanRV64D/", "G"),
    ("LeanRV64D.lean", "G"),
    ("SP1Clean/Model/Register.lean", "L1"),
    ("SP1Clean/Model/SailWrap.lean", "L1"),
    ("SP1Clean/Model/SailMemory.lean", "L1"),
    ("SP1Clean/Model/SailDecode.lean", "L1"),
    ("SP1Clean/Model/SailPure.lean", "L1"),
    ("SP1Clean/Semantics/ISA/", "L1"),
    ("SP1Clean/Model/Semantics/", "L1"),
    ("SP1Clean/Model/Core/", "L1"),
    ("SP1Clean/Model/Machine/", "L1"),
    ("SP1Clean/Proofs/Sail/", "L1"),
    ("SP1Clean/Alignment/Chips/*/Bridge.lean", "L1"),
    # L3 native machine: the engine, the assemblies, the capstones, the per-chip machine contracts.
    ("SP1Clean/Soundness/", "L3"),
    ("SP1Clean/Proofs/Completeness/", "L3"),
    ("SP1Clean/Alignment/", "L3"),
    ("SP1Clean/FormalModel/Shard", "L3"),
    ("SP1Clean/FormalModel/Execution.lean", "L3"),
    ("SP1Clean/FormalModel/EventExecution.lean", "L3"),
    ("SP1Clean/FormalModel/SupportedShard.lean", "L3"),
    ("SP1Clean/FormalModel/CoreShard.lean", "L3"),
    ("SP1Clean/FormalModel/Relations.lean", "L3"),
    ("SP1Clean/FormalModel/Verifier.lean", "L3"),
    ("SP1Clean/FormalModel/Trace", "L3"),
    # L5 tests.
    ("SP1CleanTest/", "L5"),
    ("SP1CleanTest.lean", "L5"),
    # L2 everything else hand-written: math, buses, contracts, gadgets, chips, upstream-destined.
    ("SP1Clean/", "L2"),
    ("SP1Clean.lean", "L2"),
    ("ToClean/", "L2"), ("ToClean.lean", "L2"),
    ("ToMathlib/", "L2"), ("ToMathlib.lean", "L2"),
    ("ToPolyFun/", "L2"), ("ToPolyFun.lean", "L2"),
]

# ---- headline declarations (module, label, status) ----------------------------------------------
HEADLINES = [
    ("SP1Clean.FormalModel.Shard", "Shard.Executes/Admissible (capstone vocabulary)", "unfilled"),
    ("SP1Clean.Soundness.Shard.Machine", "Shard.realizes / statement_iff_of_realizes (capstone)", "unfilled"),
    ("SP1Clean.Soundness.AIR", "supported_core_native_sound (retained 55-table)", "closed"),
    ("SP1Clean.Soundness.BootHalt", "supported_core_boot_to_halt_single_shard", "closed"),
    ("SP1Clean.Soundness.NativeCompleteness", "supported_core_native_complete (+ totality-conditional)", "closed/conditional"),
    ("SP1Clean.Proofs.Completeness.NativeTraceCompiler", "nativeTrace / NativeShardTraceTotal", "closed/open"),
    ("SP1Clean.Soundness.HostHintReadFinalSnapshot", "HostHintReadCPU.source_execution_with_memory (frontier)", "closed, not capstone"),
    ("SP1Clean.Faithful.SupportedMachine", "supportedChipFaithfulness (25 ChipFaithful anchors)", "closed"),
    ("SP1Clean.Soundness.CoreAIR", "sp1_air_sound_of_obligations (exact upstream)", "conditional"),
    ("SP1Clean.Soundness.CoreAIRSyscallFree", "CoreAIR syscall-free obligations", "partial"),
    ("SP1Clean.Composition.CoreArtifact", "exactNativeArtifact_* (exact -> native transport)", "conditional"),
    ("SP1Clean.Composition.Balance", "naturalLedger balance bridge", "closed"),
    ("SP1Clean.Composition.CoreSystemSemantics", "SyscallCore/MemoryLocal typed views", "closed"),
]


def classify_layer(path):
    for prefix, layer in LAYERS:
        if "*" in prefix:
            if fnmatch.fnmatch(path, prefix):
                return layer
        elif path.startswith(prefix):
            return layer
    return "?"


def load_strata():
    strata = []
    with open(os.path.join(ROOT, "scripts", "layering.txt"), encoding="utf-8") as f:
        for raw in f:
            line = raw.split("#", 1)[0].strip()
            if not line:
                continue
            level, pillar, prefix = line.split()
            strata.append((prefix, int(level), pillar))
    strata.sort(key=lambda e: -len(e[0]))
    return strata


def classify_stratum(path, strata):
    for prefix, level, pillar in strata:
        if "*" in prefix:
            if fnmatch.fnmatch(path, prefix):
                return level
        elif path.startswith(prefix):
            return level
    if path.startswith("LeanRV64D"):
        return -1
    if path.startswith("SP1CleanTest"):
        return 12
    if path in ("SP1Clean.lean", "SP1Clean/Core.lean", "ToClean.lean", "ToMathlib.lean", "ToPolyFun.lean"):
        return 99  # root indices: not a layer, imported by nothing
    return None


def read_graph():
    """module -> (path, imports, lines)."""
    graph = {}
    for tree in TREES:
        root_file = os.path.join(ROOT, tree + ".lean")
        paths = []
        if os.path.exists(root_file):
            paths.append(tree + ".lean")
        for dp, _, fs in os.walk(os.path.join(ROOT, tree)):
            for fn in fs:
                if fn.endswith(".lean"):
                    paths.append(os.path.relpath(os.path.join(dp, fn), ROOT))
        for path in paths:
            mod = path[:-5].replace("/", ".")
            imports, lines, in_header = [], 0, True
            with open(os.path.join(ROOT, path), encoding="utf-8", errors="replace") as f:
                for line in f:
                    lines += 1
                    if not in_header:
                        continue
                    s = line.strip()
                    m = IMPORT_RE.match(s)
                    if m:
                        imports.append(m.group(1))
                    elif s and not s.startswith(("--", "/-", "module", "prelude")) and not s.endswith("-/"):
                        # first non-import, non-comment line ends the header
                        in_header = False
            graph[mod] = (path, imports, lines)
    return graph


def closure(graph, start):
    seen, stack = set(), [start]
    while stack:
        m = stack.pop()
        if m in seen or m not in graph:
            continue
        seen.add(m)
        stack.extend(graph[m][1])
    return seen


def read_lake_log(path):
    secs = {}
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            m = BUILT_RE.search(line)
            if m:
                v = float(m.group(2))
                secs[m.group(1)] = v / 1000 if m.group(3) == "ms" else v
    return secs


TS_RE = re.compile(r"^\ufeff?(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d)(?:\.\d+)?Z\s")


def read_lake_log_events(path):
    """module -> (seconds, end time in epoch seconds or None) from `Built` lines with an optional
    GitHub Actions timestamp prefix (a local Lake log has none, so `end` is None there)."""
    import datetime as dt
    events = {}
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            m = BUILT_RE.search(line)
            if not m:
                continue
            v = float(m.group(2))
            v = v / 1000 if m.group(3) == "ms" else v
            t = TS_RE.match(line)
            end = dt.datetime.fromisoformat(t.group(1)).replace(tzinfo=dt.timezone.utc).timestamp() if t else None
            events[m.group(1)] = (v, end)
    return events


def critical_path(imports, secs):
    """Longest path through the import DAG restricted to the modules in `secs`, each weighted by its
    seconds; `imports` maps module -> imported modules. Returns (length, [modules root..leaf])."""
    best = {}
    order = []
    state = {}
    for root in secs:
        if root in state:
            continue
        stack = [(root, False)]
        while stack:
            m, done = stack.pop()
            if done:
                state[m] = 2
                order.append(m)
                continue
            if state.get(m) == 2:
                continue
            state[m] = 1
            stack.append((m, True))
            for i in imports.get(m, []):
                if i in secs and state.get(i) != 2:
                    stack.append((i, False))
    for m in order:
        pred = max((best[i] for i in imports.get(m, []) if i in best), key=lambda p: p[0], default=(0.0, []))
        best[m] = (pred[0] + secs[m], pred[1] + [m])
    if not best:
        return 0.0, []
    return max(best.values(), key=lambda p: p[0])


def timeline(events, bucket=60):
    """Concurrency over the build from timestamped events: returns None without timestamps, else a
    dict with the span, the average/peak concurrency, the seconds spent at <= 1 and <= 2 running
    jobs, the longest solo stretch (module, seconds), and per-bucket running counts. Jobs under
    one second are left out (their timestamps cluster and would inflate the counts)."""
    timed = {m: (s, e) for m, (s, e) in events.items() if e is not None and s >= 1.0}
    if not timed:
        return None
    starts = {m: e - s for m, (s, e) in timed.items()}
    t0 = min(starts.values()); t1 = max(e for _, e in timed.values())
    span = max(t1 - t0, 1e-9)
    n = int(span // bucket) + 1
    running = [0] * n
    for m, (s, e) in timed.items():
        lo = int((starts[m] - t0) // bucket); hi = int((e - t0) // bucket)
        for b in range(max(lo, 0), min(hi, n - 1) + 1):
            running[b] += 1
    total = sum(s for s, _ in timed.values())
    le1 = sum(bucket for r in running if r <= 1)
    le2 = sum(bucket for r in running if r <= 2)
    # the module that was running alone for the longest stretch
    solo_best = ("", 0.0)
    for m, (s, e) in timed.items():
        lo = int((starts[m] - t0) // bucket); hi = int((e - t0) // bucket)
        alone = sum(bucket for b in range(max(lo, 0), min(hi, n - 1) + 1) if running[b] <= 1)
        if alone > solo_best[1]:
            solo_best = (m, alone)
    return {"span": span, "total": total, "avg": total / span, "peak": max(running),
            "le1": le1, "le2": le2, "solo": solo_best, "running": running, "bucket": bucket}


CATEGORIES = ["import", "elaboration", "simp", "tactic execution", "interpretation", "type checking",
              "typeclass inference", "blocked (unaccounted)", "linting"]


def read_profile_dir(path):
    """Per-module solo wall seconds and category seconds from profile_aggregate.py's profile.json."""
    pj = os.path.join(path, "profile.json")
    if not os.path.exists(pj):
        return {}
    data = json.load(open(pj))
    mods = data.get("modules", {})
    if isinstance(mods, list):
        mods = {row["module"]: row for row in mods}
    return {m: {"solo": row.get("seconds", 0.0), **{c: row.get("categories", {}).get(c, 0.0) for c in CATEGORIES}}
            for m, row in mods.items()}


def fmt(x):
    return f"{x:,.0f}".replace(",", " ")


def write_critical_path(args, imports, secs, events):
    """critical_path.md (+ timeline.md when the log is timestamped)."""
    P = args.processors
    total = sum(secs.values())
    cp, path = critical_path(imports, secs)
    bound = max(cp, total / P) if P else cp
    with open(os.path.join(args.out, "critical_path.md"), "w") as f:
        f.write(f"Source log: `{args.lake_log}` — {len(secs)} built modules, {fmt(total)} s summed.\n\n")
        f.write(f"| Critical path | Σ / {P} | {P}-processor bound `max(CP, Σ/P)` | CP share of bound |\n|---:|---:|---:|---:|\n")
        f.write(f"| {fmt(cp)} s ({cp/60:.1f} min) | {fmt(total/P)} s ({total/P/60:.1f} min) | {fmt(bound)} s ({bound/60:.1f} min) | {100*cp/max(bound,1e-9):.0f} % |\n\n")
        f.write("The build is *critical-path-bound* when CP > Σ/P (shortening the path helps) and *throughput-bound* "
                "otherwise (only CPU-seconds help). Modules outside the import graph (dependencies such as Clean) "
                "count in Σ but not in the path.\n\n")
        f.write(f"Path ({len(path)} modules, root → leaf):\n\n")
        for m in path:
            f.write(f"- `{m}` {secs[m]:.0f} s\n")
    tl = timeline(events)
    if tl:
        with open(os.path.join(args.out, "timeline.md"), "w") as f:
            f.write(f"Source log: `{args.lake_log}` (GitHub Actions timestamps; start = end − duration).\n\n")
            f.write("| Build span | Σ built | Average concurrency | Peak | Seconds at ≤ 1 job | at ≤ 2 jobs | Longest solo stretch |\n|---:|---:|---:|---:|---:|---:|---|\n")
            f.write(f"| {tl['span']/60:.1f} min | {fmt(tl['total'])} s | {tl['avg']:.2f} | {tl['peak']} | {fmt(tl['le1'])} | {fmt(tl['le2'])} | `{tl['solo'][0]}` {fmt(tl['solo'][1])} s |\n\n")
            f.write(f"Running jobs per {tl['bucket']}-second bucket (minute: count):\n\n")
            f.write(" ".join(f"{i}:{r}" for i, r in enumerate(tl["running"])) + "\n")


def read_touched(path, graph_modules):
    """Module names from a file of names or repo paths (`git diff --name-only` output works)."""
    touched = set()
    with open(path, encoding="utf-8") as f:
        for raw in f:
            item = raw.strip()
            if not item:
                continue
            if item.endswith(".lean"):
                item = item[:-5].replace("/", ".")
            if item in graph_modules:
                touched.add(item)
    return touched


def write_compare(args, imports):
    """compare.md: base (`--lake-log`) vs head (`--compare`)."""
    P = args.processors
    base = read_lake_log_events(args.lake_log)
    head = read_lake_log_events(args.compare)
    bs = {m: s for m, (s, _) in base.items()}
    hs = {m: s for m, (s, _) in head.items()}
    touched = read_touched(args.touched, set(imports)) if args.touched else set()
    common = sorted(set(bs) & set(hs))
    deltas = {m: (hs[m] - bs[m], (hs[m] - bs[m]) / bs[m] if bs[m] else float("inf")) for m in common}
    untouched = [m for m in common if m not in touched]
    noisy = [m for m in untouched if abs(deltas[m][1]) > 0.15 and max(bs[m], hs[m]) >= 5]
    abs_pct = sorted(abs(deltas[m][1]) for m in untouched if bs[m] >= 5)
    median_pct = abs_pct[len(abs_pct) // 2] if abs_pct else 0.0
    with open(os.path.join(args.out, "compare.md"), "w") as f:
        f.write("| | Modules | Σ built s | Critical path s | " + f"{P}-processor bound s |\n|---|---:|---:|---:|---:|\n")
        for name, secs in (("base", bs), ("head", hs)):
            cp, _ = critical_path(imports, secs)
            tot = sum(secs.values())
            f.write(f"| {name} | {len(secs)} | {fmt(tot)} | {fmt(cp)} | {fmt(max(cp, tot / P))} |\n")
        tb, th = sum(bs.values()), sum(hs.values())
        f.write(f"\nΔ Σ built: {th - tb:+.0f} s ({100 * (th - tb) / max(tb, 1e-9):+.1f} %). Only-in-base: {len(set(bs) - set(hs))}, only-in-head: {len(set(hs) - set(bs))}.\n\n")
        if touched:
            f.write(f"## Touched modules ({len(touched)} named, {len([m for m in touched if m in common])} in both logs)\n\n| Module | base s | head s | Δ s | Δ % |\n|---|---:|---:|---:|---:|\n")
            for m in sorted(touched, key=lambda m: -abs(deltas.get(m, (0, 0))[0])):
                if m in common:
                    f.write(f"| `{m}` | {bs[m]:.1f} | {hs[m]:.1f} | {deltas[m][0]:+.1f} | {100 * deltas[m][1]:+.0f} % |\n")
                else:
                    f.write(f"| `{m}` | {bs.get(m, float('nan')):.1f} | {hs.get(m, float('nan')):.1f} | — | — |\n")
            f.write("\n")
        for title, rows in (("Largest regressions (common modules)", sorted(common, key=lambda m: -deltas[m][0])[:20]),
                            ("Largest improvements (common modules)", sorted(common, key=lambda m: deltas[m][0])[:20])):
            f.write(f"## {title}\n\n| Module | base s | head s | Δ s | Δ % | touched |\n|---|---:|---:|---:|---:|---|\n")
            for m in rows:
                f.write(f"| `{m}` | {bs[m]:.1f} | {hs[m]:.1f} | {deltas[m][0]:+.1f} | {100 * deltas[m][1]:+.0f} % | {'yes' if m in touched else ''} |\n")
            f.write("\n")
        f.write(f"## Noise check\n\nUntouched common modules ≥ 5 s: median |Δ| = {100 * median_pct:.0f} %; "
                f"{len(noisy)} outside ±15 %" + (": " + ", ".join(f"`{m}` ({100 * deltas[m][1]:+.0f} %)" for m in noisy[:15]) if noisy else "") + ".\n")
    print(f"wrote {args.out}/compare.md: base {len(bs)} modules {fmt(tb)} s, head {len(hs)} modules {fmt(th)} s, {len(noisy)} noisy untouched")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lake-log", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--profile-dir")
    ap.add_argument("--processors", type=int, default=4, help="P for the P-processor bound (default 4 = the CI runner)")
    ap.add_argument("--compare", help="a second (head) Lake log: write compare.md against --lake-log (the base) and stop")
    ap.add_argument("--touched", help="with --compare: file of touched module names or repo paths, one per line")
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)

    graph = read_graph()
    imports = {m: v[1] for m, v in graph.items()}
    if args.compare:
        write_compare(args, imports)
        return
    strata = load_strata()
    events = read_lake_log_events(args.lake_log)
    secs = {m: s for m, (s, _) in events.items()}
    cats = read_profile_dir(args.profile_dir) if args.profile_dir else {}
    write_critical_path(args, imports, secs, events)

    info = {}
    for mod, (path, imports, lines) in graph.items():
        info[mod] = {
            "path": path, "layer": classify_layer(path), "stratum": classify_stratum(path, strata),
            "seconds": secs.get(mod, 0.0), "lines": lines, "imports": imports,
            "prof": cats.get(mod, {}),
        }
    unassigned = [m for m, i in info.items() if i["layer"] == "?" or i["stratum"] is None]
    if unassigned:
        print("FAIL: modules without a layer/stratum:", unassigned[:10], file=sys.stderr)
        sys.exit(1)

    closures = {h: closure(graph, h) for h, _, _ in HEADLINES if h in graph}
    missing = [h for h, _, _ in HEADLINES if h not in graph]
    if missing:
        print("note: headline modules not found:", missing, file=sys.stderr)

    # modules.tsv
    with open(os.path.join(args.out, "modules.tsv"), "w", newline="") as f:
        w = csv.writer(f, delimiter="\t")
        prof_cols = (["solo"] + CATEGORIES) if cats else []
        w.writerow(["module", "layer", "stratum", "seconds", "lines"] + prof_cols + [h for h in closures] + ["n_headlines"])
        for mod in sorted(info, key=lambda m: -info[m]["seconds"]):
            flags = [1 if mod in closures[h] else 0 for h in closures]
            prof = [f"{info[mod]['prof'].get(c, 0.0):.2f}" for c in prof_cols]
            w.writerow([mod, info[mod]["layer"], info[mod]["stratum"], f"{info[mod]['seconds']:.2f}",
                        info[mod]["lines"]] + prof + flags + [sum(flags)])

    # layers.md
    total = sum(i["seconds"] for i in info.values())
    layer_names = {"L1": "L1 ISA semantics", "L2": "L2 native gadgets/chips", "L3": "L3 native machine",
                   "L4": "L4 SP1 alignment", "L5": "L5 tests", "G": "G generated Sail model"}
    by_layer = collections.defaultdict(lambda: [0, 0.0, 0])
    by_layer_stratum = collections.defaultdict(lambda: [0, 0.0])
    for i in info.values():
        b = by_layer[i["layer"]]; b[0] += 1; b[1] += i["seconds"]; b[2] += i["lines"]
        bs = by_layer_stratum[(i["layer"], i["stratum"])]; bs[0] += 1; bs[1] += i["seconds"]
    with open(os.path.join(args.out, "layers.md"), "w") as f:
        f.write(f"Source log: `{args.lake_log}` — {len(secs)} built modules, {fmt(total)} s summed.\n\n")
        f.write("| Layer | Modules | Seconds | Share | Lines | s / 100 lines |\n|---|---:|---:|---:|---:|---:|\n")
        for layer in ["L1", "L2", "L3", "L4", "L5", "G"]:
            n, s, ln = by_layer[layer]
            f.write(f"| {layer_names[layer]} | {n} | {fmt(s)} | {100*s/total:.1f} % | {fmt(ln)} | {100*s/max(ln,1):.2f} |\n")
        f.write("\n| Layer | Stratum | Modules | Seconds |\n|---|---:|---:|---:|\n")
        for (layer, st), (n, s) in sorted(by_layer_stratum.items(), key=lambda kv: (kv[0][0], kv[0][1] if kv[0][1] is not None else -2)):
            f.write(f"| {layer} | {st} | {n} | {fmt(s)} |\n")
        if cats:
            f.write("\nSolo profiler sweep (`scripts/profile_compile.sh`, one `lean` per module, sequential): "
                    "wall and Lean's category seconds per layer (categories can exceed wall — proof bodies "
                    "elaborate on parallel threads; `blocked` is the main thread waiting for them).\n\n")
            f.write("| Layer | Modules swept | Solo wall | " + " | ".join(CATEGORIES) + " |\n|---|---:|---:|" + "---:|" * len(CATEGORIES) + "\n")
            for layer in ["L1", "L2", "L3", "L4", "L5"]:
                rows = [i["prof"] for i in info.values() if i["layer"] == layer and i["prof"]]
                if not rows:
                    continue
                f.write(f"| {layer_names[layer]} | {len(rows)} | {fmt(sum(r['solo'] for r in rows))} | "
                        + " | ".join(fmt(sum(r[c] for r in rows)) for c in CATEGORIES) + " |\n")
            rows = [i["prof"] for i in info.values() if i["prof"]]
            f.write(f"| all | {len(rows)} | {fmt(sum(r['solo'] for r in rows))} | "
                    + " | ".join(fmt(sum(r[c] for r in rows)) for c in CATEGORIES) + " |\n")

    # claims.md
    with open(os.path.join(args.out, "claims.md"), "w") as f:
        f.write("| Headline (module) | Status | Closure | Seconds | By layer (modules / s) |\n|---|---|---:|---:|---|\n")
        for h, label, status in HEADLINES:
            if h not in closures:
                continue
            cl = closures[h]
            s = sum(info[m]["seconds"] for m in cl)
            per = collections.defaultdict(lambda: [0, 0.0])
            for m in cl:
                per[info[m]["layer"]][0] += 1; per[info[m]["layer"]][1] += info[m]["seconds"]
            per_s = ", ".join(f"{l} {n}/{fmt(v)}" for l, (n, v) in sorted(per.items()))
            f.write(f"| {label} (`{h}`) | {status} | {len(cl)} | {fmt(s)} | {per_s} |\n")

    # unreached.md
    reached = set().union(*closures.values()) if closures else set()
    unreached = [m for m in info if m not in reached and m.split(".")[0] in ("SP1Clean",)]
    with open(os.path.join(args.out, "unreached.md"), "w") as f:
        s = sum(info[m]["seconds"] for m in unreached)
        f.write(f"{len(unreached)} `SP1Clean.*` modules in no headline closure, {fmt(s)} s.\n\n")
        bydir = collections.defaultdict(list)
        for m in unreached:
            bydir[os.path.dirname(info[m]["path"])].append(m)
        for d, ms in sorted(bydir.items()):
            f.write(f"- `{d}/` ({len(ms)} modules, {fmt(sum(info[m]['seconds'] for m in ms))} s): "
                    + ", ".join(f"`{m.split('.')[-1]}`" for m in sorted(ms)) + "\n")

    # chips.md
    chips = collections.defaultdict(collections.Counter)
    kinds = collections.Counter()
    for mod, i in info.items():
        mm = re.search(r"\.([A-Za-z0-9]+Chip)\b", mod)
        if not mm:
            continue
        chip = mm.group(1)
        if ".Extracted.ChipOracle." in mod: kind = "ChipOracle (L4)"
        elif ".Faithful." in mod: kind = "Faithful (L4)"
        elif ".Alignment." in mod: kind = "Bridge (L1)" if mod.endswith(".Bridge") else "Contracts (L3)"
        elif ".Native.Chips." in mod: kind = "Native.Defs (L2)"
        elif ".Proofs.Chips." in mod: kind = "Proofs." + mod.split(chip + ".")[-1].split(".")[0] + " (L2)"
        elif mod.startswith("SP1CleanTest"): kind = "Test (L5)"
        else: kind = "other"
        chips[chip][kind] += i["seconds"]; kinds[kind] += i["seconds"]
    with open(os.path.join(args.out, "chips.md"), "w") as f:
        tot = sum(kinds.values())
        f.write(f"Chip-named modules: {fmt(tot)} s ({100*tot/total:.1f} % of the build).\n\n| File kind | Seconds |\n|---|---:|\n")
        for k, v in kinds.most_common():
            f.write(f"| {k} | {fmt(v)} |\n")
        f.write("\n| Chip | Seconds | Largest kinds |\n|---|---:|---|\n")
        for c, d in sorted(chips.items(), key=lambda kv: -sum(kv[1].values())):
            f.write(f"| {c} | {fmt(sum(d.values()))} | " + ", ".join(f"{k} {v:.0f}" for k, v in d.most_common(4)) + " |\n")

    print(f"wrote {args.out}/{{modules.tsv,layers.md,claims.md,unreached.md,chips.md,critical_path.md[,timeline.md]}}: "
          f"{len(info)} modules, {fmt(total)} s, {len(closures)} headlines, {len(unreached)} unreached")


if __name__ == "__main__":
    main()
