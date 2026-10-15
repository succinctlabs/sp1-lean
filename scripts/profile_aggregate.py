#!/usr/bin/env python3
"""Aggregate compile-time measurements into rankings and cost splits.

Two inputs, one report shape:

* ``--profile-dir DIR``: the output of ``scripts/profile_compile.sh`` — ``summary.tsv``
  (``cpu<TAB>wall<TAB>exit<TAB>module``; the older three-column ``seconds<TAB>exit<TAB>module``
  form is still read, its seconds taken as the primary number) plus one ``<module>.log`` per
  module carrying Lean's ``-Dprofiler`` ``cumulative profiling times:`` block.
  Produces ``DIR/profile.md`` and ``DIR/profile.json`` with the ranking, project-wide category
  totals (import, elaboration, simp, tactic execution, type checking, typeclass inference,
  compilation, linting, ...), and a per-pillar table.

* ``--lake-log LOG [LOG ...]``: one or more ``lake build`` logs (local or a GitHub Actions job log
  with timestamp prefixes). Parses every ``Built <module> (<N>s)`` line — the per-module time of a
  real parallel build — into ``<out>.tsv`` and ``<out>.md`` with the ranking and per-pillar sums.
  When a module appears in several logs (a resumed CI build), the last occurrence wins.

Pillars: ``SP1Clean.<Pillar>``, ``SP1CleanTest``, ``ToClean``, ``ToMathlib``; anything else
(dependency modules in a cold build log) is grouped by its root name.
"""

from __future__ import annotations

import argparse
import json
import re
import statistics
import sys
from collections import defaultdict
from pathlib import Path

BUILT_RE = re.compile(r"Built ([A-Za-z0-9_.']+) \(([0-9.]+)(ms|s)\)")
CATEGORY_RE = re.compile(r"^\s*(\S.*?) ([0-9.]+(?:[eE][+-]?[0-9]+)?)(ms|s)\s*$")
HEADLINE_CATEGORIES = [
    "import", "elaboration", "simp", "tactic execution", "type checking",
    "typeclass inference", "instantiate metavars", "compilation", "linting", "interpretation",
    "blocked (unaccounted)",
]


def seconds(value: str, unit: str) -> float:
    return float(value) / 1000.0 if unit == "ms" else float(value)


def pillar_of(module: str) -> str:
    parts = module.split(".")
    if parts[0] == "SP1Clean" and len(parts) > 1:
        return f"SP1Clean.{parts[1]}"
    return parts[0]


def parse_cumulative(log: Path) -> dict[str, float]:
    """Read the ``cumulative profiling times:`` block of one profiler log."""
    categories: dict[str, float] = {}
    if not log.exists():
        return categories
    in_block = False
    for line in log.read_text(errors="replace").splitlines():
        if line.startswith("cumulative profiling times:"):
            in_block = True
            categories = {}
            continue
        if not in_block:
            continue
        match = CATEGORY_RE.match(line)
        if match is None:
            continue  # the block is the last thing Lean prints; skip stray lines
        categories[match.group(1)] = categories.get(match.group(1), 0.0) + seconds(match.group(2), match.group(3))
    return categories


def check_log(log: Path) -> None:
    """Reject zero-exit diagnostics and runs that never reached the final module checks.

    This checks the profiler's output contract, not kernel correctness; the strict full
    Lake build remains the proof gate. Keep the check outside the timed Lean process.
    """
    text = log.read_text(errors="replace")
    if re.search(r"\b(?:error|warning):|stack overflow|PANIC|uncaught exception", text):
        raise ValueError(f"{log}: Lean emitted diagnostics")
    categories = parse_cumulative(log)
    if not {"import", "module linting"} <= categories.keys():
        raise ValueError(f"{log}: incomplete cumulative profiler report")


def stats(values: list[float]) -> dict[str, float]:
    if not values:
        return {"n": 0, "total": 0.0, "mean": 0.0, "median": 0.0, "p90": 0.0, "p95": 0.0, "max": 0.0}
    ordered = sorted(values)

    def pct(p: float) -> float:
        index = min(len(ordered) - 1, int(round(p * (len(ordered) - 1))))
        return ordered[index]

    return {
        "n": len(values), "total": sum(values), "mean": statistics.fmean(values),
        "median": statistics.median(values), "p90": pct(0.9), "p95": pct(0.95), "max": ordered[-1],
    }


def ranking_table(rows: list[tuple[str, float]], top: int) -> list[str]:
    out = ["| Rank | Seconds | Module |", "| ---: | ---: | --- |"]
    for index, (module, secs) in enumerate(rows[:top], start=1):
        out.append(f"| {index} | {secs:.2f} | `{module}` |")
    return out


def pillar_table(times: dict[str, float], categories: dict[str, dict[str, float]] | None) -> list[str]:
    per: dict[str, list[str]] = defaultdict(list)
    for module in times:
        per[pillar_of(module)].append(module)
    header = ["| Pillar | Modules | Seconds | Share |"]
    if categories is not None:
        header[0] += " Import | Elab | Simp | Tactics | Typecheck | TC inference | Codegen | Linting |"
    header.append("|---|---:|---:|---:|" + ("---:|" * 8 if categories is not None else ""))
    total = sum(times.values()) or 1.0
    out = header
    for pillar, modules in sorted(per.items(), key=lambda item: -sum(times[m] for m in item[1])):
        secs = sum(times[m] for m in modules)
        row = f"| `{pillar}` | {len(modules)} | {secs:.1f} | {100 * secs / total:.1f} % |"
        if categories is not None:
            def cat(name: str) -> float:
                return sum(
                    value for m in modules for key, value in categories.get(m, {}).items()
                    if key == name or (name == "compilation" and key.startswith("compilation")))
            row += " " + " | ".join(
                f"{cat(name):.1f}" for name in (
                    "import", "elaboration", "simp", "tactic execution", "type checking",
                    "typeclass inference", "compilation", "linting")) + " |"
        out.append(row)
    return out


def write_report(path_md: Path, path_json: Path, title: str, method: str, times: dict[str, float],
                 exits: dict[str, int] | None, categories: dict[str, dict[str, float]] | None,
                 top: int, walls: dict[str, float] | None = None) -> None:
    ranked = sorted(times.items(), key=lambda item: -item[1])
    summary = stats(list(times.values()))
    lines = [f"# {title}", "", method, "",
             "| Modules | Total s | Mean | Median | p90 | p95 | Max |", "|---:|---:|---:|---:|---:|---:|---:|",
             f"| {summary['n']} | {summary['total']:.1f} | {summary['mean']:.2f} | {summary['median']:.2f} | "
             f"{summary['p90']:.2f} | {summary['p95']:.2f} | {summary['max']:.2f} |", ""]
    if exits:
        failures = sorted(m for m, code in exits.items() if code != 0)
        lines.append(f"Failed measurements: {len(failures)}" + (" — " + ", ".join(f"`{m}`" for m in failures) if failures else ""))
        lines.append("")
    lines += [f"## Top {min(top, len(ranked))} modules", ""] + ranking_table(ranked, top) + [""]
    lines += ["## Per pillar", ""] + pillar_table(times, categories) + [""]
    report: dict = {"title": title, "summary": summary, "modules": {m: {"seconds": s} for m, s in times.items()}}
    if categories is not None:
        totals: dict[str, float] = defaultdict(float)
        for module, cats in categories.items():
            for name, value in cats.items():
                totals[name] += value
        lines += ["## Category totals (project-wide, seconds)", "", "| Category | Seconds | Share of measured |", "|---|---:|---:|"]
        measured = sum(totals.values()) or 1.0
        for name, value in sorted(totals.items(), key=lambda item: -item[1]):
            if value >= 0.05:
                lines.append(f"| {name} | {value:.1f} | {100 * value / measured:.1f} % |")
        lines.append("")
        lines += ["## Headline categories per top module", "",
                  "| Module | Total | " + " | ".join(HEADLINE_CATEGORIES) + " |",
                  "|---|---:|" + "---:|" * len(HEADLINE_CATEGORIES)]
        for module, secs in ranked[:top]:
            cats = categories.get(module, {})

            def headline(name: str) -> float:
                return sum(v for k, v in cats.items()
                           if k == name or (name == "compilation" and k.startswith("compilation")))
            lines.append(f"| `{module}` | {secs:.1f} | " + " | ".join(f"{headline(c):.1f}" for c in HEADLINE_CATEGORIES) + " |")
        lines.append("")
        report["category_totals"] = dict(totals)
        for module, cats in categories.items():
            report["modules"].setdefault(module, {})["categories"] = cats
    if exits:
        for module, code in exits.items():
            report["modules"].setdefault(module, {})["exit"] = code
    if walls:
        for module, wall in walls.items():
            report["modules"].setdefault(module, {})["wall"] = wall
    path_md.write_text("\n".join(lines) + "\n")
    path_json.write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")


def run_profile_dir(directory: Path, top: int) -> None:
    summary = directory / "summary.tsv"
    if not summary.exists():
        sys.exit(f"missing {summary}")
    times: dict[str, float] = {}
    walls: dict[str, float] = {}
    exits: dict[str, int] = {}
    categories: dict[str, dict[str, float]] = {}
    for line in summary.read_text().splitlines():
        parts = line.rstrip("\n").split("\t")
        if len(parts) == 4:
            cpu, wall, code, module = parts
            walls[module] = float(wall)
        elif len(parts) == 3:
            cpu, code, module = parts
        else:
            continue
        times[module] = float(cpu)
        exits[module] = int(code)
        categories[module] = parse_cumulative(directory / f"{module}.log")
    write_report(
        directory / "profile.md", directory / "profile.json",
        "Compile-time profile (isolated per-module elaboration)",
        "Method: `scripts/profile_compile.sh` — one `lean -Dprofiler=true` per module (package flags from "
        "`scripts/lean_flags.py`) against a warm olean cache, sequential. The primary number is the process's "
        "CPU time (user+sys; proof bodies elaborate on parallel threads, so wall under-counts them) when the "
        "sweep recorded it, else wall. Category columns come from Lean's `cumulative profiling times` block "
        "(seconds).",
        times, exits, categories, top, walls)
    print(f"wrote {directory / 'profile.md'} and profile.json ({len(times)} modules)")


def run_lake_logs(logs: list[Path], out: Path, top: int) -> None:
    times: dict[str, float] = {}
    for log in logs:
        for match in BUILT_RE.finditer(log.read_text(errors="replace")):
            times[match.group(1)] = seconds(match.group(2), match.group(3))
    if not times:
        sys.exit("no `Built <module> (<N>s)` lines found")
    out.parent.mkdir(parents=True, exist_ok=True)
    ranked = sorted(times.items(), key=lambda item: -item[1])
    out.with_suffix(".tsv").write_text("".join(f"{secs}\t{module}\n" for module, secs in ranked))
    write_report(
        out.with_suffix(".md"), out.with_suffix(".json"),
        "Build-log profile (per-module times of a real `lake build`)",
        "Method: `scripts/profile_aggregate.py --lake-log` over " + ", ".join(f"`{log}`" for log in logs)
        + ". Times are Lake's per-module `Built … (Ns)` figures from a parallel build; the last "
        "occurrence of a module wins when logs overlap.",
        times, None, None, top)
    print(f"wrote {out.with_suffix('.md')}, .tsv, .json ({len(times)} modules, "
          f"{sum(times.values()):.1f} s summed)")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--profile-dir", type=Path, help="output directory of scripts/profile_compile.sh")
    parser.add_argument("--check-log", type=Path, help="validate one completed Lean profiler log")
    parser.add_argument("--lake-log", type=Path, nargs="+", help="lake build log(s) to harvest")
    parser.add_argument("--out", type=Path, default=Path(".lake/profile/build-log"),
                        help="output path prefix for --lake-log (default .lake/profile/build-log)")
    parser.add_argument("--top", type=int, default=50, help="rows in ranking tables (default 50)")
    args = parser.parse_args()
    if args.profile_dir is None and not args.lake_log and args.check_log is None:
        parser.error("give --profile-dir, --lake-log or --check-log")
    if args.check_log is not None:
        try:
            check_log(args.check_log)
        except (OSError, ValueError) as error:
            sys.exit(str(error))
    if args.profile_dir is not None:
        run_profile_dir(args.profile_dir, args.top)
    if args.lake_log:
        run_lake_logs(args.lake_log, args.out, args.top)


if __name__ == "__main__":
    main()
