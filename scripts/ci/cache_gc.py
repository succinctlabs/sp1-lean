#!/usr/bin/env python3
"""cache_gc.py — keep the repository's GitHub Actions cache inside its 10 GB budget by rule.

The build cache layout (`.github/workflows/lean_action_ci.yml`) writes one entry per build under a
key `<prefix>-<kind>-<sha>-<run id>-<attempt>` where `<prefix>` is
`sp1-<version>-<os>-<hashFiles(lean-toolchain, lake-manifest.json)>` and `<kind>` is `core`
(the PR-CI build), `align` (the full alignment build, a superset of `core` for the same sha),
`core-pr<N>` / `align-pr<N>` (entries a pull request wrote on its own ref); the earlier layout's
bare `<prefix>-<sha>-…` is read as `core`, its `-test-` / `-align-test-` entries as the test
sub-caches of the same sha. Without garbage collection every merge to `main` adds ≈ 1.6 GB and
every PR run ≈ 0.8 GB that no other ref can restore, and GitHub's LRU then evicts entries at random
with respect to lineage.

Rules (a dry run prints the plan; `--apply` deletes):
  1. superseded core: a `main` sha whose `align` entry exists and is older than `--min-age`
     minutes no longer needs its `core` entry — `align` is a superset;
  2. retention on `main`: keep the newest `--keep-align` align shas and the newest `--keep-core`
     core-only shas (an alignment run that failed or was cancelled); older `main` entries go;
  3. stale prefix on `main`: an entry whose key starts with `sp1-v` but not with `--prefix` can
     never be restored by the current toolchain/manifest — deleted (`main` only, so a PR that bumps
     the toolchain keeps the entries it wrote under the new prefix);
  4. one build per PR ref: for each `refs/pull/N/merge`, keep only the newest `core` and the newest
     `align` entry;
  5. closed PR: `--closed-ref refs/pull/N/merge` (repeatable) or `--sweep-closed-prs` (every closed
     PR per `gh pr list`) deletes everything on those refs;
  6. safety: nothing younger than `--min-age` minutes, never the newest `main` align or the newest
     `main` core, never a key the layout does not recognise (unless rule 5 names its ref).

Usage:
  scripts/ci/cache_gc.py --prefix <prefix> [--repo owner/name] [--closed-ref refs/pull/N/merge]...
                         [--sweep-closed-prs] [--only-ref refs/pull/N/merge] [--keep-align 5]
                         [--keep-core 2] [--min-age 10] [--input list.json] [--apply]
`--input` takes the JSON of `gh cache list --json id,key,ref,createdAt,sizeInBytes` (tests, or an
offline plan); without it the listing is fetched with `gh`.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import re
import subprocess
import sys

PREFIX_RE = re.compile(r"^(?P<prefix>sp1-v\d+-[A-Za-z0-9]+-[0-9a-f]{64})-(?P<rest>.+)$")
REST_RE = re.compile(
    r"^(?:(?P<kind>align-test|test|align|core)-)?(?:pr(?P<pr>\d+)-)?(?P<sha>[0-9a-f]{40})-(?P<run>\d+)-(?P<attempt>\d+)$"
)
MAIN_REF = "refs/heads/main"


def parse_key(key: str) -> dict | None:
    """The layout fields of a build-cache key, or None for a key the layout does not own."""
    m = PREFIX_RE.match(key)
    if not m:
        return None
    r = REST_RE.match(m.group("rest"))
    if not r:
        return None
    kind = r.group("kind") or "core"
    return {"prefix": m.group("prefix"), "kind": kind, "pr": r.group("pr"), "sha": r.group("sha")}


def _when(entry: dict) -> dt.datetime:
    """`createdAt` as an aware datetime (fractional seconds dropped: Python 3.9 rejects 5 digits)."""
    text = entry["createdAt"].replace("Z", "+00:00")
    text = re.sub(r"\.\d+(?=[+-]\d\d:\d\d$)", "", text)
    return dt.datetime.fromisoformat(text)


def plan(entries: list[dict], prefix: str, now: dt.datetime, closed_refs: list[str] | None = None,
         keep_align: int = 5, keep_core: int = 2, min_age_min: int = 10) -> list[tuple[dict, str]]:
    """The entries to delete, each with the rule that selects it. Pure: no I/O."""
    min_age = dt.timedelta(minutes=min_age_min)
    doomed: dict[str, tuple[dict, str]] = {}

    def condemn(entry: dict, reason: str) -> None:
        if entry["id"] in doomed:
            return
        if now - _when(entry) < min_age:
            return
        doomed[entry["id"]] = (entry, reason)

    # 5. closed PR: everything on that ref (the only rule that touches keys outside the layout).
    for ref in closed_refs or []:
        for e in entries:
            if e["ref"] == ref:
                condemn(e, f"closed PR ref {ref}")

    parsed = [(e, parse_key(e["key"])) for e in entries]
    main = [(e, p) for e, p in parsed if p and e["ref"] == MAIN_REF]

    # 3. stale prefix on main.
    for e, p in main:
        if p["prefix"] != prefix:
            condemn(e, "stale prefix on main")

    current_main = [(e, p) for e, p in main if p["prefix"] == prefix and p["pr"] is None]
    by_sha: dict[str, dict[str, list[dict]]] = {}
    for e, p in current_main:
        by_sha.setdefault(p["sha"], {}).setdefault(p["kind"], []).append(e)
    newest = lambda es: max(es, key=_when)  # noqa: E731
    align_shas = sorted((s for s, k in by_sha.items() if "align" in k), key=lambda s: _when(newest(by_sha[s]["align"])), reverse=True)
    core_only = sorted((s for s, k in by_sha.items() if "align" not in k and "core" in k), key=lambda s: _when(newest(by_sha[s]["core"])), reverse=True)
    protected = set()
    if align_shas:
        protected.add(newest(by_sha[align_shas[0]]["align"])["id"])
    if core_only:
        protected.add(newest(by_sha[core_only[0]]["core"])["id"])

    # 1. superseded core once align is older than min-age (the small `test` sub-caches stay: the
    #    test job's fallback only matches `-test-` keys; retention takes them with their sha).
    for sha in align_shas:
        a = newest(by_sha[sha]["align"])
        if now - _when(a) < min_age:
            continue
        for e in by_sha[sha].get("core", []):
            if e["id"] not in protected:
                condemn(e, f"superseded by align-{sha[:8]}")
    # 2. retention on main.
    for sha in align_shas[keep_align:]:
        for kind, es in by_sha[sha].items():
            for e in es:
                if e["id"] not in protected:
                    condemn(e, f"main retention: older than the newest {keep_align} align shas")
    for sha in core_only[keep_core:]:
        for kind, es in by_sha[sha].items():
            for e in es:
                if e["id"] not in protected:
                    condemn(e, f"main retention: older than the newest {keep_core} core-only shas")
    # 4. one build per PR ref: the newest core and the newest align stay (with the test sub-caches
    #    of the same sha); every other entry on the ref goes.
    pr_refs: dict[str, list[tuple[dict, dict]]] = {}
    for e, p in parsed:
        if p and e["ref"].startswith("refs/pull/") and p["prefix"] == prefix:
            pr_refs.setdefault(e["ref"], []).append((e, p))
    for ref, items in pr_refs.items():
        keep_sha = {}
        for kind in ("core", "align"):
            es = [e for e, p in items if p["kind"] == kind]
            if es:
                keep_sha[kind] = next(p["sha"] for e, p in items if e["id"] == newest(es)["id"])
        for e, p in items:
            base = "align" if p["kind"].startswith("align") else "core"
            if keep_sha.get(base) != p["sha"]:
                condemn(e, f"older {base} build on {ref}")
    return sorted(doomed.values(), key=lambda t: _when(t[0]))


def closed_pr_refs(repo: str) -> list[str]:
    """`refs/pull/N/merge` of every closed (merged or not) pull request."""
    out = subprocess.run(["gh", "pr", "list", "--repo", repo, "--state", "closed", "--limit", "500",
                          "--json", "number"], check=True, capture_output=True, text=True).stdout
    return [f"refs/pull/{pr['number']}/merge" for pr in json.loads(out)]


def fetch(repo: str) -> list[dict]:
    out = subprocess.run(
        ["gh", "cache", "list", "--repo", repo, "--limit", "500", "--json", "id,key,ref,createdAt,sizeInBytes"],
        check=True, capture_output=True, text=True).stdout
    return json.loads(out)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--prefix", required=True, help="the current cache prefix (sp1-<version>-<os>-<hashFiles>)")
    ap.add_argument("--repo", default="dtumad/sp1-lean")
    ap.add_argument("--closed-ref", action="append", default=[], help="delete everything on this ref (a closed PR's refs/pull/N/merge); repeatable")
    ap.add_argument("--sweep-closed-prs", action="store_true", help="also delete every entry on the ref of any closed PR (`gh pr list --state closed`)")
    ap.add_argument("--keep-align", type=int, default=5)
    ap.add_argument("--keep-core", type=int, default=2)
    ap.add_argument("--min-age", type=int, default=10, help="minutes; younger entries are never touched")
    ap.add_argument("--only-ref", help="restrict deletions to entries on this ref (a PR job tidying its own ref)")
    ap.add_argument("--input", help="JSON listing instead of `gh cache list`")
    ap.add_argument("--apply", action="store_true", help="delete; without it only the plan is printed")
    args = ap.parse_args()
    entries = json.load(open(args.input)) if args.input else fetch(args.repo)
    closed = list(args.closed_ref) + (closed_pr_refs(args.repo) if args.sweep_closed_prs else [])
    now = dt.datetime.now(dt.timezone.utc)
    doomed = plan(entries, args.prefix, now, closed, args.keep_align, args.keep_core, args.min_age)
    if args.only_ref:
        doomed = [(e, r) for e, r in doomed if e["ref"] == args.only_ref]
    total = sum(e["sizeInBytes"] for e in entries)
    freed = sum(e["sizeInBytes"] for e, _ in doomed)
    print(f"{len(entries)} entries, {total / 1e9:.2f} GB; plan deletes {len(doomed)} entries, {freed / 1e9:.2f} GB"
          f" ({'APPLY' if args.apply else 'dry run'})")
    for e, reason in doomed:
        print(f"  {e['sizeInBytes'] / 1e6:7.0f} MB  {e['ref']:24s} {e['key'][-64:]}  — {reason}")
    if args.apply:
        for e, _ in doomed:
            subprocess.run(["gh", "cache", "delete", str(e["id"]), "--repo", args.repo], check=True)
        print(f"deleted {len(doomed)} entries")


if __name__ == "__main__":
    main()
