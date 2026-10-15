#!/usr/bin/env python3
"""cache_pick.py — choose the build-cache entry a CI job should restore, by lineage.

`actions/cache` matches an exact key first and then each restore-key *prefix* against the newest
entry, with no notion of branch history — so a bare `<prefix>-` fallback restores whatever was
written last, which for a PR based on an older `main` is the wrong tree (a scripts-only PR once
rebuilt 582 modules that way). This script picks the exact key instead, from `gh cache list` and
the first-parent history of the commit being built, and prints one exact key plus two short
fallback prefixes for `$GITHUB_OUTPUT`:

  pick=<exact key or empty>     fallback1=<prefix>-align-<sha>-      fallback2=<prefix>-core-<sha>-

Modes (`--mode`):
  pr     own newest `align-pr<N>` on refs/pull/N/merge → own newest `core-pr<N>` → for each sha of
         `--lineage` (the first parents of HEAD^1 — the `main` tip the merge ref's tree contains):
         `align-<sha>` then `core-<sha>` written on refs/heads/main → newest `main` align → newest
         `main` core. Own-PR first: a deep PR's own entry holds its rebuilt closure, main's does not.
  main   for each sha of `--lineage` (HEAD first, so a re-run hits the previous attempt): `align`
         then `core` → newest main align → newest main core.

Only entries a job can actually restore are considered: those on refs/heads/main and, for a PR,
on its own merge ref. Keys outside the layout are ignored. With no listing (API failure) the
exact key is empty and the fallbacks alone drive the restore.

Usage:
  scripts/ci/cache_pick.py --mode pr --prefix <prefix> --pr 12 --lineage <file of shas> [--input list.json]
  scripts/ci/cache_pick.py --mode main --prefix <prefix> --lineage <file of shas>
"""
from __future__ import annotations

import argparse
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
    m = PREFIX_RE.match(key)
    if not m:
        return None
    r = REST_RE.match(m.group("rest"))
    if not r:
        return None
    return {"prefix": m.group("prefix"), "kind": r.group("kind") or "core", "pr": r.group("pr"), "sha": r.group("sha")}


def _newest(entries: list[dict]) -> dict | None:
    return max(entries, key=lambda e: e["createdAt"]) if entries else None


def pick(entries: list[dict], prefix: str, mode: str, lineage: list[str], pr: str | None = None) -> str | None:
    """The exact key to restore, or None. Pure: no I/O."""
    usable = []
    for e in entries:
        p = parse_key(e["key"])
        if not p or p["prefix"] != prefix or p["kind"] not in ("core", "align"):
            continue
        if e["ref"] == MAIN_REF and p["pr"] is None:
            usable.append((e, p, "main"))
        elif mode == "pr" and pr and e["ref"] == f"refs/pull/{pr}/merge" and p["pr"] == pr:
            usable.append((e, p, "own"))

    def newest(where: str, kind: str, sha: str | None = None) -> dict | None:
        return _newest([e for e, p, w in usable if w == where and p["kind"] == kind and (sha is None or p["sha"] == sha)])

    if mode == "pr":
        for kind in ("align", "core"):
            e = newest("own", kind)
            if e:
                return e["key"]
    for sha in lineage:
        for kind in ("align", "core"):
            e = newest("main", kind, sha)
            if e:
                return e["key"]
    for kind in ("align", "core"):
        e = newest("main", kind)
        if e:
            return e["key"]
    return None


def fetch(repo: str) -> list[dict]:
    try:
        out = subprocess.run(
            ["gh", "cache", "list", "--repo", repo, "--limit", "500", "--json", "id,key,ref,createdAt,sizeInBytes"],
            check=True, capture_output=True, text=True).stdout
        return json.loads(out)
    except (subprocess.CalledProcessError, json.JSONDecodeError, OSError) as err:
        print(f"cache_pick: listing failed ({err}); fallbacks only", file=sys.stderr)
        return []


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--mode", choices=["pr", "main"], required=True)
    ap.add_argument("--prefix", required=True)
    ap.add_argument("--lineage", required=True, help="file: first-parent shas, newest first (`git rev-list --first-parent -n 30 …`)")
    ap.add_argument("--pr", help="pull request number (mode pr)")
    ap.add_argument("--repo", default="dtumad/sp1-lean")
    ap.add_argument("--input", help="JSON listing instead of `gh cache list`")
    args = ap.parse_args()
    lineage = [line.strip() for line in open(args.lineage) if line.strip()]
    entries = json.load(open(args.input)) if args.input else fetch(args.repo)
    key = pick(entries, args.prefix, args.mode, lineage, args.pr) or ""
    head = lineage[0] if lineage else ""
    print(f"pick={key}")
    print(f"fallback1={args.prefix}-align-{head}-")
    print(f"fallback2={args.prefix}-core-{head}-")


if __name__ == "__main__":
    main()
