"""Regressions for scripts/ci/cache_gc.py: the deletion plan over a synthetic cache listing."""

import datetime as dt
import importlib.util
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "cache_gc", Path(__file__).resolve().parents[1] / "ci" / "cache_gc.py"
)
gc = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gc)

P = "sp1-v2-Linux-" + "a" * 64
OLD = "sp1-v1-Linux-" + "b" * 64
NOW = dt.datetime(2026, 9, 22, 12, 0, tzinfo=dt.timezone.utc)


def sha(n):
    return f"{n:040x}"


def entry(key, ref, hours_ago, size=800, ident=None):
    return {"id": ident or key, "key": key, "ref": ref, "sizeInBytes": size * 10**6,
            "createdAt": (NOW - dt.timedelta(hours=hours_ago)).strftime("%Y-%m-%dT%H:%M:%S.12345Z")}


MAIN = "refs/heads/main"


class ParseTests(unittest.TestCase):
    def test_layouts(self):
        self.assertEqual(gc.parse_key(f"{P}-core-{sha(1)}-10-1")["kind"], "core")
        self.assertEqual(gc.parse_key(f"{P}-align-{sha(1)}-10-1")["kind"], "align")
        self.assertEqual(gc.parse_key(f"{P}-{sha(1)}-10-1")["kind"], "core")  # old layout
        self.assertEqual(gc.parse_key(f"{P}-test-{sha(1)}-10-1")["kind"], "test")
        self.assertEqual(gc.parse_key(f"{P}-align-test-{sha(1)}-10-1")["kind"], "align-test")
        pr = gc.parse_key(f"{P}-core-pr12-{sha(1)}-10-1")
        self.assertEqual((pr["kind"], pr["pr"]), ("core", "12"))
        self.assertIsNone(gc.parse_key("sail-toolchain-Linux-ocaml5.2.1-deadbeef"))
        self.assertIsNone(gc.parse_key(f"{P}-none"))


class PlanTests(unittest.TestCase):
    def reasons(self, entries, **kw):
        return {e["id"]: r for e, r in gc.plan(entries, P, NOW, **kw)}

    def test_superseded_core_and_protection(self):
        entries = [
            entry(f"{P}-core-{sha(1)}-1-1", MAIN, 5, ident="core1"),
            entry(f"{P}-align-{sha(1)}-2-1", MAIN, 4, ident="align1"),
            entry(f"{P}-test-{sha(1)}-1-1", MAIN, 5, size=7, ident="test1"),
            entry(f"{P}-core-{sha(2)}-3-1", MAIN, 1, ident="core2"),  # core-only: alignment pending
        ]
        r = self.reasons(entries)
        self.assertIn("core1", r)
        self.assertNotIn("align1", r)
        self.assertNotIn("test1", r)   # test sub-caches are not touched by rule 1
        self.assertNotIn("core2", r)   # newest core-only sha is protected

    def test_min_age(self):
        entries = [
            entry(f"{P}-core-{sha(1)}-1-1", MAIN, 0.05, ident="core1"),
            entry(f"{P}-align-{sha(1)}-2-1", MAIN, 0.02, ident="align1"),
        ]
        self.assertEqual(self.reasons(entries), {})

    def test_retention(self):
        entries = []
        for i in range(1, 8):  # 7 align shas, newest first = sha 7
            entries.append(entry(f"{P}-align-{sha(i)}-{i}-1", MAIN, 100 - i * 10, ident=f"align{i}"))
            entries.append(entry(f"{P}-align-test-{sha(i)}-{i}-1", MAIN, 100 - i * 10, size=15, ident=f"atest{i}"))
        r = self.reasons(entries, keep_align=5)
        self.assertEqual(set(r), {"align1", "atest1", "align2", "atest2"})
        self.assertNotIn("align7", r)

    def test_stale_prefix_only_on_main(self):
        entries = [
            entry(f"{OLD}-align-{sha(1)}-1-1", MAIN, 30, ident="stale-main"),
            entry(f"{OLD}-core-{sha(2)}-1-1", "refs/pull/9/merge", 30, ident="stale-pr"),
            entry(f"{P}-align-{sha(3)}-2-1", MAIN, 3, ident="current"),
        ]
        r = self.reasons(entries)
        self.assertIn("stale-main", r)
        self.assertNotIn("stale-pr", r)
        self.assertNotIn("current", r)

    def test_one_build_per_pr_ref(self):
        ref = "refs/pull/7/merge"
        entries = [
            entry(f"{P}-core-pr7-{sha(1)}-1-1", ref, 6, ident="old-core"),
            entry(f"{P}-test-{sha(1)}-1-1", ref, 6, size=7, ident="old-test"),
            entry(f"{P}-core-pr7-{sha(2)}-2-1", ref, 2, ident="new-core"),
            entry(f"{P}-test-{sha(2)}-2-1", ref, 2, size=7, ident="new-test"),
            entry(f"{P}-align-pr7-{sha(1)}-1-2", ref, 5, ident="only-align"),
        ]
        r = self.reasons(entries)
        self.assertEqual(set(r), {"old-core", "old-test"})

    def test_closed_ref_takes_everything_including_foreign_keys(self):
        ref = "refs/pull/31/merge"
        entries = [
            entry("sail-toolchain-Linux-ocaml5.2.1-deadbeef", ref, 40, ident="sail"),
            entry(f"{P}-core-{sha(1)}-1-1", ref, 40, ident="core"),
            entry(f"{P}-core-{sha(1)}-1-1", MAIN, 40, ident="main-core"),
        ]
        r = self.reasons(entries, closed_refs=[ref])
        self.assertEqual(set(r), {"sail", "core"})


if __name__ == "__main__":
    unittest.main()
