"""Regressions for scripts/ci/cache_pick.py: lineage-aware restore selection."""

import importlib.util
import re
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "cache_pick", Path(__file__).resolve().parents[1] / "ci" / "cache_pick.py"
)
cp = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(cp)

P = "sp1-v2-Linux-" + "a" * 64
MAIN = "refs/heads/main"


def sha(n):
    return f"{n:040x}"


def entry(key, ref, t):
    return {"id": key, "key": key, "ref": ref, "sizeInBytes": 1, "createdAt": f"2026-09-21T{t:02d}:00:00Z"}


class PickTests(unittest.TestCase):
    def setUp(self):
        # main history: sha 3 (newest) ← 2 ← 1. Entries: align-1, core-2, align-2 (later), core-3.
        self.entries = [
            entry(f"{P}-align-{sha(1)}-1-1", MAIN, 1),
            entry(f"{P}-core-{sha(2)}-2-1", MAIN, 2),
            entry(f"{P}-align-{sha(2)}-3-1", MAIN, 3),
            entry(f"{P}-core-{sha(3)}-4-1", MAIN, 4),
            entry(f"{P}-core-pr7-{sha(9)}-5-1", "refs/pull/7/merge", 5),
            entry(f"{P}-core-pr8-{sha(8)}-6-1", "refs/pull/8/merge", 6),
            entry("sail-toolchain-Linux-x", MAIN, 7),
        ]

    def test_pr_prefers_own_then_lineage(self):
        # PR 7 based on sha 2: its own entry wins over main's.
        self.assertEqual(cp.pick(self.entries, P, "pr", [sha(2), sha(1)], pr="7"), f"{P}-core-pr7-{sha(9)}-5-1")
        # PR 8's entries are not restorable by PR 7; lineage picks align-2 over core-2.
        entries = [e for e in self.entries if "pr7" not in e["key"]]
        self.assertEqual(cp.pick(entries, P, "pr", [sha(2), sha(1)], pr="7"), f"{P}-align-{sha(2)}-3-1")

    def test_lineage_walks_past_a_missing_sha(self):
        # based on sha 5 (no entry) whose parent is sha 3 (core only).
        self.assertEqual(cp.pick(self.entries, P, "pr", [sha(5), sha(3), sha(2)], pr="7"),
                         f"{P}-core-pr7-{sha(9)}-5-1")
        entries = [e for e in self.entries if "pr7" not in e["key"]]
        self.assertEqual(cp.pick(entries, P, "pr", [sha(5), sha(3), sha(2)], pr="7"), f"{P}-core-{sha(3)}-4-1")

    def test_main_mode_includes_head_and_falls_back_to_newest(self):
        self.assertEqual(cp.pick(self.entries, P, "main", [sha(3), sha(2)]), f"{P}-core-{sha(3)}-4-1")
        # no lineage entry at all → newest main align, then newest main core
        self.assertEqual(cp.pick(self.entries, P, "main", [sha(42)]), f"{P}-align-{sha(2)}-3-1")

    def test_wrong_prefix_and_empty(self):
        self.assertIsNone(cp.pick(self.entries, "sp1-v3-Linux-" + "b" * 64, "main", [sha(3)]))
        self.assertIsNone(cp.pick([], P, "main", [sha(3)]))


class WorkflowCacheContractTests(unittest.TestCase):
    """A version/path mismatch makes restores miss or makes cleanup delete current caches."""

    def test_cache_identity_matches_across_workflows(self):
        root = Path(__file__).resolve().parents[2] / ".github" / "workflows"
        production = (root / "lean_action_ci.yml").read_text()
        experiment = (root / "build-experiment.yml").read_text()
        cleanup = (root / "cache-cleanup.yml").read_text()

        def version(text):
            return re.search(r"^  SP1_CACHE_VERSION: (.+)$", text, re.MULTILINE)[1]

        def paths(text):
            return re.search(r"^  CACHE_PATHS: \|\n((?:    .+\n)+)", text, re.MULTILINE)[1]

        self.assertEqual(version(production), version(experiment))
        self.assertEqual(version(production), version(cleanup))
        self.assertEqual(paths(production), paths(experiment))


if __name__ == "__main__":
    unittest.main()
