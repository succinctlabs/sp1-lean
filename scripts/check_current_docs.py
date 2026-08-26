#!/usr/bin/env python3
"""Gate the maintained documentation set and hand-written Lean module docstrings.

Historical campaign notes belong in git history.  This check fails when a maintained source still
links to one of the retired documents, when a relative Markdown link no longer resolves, or when a
hand-written Lean module has no module docstring.  Generated Lean sources and retained external
audit reports are intentionally outside the docstring/link-style policy.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys
from urllib.parse import unquote


ROOT = Path(__file__).resolve().parent.parent

RETIRED_DOCS = {
    "docs/bus-model.md",
    "docs/chip-standardization.md",
    "docs/proposals/bus-representation-consolidation.md",
    "docs/proposals/consolidation-progress.md",
    "docs/agents/shard-completeness-handoff.md",
    "docs/snapshots/compile-profile.md",
    "docs/agents/cleanup-profile.md",
    "docs/agents/cleanup-deferred.md",
    "docs/agents/perf-findings.md",
    "docs/agents/mul-operation-learnings.md",
}

LEAN_ROOTS = ("SP1Clean", "SP1CleanTest", "ToClean", "ToMathlib")
LINK_RE = re.compile(r"(?<!!)\[[^\]]*\]\(([^)]+)\)")


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def maintained_markdown() -> list[Path]:
    paths = [ROOT / "AGENTS.md", ROOT / "CLAUDE.md", ROOT / "README.md", ROOT / "rust/README.md"]
    paths.extend((ROOT / "docs").rglob("*.md"))
    return sorted(
        path
        for path in paths
        if relative(path) not in RETIRED_DOCS
        and not relative(path).startswith("docs/audits/")
    )


def local_link_target(source: Path, raw_target: str) -> Path | None:
    target = raw_target.strip()
    if target.startswith("<") and target.endswith(">"):
        target = target[1:-1]
    else:
        # A Markdown title follows whitespace; repository paths do not contain unescaped spaces.
        target = target.split(maxsplit=1)[0]
    if not target or target.startswith("#"):
        return None
    if re.match(r"^[A-Za-z][A-Za-z0-9+.-]*:", target):
        return None
    target = unquote(target.split("#", 1)[0])
    if not target:
        return None
    if target.startswith("/"):
        return ROOT / target.removeprefix("/")
    return source.parent / target


failures: list[str] = []
markdown = maintained_markdown()

for source in markdown:
    text = source.read_text()
    for retired in sorted(RETIRED_DOCS):
        if retired in text:
            failures.append(f"{relative(source)} still references retired `{retired}`")
    for match in LINK_RE.finditer(text):
        target = local_link_target(source, match.group(1))
        if target is not None and not target.exists():
            line = text.count("\n", 0, match.start()) + 1
            failures.append(
                f"{relative(source)}:{line}: unresolved local link `{match.group(1)}`"
            )

# Docstrings and comments are part of the maintained documentation surface too.
source_paths: list[Path] = []
for root_name in LEAN_ROOTS:
    source_paths.extend((ROOT / root_name).rglob("*.lean"))
source_paths.extend((ROOT / "scripts").glob("*.lean"))

handwritten_lean = sorted(
    path
    for path in source_paths
    if not relative(path).startswith("SP1Clean/Extracted/")
    and not path.name.endswith("Vectors.lean")
    and path.name not in {"axiom_probe.lean", "axiom_probe_test.lean"}
)

for source in handwritten_lean:
    text = source.read_text()
    if "/-!" not in text:
        failures.append(f"{relative(source)} has no module docstring (`/-! ... -/`)")
    for retired in sorted(RETIRED_DOCS):
        if retired in text:
            failures.append(f"{relative(source)} still references retired `{retired}`")

if failures:
    for failure in failures:
        print(f"FAIL: {failure}")
    print(f"FAIL: maintained documentation has {len(failures)} issue(s)")
    sys.exit(1)

print(
    "PASS: maintained documentation is current "
    f"({len(markdown)} Markdown files, {len(handwritten_lean)} hand-written Lean module docstrings)"
)
