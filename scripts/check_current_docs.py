#!/usr/bin/env python3
"""Gate the maintained documentation set and hand-written Lean module docstrings.

Check relative Markdown links, quoted repository paths, and hand-written Lean module docstrings.
This checks resolution, not whether prose or theorem statements are semantically current.
Generated Lean sources and retained external audit reports are outside this policy.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys
from urllib.parse import unquote


ROOT = Path(__file__).resolve().parent.parent


LEAN_ROOTS = ("SP1Clean", "SP1CleanTest", "ToClean", "ToMathlib", "ToPolyFun")
LINK_RE = re.compile(r"(?<!!)\[[^\]]*\]\(([^)]+)\)")


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def maintained_markdown() -> list[Path]:
    paths = [ROOT / "AGENTS.md", ROOT / "CLAUDE.md", ROOT / "README.md", ROOT / "rust/README.md"]
    paths.extend((ROOT / "docs").rglob("*.md"))
    return sorted(
        path
        for path in paths
        if not relative(path).startswith("docs/audits/")
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
    for quoted in re.findall(r"`((?:SP1Clean|SP1CleanTest|ToClean|ToMathlib|ToPolyFun|docs|scripts)/[A-Za-z0-9_/.-]+)`", text):
        if not (ROOT / quoted).exists():
            failures.append(f"{relative(source)} cites missing path `{quoted}`")
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
source_paths.extend((ROOT / "scripts").rglob("*.lean"))

handwritten_lean = sorted(
    path
    for path in source_paths
    if not relative(path).startswith("SP1Clean/Extracted/")
    and not path.name.endswith("Vectors.lean")
)

for source in handwritten_lean:
    text = source.read_text()
    if "/-!" not in text:
        failures.append(f"{relative(source)} has no module docstring (`/-! ... -/`)")

if failures:
    for failure in failures:
        print(f"FAIL: {failure}")
    print(f"FAIL: maintained documentation has {len(failures)} issue(s)")
    sys.exit(1)

print(
    "PASS: documentation links and module docstrings resolve "
    f"({len(markdown)} Markdown files, {len(handwritten_lean)} hand-written Lean module docstrings)"
)
