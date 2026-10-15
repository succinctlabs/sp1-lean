#!/usr/bin/env python3
"""lean_flags.py — print the `lean` command-line flags a Lake build applies to a module.

`lake env lean <file>` applies neither `moreLeanArgs` nor `[leanOptions]`, so every script that
invokes `lean` directly (`scripts/profile_compile.sh`, the recipes in
`docs/agents/build-profiling.md`) must replicate the package configuration. This helper reads it
from `lakefile.toml` instead of keeping a hand copy: package `moreLeanArgs` + package
`[leanOptions]` + the library's own `leanOptions`/`moreLeanArgs` (the library wins on a key, as in
Lake), each option rendered as `-Dkey=value`.

Usage:
  scripts/lean_flags.py [--lib NAME]                 one flag per line
  scripts/lean_flags.py --lib SP1CleanTest --shell   space-separated, for `$(...)` in shell

The TOML reader is `tomllib` (Python 3.11+) or `tomli`; without either, a minimal parser for the
subset `lakefile.toml` uses (flat and dotted keys, `[table]`, `[[array-of-tables]]`, string /
boolean / string-array values, `#` comments) is used and rejects anything else.
"""
from __future__ import annotations

import argparse
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

try:
    import tomllib as _toml
except ModuleNotFoundError:
    try:
        import tomli as _toml  # type: ignore[no-redef]
    except ModuleNotFoundError:
        _toml = None

_KEY_RE = re.compile(r'^([A-Za-z0-9_.\-]+)\s*=\s*(.*)$')
_STRING_RE = re.compile(r'^"((?:[^"\\]|\\.)*)"')


def _strip_comment(line: str) -> str:
    out, quoted = [], False
    for ch in line:
        if ch == '"':
            quoted = not quoted
        if ch == "#" and not quoted:
            break
        out.append(ch)
    return "".join(out).strip()


def _parse_value(raw: str):
    raw = raw.strip()
    if raw in ("true", "false"):
        return raw == "true"
    if raw.startswith("["):
        if not raw.endswith("]"):
            raise ValueError(f"unsupported multi-line array: {raw!r}")
        items, rest = [], raw[1:-1].strip()
        while rest:
            m = _STRING_RE.match(rest)
            if not m:
                raise ValueError(f"unsupported array element: {rest!r}")
            items.append(m.group(1))
            rest = rest[m.end():].strip().lstrip(",").strip()
        return items
    m = _STRING_RE.match(raw)
    if m and m.end() == len(raw):
        return m.group(1)
    if re.fullmatch(r"-?\d+", raw):
        return int(raw)
    raise ValueError(f"unsupported TOML value: {raw!r}")


def _set_dotted(table: dict, dotted: str, value) -> None:
    keys = dotted.split(".")
    for key in keys[:-1]:
        table = table.setdefault(key, {})
    table[keys[-1]] = value


def parse_minimal_toml(text: str) -> dict:
    """The lakefile subset only; raises ValueError on anything outside it."""
    root: dict = {}
    current = root
    for lineno, line in enumerate(text.splitlines(), 1):
        stripped = _strip_comment(line)
        if not stripped:
            continue
        if stripped.startswith("[["):
            name = stripped[2:-2].strip()
            current = {}
            root.setdefault(name, []).append(current)
            continue
        if stripped.startswith("["):
            name = stripped[1:-1].strip()
            current = root.setdefault(name, {})
            continue
        m = _KEY_RE.match(stripped)
        if not m:
            raise ValueError(f"lakefile.toml:{lineno}: unsupported line {line!r}")
        _set_dotted(current, m.group(1), _parse_value(m.group(2)))
    return root


def load_lakefile(path: str) -> dict:
    with open(path, "rb") as handle:
        data = handle.read()
    if _toml is not None:
        return _toml.loads(data.decode("utf-8"))
    return parse_minimal_toml(data.decode("utf-8"))


def _render(value) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    return str(value)


def _flatten(options: dict, prefix: str = "") -> dict:
    flat: dict = {}
    for key, value in options.items():
        name = f"{prefix}{key}"
        if isinstance(value, dict):
            flat.update(_flatten(value, name + "."))
        else:
            flat[name] = value
    return flat


def flags_for(config: dict, lib: str | None = None) -> list[str]:
    """`moreLeanArgs` + `-D` options for the package, overridden by library `lib`'s own."""
    args = list(config.get("moreLeanArgs", []))
    options = _flatten(config.get("leanOptions", {}))
    if lib is not None:
        libs = [entry for entry in config.get("lean_lib", []) if entry.get("name") == lib]
        if not libs:
            raise KeyError(f"no [[lean_lib]] named {lib!r} in lakefile.toml")
        args += libs[0].get("moreLeanArgs", [])
        options.update(_flatten(libs[0].get("leanOptions", {})))
    return args + [f"-D{key}={_render(value)}" for key, value in options.items()]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--lib", help="library whose own leanOptions override the package's")
    parser.add_argument("--lakefile", default=os.path.join(ROOT, "lakefile.toml"))
    parser.add_argument("--shell", action="store_true", help="one line, space-separated")
    args = parser.parse_args()
    flags = flags_for(load_lakefile(args.lakefile), args.lib)
    print(" ".join(flags) if args.shell else "\n".join(flags))


if __name__ == "__main__":
    main()
