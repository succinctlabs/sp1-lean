#!/usr/bin/env python3
"""Check resolved dependencies and generated provenance, independently of documentation."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
from lean_flags import load_lakefile

ROOT = Path(__file__).resolve().parents[1]


def sp1_pin_errors(cargo: str, locked: str, sp1: dict) -> list[str]:
    """Check every direct and transitive SP1 crate against the reviewed release."""
    errors = []
    version, revision = sp1["version"], sp1["revision"]
    repository = "https://github.com/succinctlabs/sp1"
    if not re.fullmatch(r"v\d+\.\d+\.\d+", version):
        errors.append("SP1 target must be a stable release")
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        errors.append("SP1 target must use a full commit")
    direct = re.findall(r"^(sp1-[\w-]+|slop-[\w-]+)\s*=\s*(.+)$", cargo, re.M)
    if not direct or len({name for name, _ in direct}) != len(direct):
        errors.append("missing or duplicate direct SP1 dependencies")
    for name, raw in direct:
        attributes = dict(re.findall(r'(\w+)\s*=\s*"([^"]+)"', raw))
        if (attributes.get("git") != repository or attributes.get("rev") != revision
                or any(key in attributes for key in ("path", "branch", "tag"))):
            errors.append(f"{name}: direct SP1 pin differs from release provenance")
    found = set()
    expected = f"git+{repository}?rev={revision}#{revision}"
    for block in locked.split("[[package]]"):
        fields = dict(re.findall(r'^(name|version|source) = "([^"]+)"$', block, re.M))
        name = fields.get("name", "")
        if not name.startswith(("sp1-", "slop-")) or name == "sp1-clean-comparison":
            continue
        if name in found:
            errors.append(f"{name}: duplicate locked SP1 package")
        found.add(name)
        if fields.get("source") != expected or fields.get("version") != version.removeprefix("v"):
            errors.append(f"{name}: locked SP1 pin differs from release provenance")
    if not {name for name, _ in direct} <= found:
        errors.append("direct SP1 dependencies missing from lockfile")
    return errors


def tree_hash(root: Path) -> tuple[str, int]:
    """Hash the generated model with paths, preserving the generator's historical digest."""
    files = [root / "LeanRV64D.lean", *sorted(
        path for path in (root / "LeanRV64D").rglob("*") if path.is_file())]
    digest = hashlib.sha256()
    for path in files:
        digest.update(path.relative_to(root).as_posix().encode() + b"\0")
        digest.update(hashlib.sha256(path.read_bytes()).hexdigest().encode() + b"\n")
    return digest.hexdigest(), len(files)


def check(root: Path) -> list[str]:
    errors = []

    def require(condition, message):
        if not condition:
            errors.append(message)

    config = load_lakefile(root / "lakefile.toml")
    packages = json.loads((root / "lake-manifest.json").read_text())["packages"]
    manifest = {package["name"]: package for package in packages}
    require(len(manifest) == len(packages), "duplicate package in Lake manifest")
    requirements = config["require"]
    names = [item["name"] for item in requirements]
    require(len(set(names)) == len(names), "duplicate direct dependency")
    for package in packages:
        name = package["name"]
        require(package.get("type") == "git", f"{name}: dependency must be a git pin")
        require(bool(re.fullmatch(r"[0-9a-f]{40}", package.get("rev", ""))),
                f"{name}: resolved revision must be a full commit")
        require(package.get("inherited", False) or name in names,
                f"{name}: direct manifest package missing from lakefile")
    for dependency in requirements:
        name, revision = dependency["name"], dependency.get("rev", "")
        package = manifest.get(name, {})
        require(bool(package), f"{name}: missing resolved dependency")
        require(bool(dependency.get("git")), f"{name}: path dependencies are not reproducible")
        require(dependency.get("git", "").removesuffix(".git") ==
                package.get("url", "").removesuffix(".git"), f"{name}: repository URL mismatch")
        commit = bool(re.fullmatch(r"[0-9a-f]{40}", revision))
        require(commit or bool(re.fullmatch(r"v\d+\.\d+\.\d+(?:-rc\d+)?", revision)),
                f"{name}: use an exact commit or version tag, not a moving branch")
        require(revision == package.get("rev" if commit else "inputRev"),
                f"{name}: requested and resolved revisions disagree")

    # The generated program and its runtime must come from the same Clean revision.
    cargo = (root / "rust/sp1-comparison/Cargo.toml").read_text()
    backend = re.search(r'^clean_backend\s*=\s*\{([^}\n]+)\}', cargo, re.M)
    backend_pin = dict(re.findall(r'(\w+)\s*=\s*"([^"]+)"', backend[1])) if backend else {}
    clean = manifest["Clean"]
    require(backend_pin.get("rev") == clean["rev"] and
            backend_pin.get("git", "").removesuffix(".git") == clean["url"].removesuffix(".git") and
            "path" not in backend_pin,
            "Clean Rust backend must match the pinned Lean emitter")
    locked = (root / "rust/sp1-comparison/Cargo.lock").read_text()
    sources = [re.search(r'^source = "([^"]+)"', block, re.M) for block in
               locked.split("[[package]]") if re.search(r'^name = "clean_backend"$', block, re.M)]
    expected_source = f'git+{backend_pin.get("git", "")}?rev={clean["rev"]}#{clean["rev"]}'
    require(len(sources) == 1 and sources[0] is not None and sources[0][1] == expected_source,
            "locked Clean Rust backend differs from the Lean emitter")

    toolchain = (root / "lean-toolchain").read_text().strip()
    require(bool(re.fullmatch(r"leanprover/lean4:v\d+\.\d+\.\d+(?:-rc\d+)?", toolchain)),
            "Lean toolchain must name an exact release")
    provenance = json.loads((root / "scripts/provenance.json").read_text())
    sail, sp1 = provenance["sail"], provenance["sp1"]
    errors.extend(sp1_pin_errors(cargo, locked, sp1))
    legacy = sp1["legacy"]
    for name, revision in [(key, sail[key]) for key in
                           ("compilerRevision", "modelRevision", "baseSnapshot")] + [
                               (key, legacy[key]) for key in ("semanticRevision", "extractorRevision")]:
        require(bool(re.fullmatch(r"[0-9a-f]{40}", revision)), f"{name}: expected full commit")
    model_hash, model_files = tree_hash(root)
    require((model_hash, model_files) == (sail["generatedTreeSha256"], sail["generatedFiles"]),
            "generated Sail tree differs from provenance; regenerate through the owned pipeline")
    config_hash = hashlib.sha256(
        (root / "scripts/sail-config/sp1_rv64d_cfg.json").read_bytes()).hexdigest()
    require(config_hash == sail["configSha256"], "Sail platform config differs from provenance")
    profile = (root / "SP1Clean/FormalModel/CoreProfile.lean").read_text()
    semantic = re.search(r'def sp1SemanticRevision : String := "([0-9a-f]{40})"', profile)
    require(semantic is not None and semantic[1] == legacy["semanticRevision"],
            "legacy Lean semantic revision differs from extraction provenance")
    dumps = json.loads((root / "export/sp1dump/index.json").read_text())
    require(dumps.get("sp1Commit") == legacy["extractorRevision"],
            "SP1 dumps differ from the extractor revision")

    libraries = {library["name"]: library for library in config["lean_lib"]}
    options = {name: library.get("leanOptions", {}) for name, library in libraries.items()}
    require(options.get("SP1CoreTest") == options.get("SP1CleanTest"),
            "test libraries must carry identical Lean options")
    if "LeanRV64DRvfi" in libraries:
        expected = dict(options["LeanRV64D"])
        expected["backward"] = {"do": {"legacy": True}}
        require(options["LeanRV64DRvfi"] == expected,
                "RvfiDii options must differ only by backward.do.legacy")
        require(libraries["LeanRV64DRvfi"].get("roots") == ["LeanRV64D.RvfiDii"],
                "legacy do workaround must be confined to RvfiDii")
    for name, opts in options.items():
        if name not in {"SP1CoreTest", "SP1CleanTest", "LeanRV64D", "LeanRV64DRvfi"}:
            require("linter" not in opts and "linter" not in opts.get("weak", {}),
                    f"{name}: linters belong at package level")
    return errors


def main() -> int:
    argparse.ArgumentParser(description=__doc__).parse_args()
    try:
        errors = check(ROOT)
    except (OSError, ValueError, KeyError, TypeError) as error:
        errors = [f"invalid dependency/provenance data: {error}"]
    for error in errors:
        print(f"FAIL: {error}", file=sys.stderr)
    if not errors:
        print("PASS: dependency pins, generated provenance and Lake configuration agree")
    return bool(errors)


if __name__ == "__main__":
    sys.exit(main())
