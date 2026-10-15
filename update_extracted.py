#!/usr/bin/env python3

"""Regenerate whole-chip Rust AIR oracles and transitional helper modules from the upstream
`sp1-constraint-compiler`.

Adapted from sp1-lean's `update_constraints.py`. The upstream compiler emits field-generic Lean
directly: an operation/table **column struct** plus ordered **`asserts` and `interactions` lists**
(`{F : Type} [Field F] [CoeHead F ℕ]`). This script runs the compiler, sandwiches its output
between a fixed header/footer, and writes the whole file. It never emits an executable Clean
`Circuit`; native circuits are deliberately hand-maintained proof objects under `Native/`.

The stable target is `Extracted/ChipOracle/<Chip>.lean`: one chip-specific namespace containing the
complete Rust row shape, helper definitions used by the emitted expression, `asserts`, and
`interactions`. Canonical reader structs are reused from native type modules; chip-private
arithmetic structs/functions remain namespaced inside that chip oracle and are not public
operation-level faithfulness boundaries. All 25 supported chips are migrated to this form;
`OPERATIONS` persists as deliberate shared substrate (canonical reader modules + statement
targets that multiple chip anchors reference). Native Clean circuits are hand-maintained under
`Native/`; this generator deliberately emits no circuit implementation. Trace conformance lives
in the dump-anchored pipeline (`scripts/update_sp1_dumps.sh` + `scripts/witgenExport.lean
--testdata`), not here — this script emits AIR artifacts only.

Shared column types are owned by `Circuits/Types`. Their field layouts are checked against
the independent Rust discovery output before reuse. Private Rust-oracle types remain generated;
modules use `--reuse-struct <Name>` and imports to avoid duplicate shared definitions. Rather than hand-maintain a per-entry reuse list, this script:

  1. *Discovery pass* — runs the compiler for every module with NO reuse and parses which
     `structure <Name>` blocks each emits, building a global struct→owning-module map (seeded by
     the native type declarations for shared-struct cases). Collisions fail loudly.
  2. *Emit pass* — for each module, reuse = every struct it emits that another module owns; those
     are passed as `--reuse-struct` and their owners are imported. The compiler re-runs and the
     file is written.

The shared interaction vocabulary lives in `SP1Clean/Extracted/ExtractionDSL.lean`; whole-chip
faithfulness anchors live in `SP1Clean/Faithful/`.

Usage: `SP1_DIR=/path/to/extraction-branch-checkout python3 update_extracted.py`.
`SP1_DIR` must be a clean checkout of the pinned extraction branch; its merge base is the
unmodified semantic SP1 revision recorded below, and every extraction change is an ordinary
commit on it.  The checkout is never modified by this script.
"""

import json
import os
from pathlib import Path
import re
import subprocess
from typing import Dict, List, Sequence, Set, Tuple

# ── Registry ────────────────────────────────────────────────────────────────────────────────
# Flat lists of module names to emit (order is irrelevant — every compiler call is independent;
# grouped only for readability). A module's reuse of sub-structs is derived automatically.

# Operation / reader / compare-op modules → `Extracted/<name>.lean`.
OPERATIONS: List[str] = [
    # Instruction readers + CPU state. These helpers reuse native column types.
    "RTypeReader", "ITypeReader", "ITypeReaderImmutable", "ALUTypeReader", "JTypeReader", "CPUState",
    # Leaf arithmetic / byte ops (compose nothing).
    "AddOperation", "SubOperation", "AddrAddOperation", "BitwiseOperation",
    "U16MSBOperation", "U16toU8OperationUnsafe", "U16toU8OperationSafe",
    # Composed arithmetic ops.
    "AddwOperation", "SubwOperation", "AddressOperation", "BitwiseU16Operation", "MulOperation",
    # Compare ops (leaf first, then composed).
    "IsZeroOperation", "U16CompareOperation",
    "IsZeroWordOperation", "IsEqualWordOperation",
    "LtOperationUnsigned", "LtOperationSigned",
]

# Stable recognition set used when `EXTRACT_ONLY` narrows the modules regenerated in one run. A
# selected system table may still call a previously generated helper that is not itself being
# rewritten in that run.
KNOWN_OPERATIONS = frozenset(OPERATIONS)

# Chip modules → `Extracted/<chip>Chip.lean` (column struct `<chip>Cols` + composed constraints).
CHIPS: List[str] = [
    "Add", "Addi", "Addw", "Sub", "Subw", "Bitwise", "Lt", "Mul", "DivRem", "AluX0",
    "ShiftLeft", "ShiftRight", "Branch", "Jal", "Jalr", "UType",
    "LoadByte", "LoadHalf", "LoadWord", "LoadDouble", "LoadX0",
    "StoreByte", "StoreHalf", "StoreWord", "StoreDouble",
]

# Non-instruction tables in the two pinned trusted Core clusters. These are extracted as exact flat
# rows under `Extracted/SystemOracle/`: unlike proof-oriented native gadgets, the flat row is merely
# a faithful name for every upstream column index and carries no claimed semantic decomposition.
SYSTEM_TABLES: List[str] = [
    "Program", "Byte", "Range", "SyscallCore", "SyscallInstrs", "MemoryBump",
    "StateBump", "MemoryLocal", "Global", "MemoryGlobalInit", "MemoryGlobalFinalize",
]

# Exact trusted clusters selected for the current theorem.  These names are checked against the
# manifest emitted by `RiscvAir::machine()` on every regeneration; they are not inferred from the
# Python extraction registry, which would allow two stale lists to agree with each other.
BASELINE_CORE_CLUSTER: Tuple[str, ...] = (
    "Program", "Byte", "Range", "SyscallCore", "DivRem", "Add", "Addi", "Addw",
    "Sub", "Subw", "Bitwise", "Mul", "ShiftRight", "ShiftLeft", "Lt", "AluX0",
    "LoadByte", "LoadHalf", "LoadWord", "LoadDouble", "LoadX0", "StoreByte",
    "StoreHalf", "StoreWord", "StoreDouble", "UType", "Branch", "Jal", "Jalr",
    "SyscallInstrs", "MemoryBump", "StateBump", "MemoryLocal", "Global",
)
MEMORY_BOUNDARY_CLUSTER: Tuple[str, ...] = (
    "Program", "Byte", "Range", "MemoryGlobalInit", "MemoryGlobalFinalize", "Global",
)

# Chips with a chip-namespaced oracle under `Extracted/ChipOracle/<Chip>.lean`. Canonical
# reader structs and their generated `asserts`/`interactions` functions are reused, while
# chip-private arithmetic structs and functions stay in the oracle.
# The 2026-07 migration is complete: every entry of `CHIPS` is here, and no legacy
# `Extracted/<Chip>Chip.lean` files remain (a `CHIPS` entry missing from this set fails the run).
CHIP_ORACLES: Set[str] = {
    "Add", "Sub", "Subw", "Mul", "DivRem", "Addi", "Jalr", "Jal", "UType", "Addw",
    "Bitwise", "Lt", "ShiftLeft", "ShiftRight", "AluX0", "Branch", "LoadByte", "LoadHalf",
    "LoadWord", "LoadDouble", "LoadX0", "StoreByte", "StoreHalf", "StoreWord",
    "StoreDouble",
}

# Native reader substrate shared by native chip rows and whole-chip Rust oracles. Reusing
# these types avoids creating a fresh CPU/register-reader hierarchy per oracle while keeping Rust
# arithmetic operation structs chip-private. Extend this set when a new canonical reader lands.
CHIP_ORACLE_SHARED_STRUCTS: Set[str] = {
    "CPUState", "RTypeReader", "ITypeReader", "JTypeReader", "ALUTypeReader",
    "RegisterAccessCols", "RegisterAccessTimestamp",
    # Native memory-access blocks nested in every load/store row.
    "MemoryAccessCols", "MemoryAccessTimestamp",
    # `ITypeReaderImmutable` operates on the `ITypeReader` row and so owns no struct of its own;
    # it is listed here for reader-roster uniformity (a no-op for struct reuse) and does its real
    # work via `CHIP_ORACLE_IMPORTED_HELPERS` below.
    "ITypeReaderImmutable",
}

# Generated helpers whose canonical operation/reader module is imported by every chip oracle that
# calls them. Do not embed a second namespace containing byte-for-byte duplicate functions. Keep this
# explicit: sharing a row struct alone does not imply that every Rust helper using it has a stable,
# reusable generated definition.
CHIP_ORACLE_IMPORTED_HELPERS: Set[str] = {
    "CPUState", "RTypeReader", "ITypeReader", "JTypeReader", "ALUTypeReader",
    "ITypeReaderImmutable",
}

# Helpers needed while rendering a self-contained chip oracle but no longer emitted as standalone
# verification artifacts. They remain in `OPERATIONS` solely so the discovery pass can embed their
# generated definitions inside the owning chip namespace.
CHIP_ONLY_HELPERS: Set[str] = {
    "SubOperation", "SubwOperation", "AddwOperation", "BitwiseOperation", "BitwiseU16Operation",
}

DEFAULT_SP1_DIR = "../sp1"
# The legacy Rust-to-Lean pipeline and dump checker share this provenance record.
_SP1_PROVENANCE = json.loads(
    (Path(__file__).resolve().parent / "scripts/provenance.json").read_text())["sp1"]["legacy"]
SP1_SEMANTIC_COMMIT = _SP1_PROVENANCE["semanticRevision"]
SP1_PINNED_COMMIT = _SP1_PROVENANCE["extractorRevision"]

# The only machine AIR files the extraction branch may touch. The checker below additionally
# verifies that every changed line in these files is an import or derive-attribute change.
EXTRACTOR_METADATA_FILES: Set[str] = {
    "crates/core/machine/src/alu/add_sub/add.rs",
    "crates/core/machine/src/alu/add_sub/addi.rs",
    "crates/core/machine/src/alu/add_sub/addw.rs",
    "crates/core/machine/src/alu/add_sub/sub.rs",
    "crates/core/machine/src/alu/add_sub/subw.rs",
    "crates/core/machine/src/alu/alu_x0.rs",
    "crates/core/machine/src/alu/bitwise/mod.rs",
    "crates/core/machine/src/alu/divrem/mod.rs",
    "crates/core/machine/src/alu/lt/mod.rs",
    "crates/core/machine/src/alu/mul/mod.rs",
    "crates/core/machine/src/alu/sll/mod.rs",
    "crates/core/machine/src/alu/sr/mod.rs",
    "crates/core/machine/src/control_flow/branch/columns.rs",
    "crates/core/machine/src/control_flow/jal/columns.rs",
    "crates/core/machine/src/control_flow/jalr/columns.rs",
    "crates/core/machine/src/memory/consistency/columns.rs",
    "crates/core/machine/src/memory/instructions/load/load_byte.rs",
    "crates/core/machine/src/memory/instructions/load/load_double.rs",
    "crates/core/machine/src/memory/instructions/load/load_half.rs",
    "crates/core/machine/src/memory/instructions/load/load_word.rs",
    "crates/core/machine/src/memory/instructions/load/load_x0.rs",
    "crates/core/machine/src/memory/instructions/store/store_byte.rs",
    "crates/core/machine/src/memory/instructions/store/store_double.rs",
    "crates/core/machine/src/memory/instructions/store/store_half.rs",
    "crates/core/machine/src/memory/instructions/store/store_word.rs",
    "crates/core/machine/src/utype/mod.rs",
}
# Trusted extraction implementation. These paths contain the constraint compiler, shape projection,
# and symbolic IR/rendering code. They are authenticated by the exact extraction-branch commit and
# reviewed as trusted tooling; matching this allowlist does NOT prove their changes semantically
# inert. Keep this surface distinct from the line-checked machine AIR files above.
TRUSTED_EXTRACTOR_PREFIXES: Tuple[str, ...] = (
    "crates/core/compiler/",
    "crates/hypercube/src/ir/",
)
TRUSTED_EXTRACTOR_FILES: Set[str] = {
    # The workspace manifest gains the vendored witgen-interp member; the lockfile follows.
    "Cargo.toml",
    "Cargo.lock",
    "crates/derive/src/into_shape.rs",
}
EXTRACTED_DIR = os.path.join("SP1Clean", "Extracted")
COMMON_IMPORTS = """import SP1Clean.Math.Word
import SP1Clean.Extracted.ExtractionDSL
import Clean.Utils.Tactics.ProvableStructDeriving"""

FOOTER = "end SP1Clean.Extracted\n"

# Auto-generated modules pay a real per-declaration linter-interpretation tax (mathlib/batteries
# TacticAnalysis, UnusedTactic, UnreachableTactic, UnnecessarySeqFocus, …) for warnings nobody
# reads — the files are regenerated, never hand-edited. `linter.all` is core's master switch;
# it must be set per file (the package-level `-D` form is rejected, see lakefile.toml).
LINTERS_OFF = "set_option linter.all false  -- auto-generated: skip linters"

_STRUCT_RE = re.compile(r"^\s*structure\s+([A-Za-z_][A-Za-z0-9_]*)\b", re.MULTILINE)
_BYTE_OPCODE_RE = re.compile(
    r"\.byte \(ByteOpcode\.ofNat ([A-Za-z_][A-Za-z0-9_]*|[0-9]+)\)"
)


# ── Compiler driver ─────────────────────────────────────────────────────────────────────────

def run_constraint_compiler(
    sp1_dir: str,
    chip: str = None,
    operation: str = None,
    public_values: bool = False,
    reuse: Sequence[str] = (),
) -> str:
    """Run the sp1-constraint-compiler and return its stdout. Pass `operation` to extract an
    operation standalone (searched across all chips), `chip` to extract a table, or
    `public_values=True` for `MachineRecord::eval_public_values`. Exactly one target may be selected.
    The only emitted Lean artifact is the two-list `asserts`/`interactions` anchor form."""
    if sum((chip is not None, operation is not None, public_values)) != 1:
        raise ValueError("select exactly one of chip, operation, or public_values")
    cmd = ["cargo", "run", "-q", "-p", "sp1-constraint-compiler", "--bin", "sp1-constraint-compiler",
           "--", "--format", "lean"]
    if chip is not None:
        cmd += ["--chip", chip]
    if operation is not None:
        cmd += ["--operation", operation]
    if public_values:
        cmd += ["--public-values"]
    for name in reuse:
        cmd += ["--reuse-struct", name]
    result = subprocess.run(cmd, cwd=sp1_dir, capture_output=True, text=True)
    if result.returncode != 0:
        target = ("public values" if public_values else
                  operation if operation is not None else f"{chip} (table)")
        raise RuntimeError(f"compiler failed for {target}:\n{result.stderr}")
    return result.stdout


def run_profile_manifest(sp1_dir: str) -> dict:
    """Read the machine cluster and row-width manifest from `RiscvAir::machine()` itself."""
    cmd = ["cargo", "run", "-q", "-p", "sp1-constraint-compiler", "--bin",
           "sp1-constraint-compiler", "--", "--profile-manifest"]
    result = subprocess.run(cmd, cwd=sp1_dir, capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(f"profile-manifest extraction failed:\n{result.stderr}")
    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError(f"profile-manifest output is not JSON:\n{result.stdout}") from error


def _emitted_structs(body: str) -> List[str]:
    """The column-struct names a compiler fragment emits (in source order)."""
    return _STRUCT_RE.findall(body)


def _preserve_raw_byte_opcodes(body: str) -> str:
    """Keep the byte interaction's opcode as the raw field expression emitted by Rust.

    The pinned compiler's Lean printer historically wrapped this value in
    `ByteOpcode.ofNat`. Lean's enum decoder maps every out-of-range value to `.Range`, so that
    wrapper is not an injective representation of the upstream AIR tuple. The semantic Rust AIR
    and Clean's byte channel both carry the raw field value. Strip only the printer wrapper here
    and fail loudly if a future printer emits a shape this reviewed rewrite does not recognize.
    """
    body = _BYTE_OPCODE_RE.sub(r".byte \1", body)
    if "ByteOpcode.ofNat" in body:
        raise ValueError(
            "unrecognized ByteOpcode.ofNat in compiler output; update the raw-opcode rewrite"
        )
    return body


# ── Ownership resolution ────────────────────────────────────────────────────────────────────

def _default_owner(struct: str) -> str:
    """Owner of a struct under the default rules (no native owner)."""
    if struct in OPERATIONS:
        return struct
    if struct.endswith("Cols") and struct[:-len("Cols")] in [*CHIPS, *SYSTEM_TABLES]:
        return struct[:-len("Cols")]
    return None


def resolve_ownership(emitted: Dict[str, List[str]]) -> Dict[str, str]:
    """Build the global struct→owning-module map, failing loudly on unresolved collisions.

    `emitted` maps each module name to the structs it emits with no reuse."""
    owner: Dict[str, str] = {}
    native = native_structs()
    for struct in {s for structs in emitted.values() for s in structs}:
        if struct in native:
            owner[struct] = native[struct][0]
            continue
        default = _default_owner(struct)
        if default is not None:
            owner[struct] = default
            continue
        emitters = [m for m, structs in emitted.items() if struct in structs]
        if len(emitters) == 1:
            owner[struct] = emitters[0]
        else:
            # A struct emitted by several modules with no native or operation owner (e.g.
            # `MemoryAccessColsU8`, which only ever appears nested in the Load/Store chips and in
            # no standalone operation). Make the first emitter — in registry order, operations
            # before chips — the canonical owner; the others skip it and import that module. This
            # keeps exactly one definition (no duplicate `structure` across the shared namespace).
            order = {
                name: i for i, name in enumerate([*OPERATIONS, *CHIPS, *SYSTEM_TABLES])
            }
            owner[struct] = min(emitters, key=lambda m: order.get(m, len(order)))
    return owner


def _import_module(owner: str) -> str:
    """The `Extracted.<…>` module file name for an owner. A chip cannot be an importable struct
    definition site (the legacy flat `<Chip>Chip.lean` modules were retired with the whole-chip
    oracle migration), so a chip owner is a registry error — give the shared type a native owner instead."""
    if owner in CHIPS:
        raise ValueError(
            f"struct owner {owner} is a chip; chips no longer own importable structs")
    if owner in SYSTEM_TABLES:
        return f"SystemOracle.{owner}"
    return owner


_CALL_RE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\.(?:asserts|interactions|value)\b")


def reuse_for(
    module: str, emitted_structs: Sequence[str], owner: Dict[str, str], body: str
) -> Tuple[List[str], List[str]]:
    """For `module`, return (`--reuse-struct` skip names, import module names).

    Imports come from two sources, since a composed module references sub-modules two ways:
      * **column structs** it emits but another module owns (skipped via `--reuse-struct`, the
        owner imported so the struct *type* resolves); and
      * **`<Sub>.asserts` / `.interactions` / `.value` calls** in its body (the sub-module imported
        so the *function* resolves). These can differ — e.g. `MulOperation` nests the
        `U16toU8Operation` struct (owned by `U16toU8OperationUnsafe`) yet calls
        `U16toU8OperationSafe.asserts`, so both modules must be imported."""
    skips: List[str] = []
    imports: List[str] = []
    seen: Set[str] = set()

    def add_import(m: str) -> None:
        if m != module and m not in seen:
            seen.add(m)
            imports.append(m)

    for struct in emitted_structs:
        o = owner[struct]
        if o != module:
            skips.append(struct)
            add_import(_import_module(o))
    for called in _CALL_RE.findall(body):
        if called in KNOWN_OPERATIONS:
            add_import(called)
    return skips, imports


# ── Rendering ───────────────────────────────────────────────────────────────────────────────

# `ProvableStruct.components : List WithProvableType` is built from a `[field, Word, …]` list of
# bare TypeMaps coerced element-wise via `CoeDep TypeMap → WithProvableType`. For a struct with many
# fields, Lean 4.28's large-list-literal elaboration *chunks* the `[…]` literal, and the coercion
# stops propagating across chunk boundaries (the tail stays a bare `List TypeMap`), so `deriving
# ProvableStruct` fails — it surfaces as an "Application type mismatch … List (Type → Type) vs
# List WithProvableType". Only `DivRemCols` (45 fields) is large enough to trip this; every other
# emitted struct stays under the threshold and derives fine. For an over-threshold struct we replace
# `deriving ProvableStruct` with an explicit instance whose `components` are *pre-wrapped*
# `⟨T, inferInstance⟩` records (no coercion → the literal is type-uniform and chunks safely). The
# `toComponents`/`fromComponents` mirror the Clean deriver verbatim, so the instance is identical to
# what the deriver would have produced (the lawfulness proofs come from the class defaults).
_LARGE_STRUCT_FIELD_THRESHOLD = 40

_DERIVE_STRUCT_RE = re.compile(
    r"^structure (\w+) \(F : Type\) where\n((?:[ \t]+\w+ : .+\n)+)deriving ProvableStruct$",
    re.MULTILINE,
)


def native_structs(directory: Path = None) -> Dict[str, Tuple[str, str]]:
    """Read shared native column declarations; the extractor never writes their definitions."""
    result = {}
    directory = directory or Path(__file__).resolve().parent / "SP1Clean/Circuits/Types"
    for path in sorted(directory.glob("*.lean")):
        # Documentation is not part of a column layout. Nested block comments are deliberately
        # not consumed by this small parser: unsupported syntax must fail the layout comparison.
        source = re.sub(r"^[ \t]*/--(?:(?!/-|-/).)*-/[ \t]*(?:\n|$)", "",
                        path.read_text(), flags=re.M | re.S)
        declarations = list(_DERIVE_STRUCT_RE.finditer(source))
        unsupported = set(_STRUCT_RE.findall(source)) - {match[1] for match in declarations}
        if unsupported:
            raise ValueError(f"{path}: unsupported native column declarations: {sorted(unsupported)}")
        for match in declarations:
            name, fields = match.group(1, 2)
            if name in result:
                raise ValueError(f"duplicate native column type: {name}")
            result[name] = (f"SP1Clean.Circuits.Types.{path.stem}", fields)
    if not result:
        raise ValueError("no native column types found")
    return result


def validate_native_layouts(discovery: Dict[str, str], native: Dict[str, Tuple[str, str]],
                            complete: bool) -> None:
    """Compare independently extracted Rust fields with native declarations before reuse.

    Whitespace is immaterial; names, order, nesting and vector lengths must agree. This is a
    migration check on Rust reflection output, not a proof of the reflection implementation.
    """
    seen = set()
    for module, body in discovery.items():
        for match in _DERIVE_STRUCT_RE.finditer(body):
            name, fields = match.group(1, 2)
            if name in native:
                if fields.split() != native[name][1].split():
                    raise ValueError(f"{module}: Rust layout of {name} differs from native columns")
                seen.add(name)
    if complete and (missing := set(native) - seen):
        raise ValueError(f"native column layouts were not checked against Rust: {sorted(missing)}")


def _render_imports(modules: Sequence[str]) -> str:
    return "".join(f"import {m if m.startswith('SP1Clean.') else 'SP1Clean.Extracted.' + m}\n"
                   for m in modules)


def _native_open(modules: Sequence[str]) -> str:
    return ("open SP1Clean.Circuits.Types\n"
            if any(m.startswith("SP1Clean.Circuits.Types.") for m in modules) else "")


def _component_of(ty: str) -> str:
    """Map a Lean field type to its `ProvableStruct` component TypeMap (mirrors the Clean deriver's
    `analyzeFieldType`): `F` → `field`, `(Vector F n)` → `fields n`, `(M F)` → `M`."""
    ty = ty.strip()
    if ty == "F":
        return "field"
    inner = ty.strip("()").strip()
    if inner.startswith("Vector F "):
        return "fields " + inner.split()[-1]
    return inner.rsplit(" F", 1)[0]


def _explicit_provable_struct(name: str, fields: Sequence[Tuple[str, str]]) -> str:
    """The struct def (sans `deriving`) plus an explicit `ProvableStruct` instance — see the note
    above `_LARGE_STRUCT_FIELD_THRESHOLD`."""
    comps = ", ".join(f"⟨{_component_of(ty)}, inferInstance⟩" for _, ty in fields)
    names = [n for n, _ in fields]
    cons = ".nil"
    for n in reversed(names):
        cons = f"(.cons {n} {cons})"
    cons = cons[1:-1]  # drop the now-redundant outermost parens
    destr = "⟨" + ", ".join(names) + "⟩"
    mk = f"{name}.mk " + " ".join(names)
    # `cons` is both the `toComponents` result term and the `fromComponents` pattern (textually
    # identical — a chain of `.cons <field>` ending in `.nil`).
    return (
        f"structure {name} (F : Type) where\n"
        + "".join(f"  {n} : {ty}\n" for n, ty in fields)
        + f"\ninstance : ProvableStruct {name} where\n"
        f"  components := [{comps}]\n"
        f"  toComponents := fun {destr} => {cons}\n"
        f"  fromComponents := fun ({cons}) => {mk}"
    )


def _expand_large_derives(body: str) -> str:
    """Replace `deriving ProvableStruct` with an explicit instance for any emitted struct whose field
    count exceeds the chunking threshold. A no-op for every current struct except `DivRemCols`."""
    def repl(m: "re.Match[str]") -> str:
        name, fieldblock = m.group(1), m.group(2)
        fields: List[Tuple[str, str]] = []
        for line in fieldblock.splitlines():
            line = line.strip()
            if not line:
                continue
            fname, fty = line.split(" : ", 1)
            fields.append((fname.strip(), fty.strip()))
        # `provable_struct_eval_lemmas` (ToClean/Circuit/StructEvalLemmas.lean): the per-field
        # `eval_<f>` bridge lemmas every hand-written struct also declares, so `circuit_norm` can
        # relate `(ProvableStruct.eval env s).f` to `Expression.eval env s.f` on an opaque `s`.
        if len(fields) <= _LARGE_STRUCT_FIELD_THRESHOLD:
            return m.group(0) + f"\nprovable_struct_eval_lemmas {name}"
        return _explicit_provable_struct(name, fields) + f"\n\nprovable_struct_eval_lemmas {name}"
    return _DERIVE_STRUCT_RE.sub(repl, body)


# System tables whose emitted `let` chains are hoisted into one top-level `private def` per binding
# (`_hoist_let_chains`). Only tables whose lists are consumed OPAQUELY qualify: `Global`'s
# `asserts`/`interactions` are only ever applied as `@[irreducible]` values (`Faithful/CoreAIR`),
# whereas the chip oracles' lists are unfolded element-wise by the `ChipFaithful` proofs and must
# keep the emitter's shape. `Global` is the sole member because it is the sole pathological case:
# the Poseidon-style closure makes its parts 535–1 649 nested `let`s, and nested-`let` elaboration
# is super-linear (measured 2026-09-22: 535 → 2 s, 668 → 4 s, 1 111 → 18 s, 1 649 → 30 s and 14 GB;
# hoisted, the 1 649-binding part elaborates in 0.9 s and 2.5 GB). Finer entry chunking cannot
# help there — every chunk holding a Poseidon output re-derives its ≈ 1 300 bindings.
HOISTED_LET_CHAIN_TABLES = frozenset({"Global"})

_LET_CHAIN_DEF_RE = re.compile(
    r"^(?P<attr>@\[irreducible\] def )(?P<name>\S+)(?P<sig>(?:[^\n]*\n)*?)  : List F :=\n"
    r"(?P<lets>(?:  let E\d+ : F := [^\n]*\n)+)"
    r"  \[\n(?P<entries>(?:    E\d+,\n)*)  \]",
    re.M,
)
_LET_REF_RE = re.compile(r"\b(E\d+)\b")


def _hoist_let_chains(body: str) -> str:
    """Rewrite every `@[irreducible] def X <binders> : List F := let E0 := …; …; [E_i, …]` block whose
    body is a `let` chain into one `private def X_E<k> <binders> : F := …` per binding (references to
    earlier bindings become applications to the same binder names) followed by
    `@[irreducible] def X <binders> : List F := [X_E<i> <binders>, …]` (each hoisted def carries
    `@[nolint unusedArguments]`: the binder block is uniform, the individual bindings are not).
    Definitionally the same list
    (each hoisted def zeta-reduces to the original binding); elaboration goes from super-linear in
    the chain length to linear, and the recursion-depth/heartbeat overrides the chains needed go
    with them. See HOISTED_LET_CHAIN_TABLES."""
    def repl(m: "re.Match[str]") -> str:
        name, sig = m.group("name"), m.group("sig")
        binder_names = re.findall(r"^  \((\w+) :", sig, re.M)
        args = " ".join(binder_names)
        lets = re.findall(r"^  let (E\d+) : F := ([^\n]*)$", m.group("lets"), re.M)
        entries = re.findall(r"^    (E\d+),$", m.group("entries"), re.M)
        header = sig.rstrip("\n")
        # one line per hoisted binding: the binder block joined with single spaces
        flat = " ".join(part.strip() for part in header.split("\n") if part.strip())
        out: List[str] = []
        for binding, expr in lets:
            expr = _LET_REF_RE.sub(lambda r: f"({name}_{r.group(1)} {args})", expr)
            # Every hoisted binding takes the part's whole binder block so the applications stay
            # uniform; most bindings use only some of it (a constant fold uses none), so the
            # environment linter's `unusedArguments` would fire on the majority of them.
            out.append(f"@[nolint unusedArguments]\nprivate def {name}_{binding} {flat} : F := {expr}")
        items = ", ".join(f"{name}_{e} {args}" for e in entries)
        out.append(f"\n{m.group('attr')}{name}{header}\n  : List F :=\n  [{items}]")
        return "\n".join(out)
    return _LET_CHAIN_DEF_RE.sub(repl, body)


def _sanity_gate(label: str, body: str) -> None:
    """The emitted module must carry the two-list `asserts` / `interactions` defs; if it emits a
    struct it must derive `ProvableStruct` (or carry an explicit `instance : ProvableStruct` from
    `_expand_large_derives`). (A pure-defs module that reuses every struct — e.g.
    `U16toU8OperationSafe` — legitimately emits no `structure`.)"""
    for needle in ("def asserts", "def interactions"):
        if needle not in body:
            raise ValueError(f"compiler output for {label} missing '{needle}' — refusing to write")
    if ("structure " in body and "deriving ProvableStruct" not in body
            and "instance : ProvableStruct" not in body):
        raise ValueError(f"compiler output for {label} emits a struct without 'deriving ProvableStruct'")


def _header(import_modules: Sequence[str], doc: str) -> str:
    """Clean-native module header: common imports, reused-module imports, doc, namespace."""
    reuse_imports = _render_imports(import_modules)
    return (
        COMMON_IMPORTS + "\n" + reuse_imports + "\n"
        + doc + "\n\n"
        + LINTERS_OFF + "\n\n"
        + "namespace SP1Clean.Extracted\nopen SP1Clean\n" + _native_open(import_modules)
    )


def render(operation: str, import_modules: Sequence[str], body: str) -> str:
    """Wrap an operation's compiler body in the clean-native module header/footer."""
    body = _preserve_raw_byte_opcodes(body)
    body = _bump_constraints_heartbeats(body.strip(), f"operation:{operation}")
    body = _expand_large_derives(body)
    _sanity_gate(operation, body)
    reused = (f"reusing the {', '.join(import_modules)} column-struct module(s), imported above"
              if import_modules else "reusing no column-struct modules")
    doc = (
        f"/-! # AUTO-GENERATED — do not edit by hand.\n\n"
        f"Generated by `update_extracted.py` from the `sp1-constraint-compiler`\n"
        f"(`--operation {operation} --format lean`). Contains SP1's `{operation}` operation\n"
        f"constraints ({reused}). Regenerate\n"
        f"with `SP1_DIR=… python3 update_extracted.py`; the faithfulness anchor lives under\n"
        f"`SP1Clean/Faithful/`. -/"
    )
    return _header(import_modules, doc) + "\n" + body + "\n\n" + FOOTER


# Measured elaboration-budget overrides for generated definitions, keyed by
# "<scope>:<name>:<namespace>.<def>". **Default is no override at all.**
#
# Essentially no generated definition needs one: the elaborator handles the entire emitted AIR at Lean's
# plain default, across chip oracles, system tables and public values alike. **Never emit a blanket
# bump.** If a definition genuinely fails, ladder it and add one entry here with the bracket recorded
# beside it.
#
# Size is not a predictor and must not be used as one. The four largest generated definitions in the
# tree (1649/1111/668/535 `let`s) are not in this table, and a *zero*-`let` `interactions` definition
# does not need an override either. Measure the definition that fails; do not extrapolate from its
# neighbours.
#
# To re-derive this table from scratch: strip every override, run a full `lake build`, and add back only
# what fails — iterating, because a heartbeat failure can mask a recursion failure in the same file.
CONSTRAINT_HEARTBEAT_OVERRIDES: Dict[str, int] = {
    # The single measured survivor. It fails in `«LCNF simp»` — the CODE GENERATOR, not elaboration —
    # which is why it is the only one: the elaborator handles every generated def at the default, and
    # only codegen on the largest chip oracle does not.
    #
    # ⚠ Do NOT size this by `let` count. An earlier revision of this comment called it a "~466-`let`
    # chain"; it is **386**. The 466/468 figure belongs to `MulOperation.asserts` — a *different*
    # definition in this same file, which carries no override and passes at the plain default. So the
    # larger definition is the cheap one: `let` count does not predict this cost. The real
    # discriminator is a single 13 KB line of twenty sub-calls, 45% of the definition's text.
    # Ladder: 200000 FAIL (`«LCNF simp»`) / 210000 ok → floor (200000, 210000], i.e. barely over the
    # default. Set to 400000 for ~2x margin because codegen cost is less predictable across toolchain
    # bumps than elaboration; the previous blanket value was 8000000, ~40x over.
    "chip_oracle:DivRem:DivRemCols.asserts": 400000,
}


def _bump_constraints_heartbeats(body: str, scope: str) -> str:
    """Prefix a generated `@[irreducible] def` with an elaboration-budget override **only** where one
    has been measured to be necessary — see `CONSTRAINT_HEARTBEAT_OVERRIDES`. Definitions absent from
    that table (the overwhelming majority) are emitted with no override, matching Lean's default.

    `scope` identifies the emitting renderer and subject, e.g. `"chip_oracle:DivRem"`; the table key
    appends the **innermost** enclosing namespace and the definition name, so a bump lands on exactly
    one definition rather than on every def in a module. The innermost component is used deliberately:
    the module's outer `namespace SP1Clean.Extracted.<X>` is contributed by the header, which is
    prepended *after* this runs, so a fully-qualified key would not match at generation time."""
    out: List[str] = []
    stack: List[str] = []
    for line in body.split("\n"):
        opened = re.match(r"namespace\s+(\S+)", line)
        if opened:
            stack.append(opened.group(1))
        elif re.match(r"end\s+\S+", line) and stack:
            stack.pop()
        if line.startswith("@[irreducible] def "):
            name = line.split()[2]
            qualified = f"{stack[-1]}.{name}" if stack else name
            value = CONSTRAINT_HEARTBEAT_OVERRIDES.get(f"{scope}:{qualified}")
            if value is not None:
                out.append(f"set_option maxHeartbeats {value} in")
        out.append(line)
    return "\n".join(out)


# Measured recursion-depth overrides for generated AIR definitions, keyed like
# CONSTRAINT_HEARTBEAT_OVERRIDES as "<scope>:<innermost-namespace>.<def>". Default: NO override.
#
# `render_system_table` and `render_public_values` emit an override only where this table names one.
# **Never emit a blanket bump.** No generated system-oracle module needs one today: `Global`'s four
# `assertsPart*` definitions used to recurse past Lean's 512 default (floor (1200, 2000]) until their
# `let` chains were hoisted (`_hoist_let_chains`); the table stays as the mechanism for the next case.
SYSTEM_RECDEPTH_OVERRIDES: Dict[str, int] = {}


def _bump_recdepth(body: str, scope: str) -> str:
    """Prefix a generated `@[irreducible] def` with a recursion-depth override only where one has
    been measured to be necessary -- see `SYSTEM_RECDEPTH_OVERRIDES`. Mirrors
    `_bump_constraints_heartbeats`, including the innermost-namespace keying (the module's outer
    namespace comes from the header, which is prepended after this runs)."""
    out: List[str] = []
    stack: List[str] = []
    for line in body.split("\n"):
        opened = re.match(r"namespace\s+(\S+)", line)
        if opened:
            stack.append(opened.group(1))
        elif re.match(r"end\s+\S+", line) and stack:
            stack.pop()
        if line.startswith("@[irreducible] def "):
            name = line.split()[2]
            qualified = f"{stack[-1]}.{name}" if stack else name
            value = SYSTEM_RECDEPTH_OVERRIDES.get(f"{scope}:{qualified}")
            if value is not None:
                out.append(f"set_option maxRecDepth {value} in")
        out.append(line)
    return "\n".join(out)


def render_system_table(
    table: str, import_modules: Sequence[str], body: str
) -> str:
    """Wrap a non-instruction table's exact flat-row assertion and interaction lists."""
    # The list-only backend already chunks large AIR bodies into irreducible parts.  Keep only the
    # recursion allowance needed to elaborate the generated `let` chains; adding one heartbeat
    # override per data definition would hide a chunk-size regression from the repository's
    # no-new-heartbeat audit gate.
    body = _preserve_raw_byte_opcodes(body)
    if table in HOISTED_LET_CHAIN_TABLES:
        body = _hoist_let_chains(body)
    body = _bump_recdepth(body.strip(), f"system:{table}")
    body = _expand_large_derives(body)
    _sanity_gate(f"{table} (system table)", body)
    reused = (f"Reuses the {', '.join(import_modules)} helper module(s)."
              if import_modules else "Reuses no helper modules.")
    doc = (
        f"/-! # AUTO-GENERATED system-table Rust AIR oracle — do not edit by hand.\n\n"
        f"Generated by `update_extracted.py` from `sp1-constraint-compiler --chip {table} "
        f"--format lean`. Contains every `{table}` main-trace column in upstream index order, "
        f"the complete per-row `assertZero` list, and the complete interaction list. The flat "
        f"vector deliberately avoids inventing semantic field names in the extraction layer; "
        f"audited adapters may name selected indices above this anchor. {reused} -/"
    )
    return _header(import_modules, doc) + "\n" + body + "\n\n" + FOOTER


def render_public_values(body: str) -> str:
    """Wrap `MachineRecord::eval_public_values`, the non-row AIR block in every Core shard."""
    body = _preserve_raw_byte_opcodes(body)
    body = _bump_recdepth(body.strip(), "public_values")
    _sanity_gate("machine public values", body)
    doc = (
        "/-! # AUTO-GENERATED Core public-values AIR oracle — do not edit by hand.\n\n"
        "Generated from the pinned `ExecutionRecord::eval_public_values` through the list-only "
        "constraint compiler mode. This is the complete machine-level assertion and interaction "
        "block; it is not attached to a table row and takes the exact 160-element public-values "
        "vector directly. -/"
    )
    return _header([], doc) + "\n" + body + "\n\n" + FOOTER


def _chip_helper_order(chip: str, chip_body: str, discovery: Dict[str, str]) -> List[str]:
    """Dependency-first order of generated helper definitions called by one chip expression."""
    ordered: List[str] = []
    visiting: Set[str] = set()
    done: Set[str] = set()

    def visit(name: str) -> None:
        if name in done:
            return
        if name in visiting:
            raise ValueError(f"cyclic generated helper dependency while rendering {chip}: {name}")
        if name not in discovery:
            raise ValueError(
                f"self-contained oracle for {chip} calls {name}, but its operation body was not "
                "discovered (include it in OPERATIONS/EXTRACT_ONLY)")
        visiting.add(name)
        for dep in _CALL_RE.findall(discovery[name]):
            if dep != name and dep in discovery:
                visit(dep)
            elif dep != name and dep[:1].isupper():
                raise ValueError(
                    f"self-contained oracle for {chip} needs generated helper {dep}, but its body "
                    "was not discovered (include it in OPERATIONS/EXTRACT_ONLY)")
        visiting.remove(name)
        done.add(name)
        ordered.append(name)

    for helper in _CALL_RE.findall(chip_body):
        if helper in discovery:
            visit(helper)
        elif helper[:1].isupper():
            raise ValueError(
                f"self-contained oracle for {chip} calls {helper}, but its operation body was not "
                "discovered (include it in OPERATIONS/EXTRACT_ONLY)")
    return ordered


def _without_generated_structures(body: str) -> str:
    """Drop struct declarations from a helper body; the chip's no-reuse row shape owns them."""
    return _DERIVE_STRUCT_RE.sub("", body).strip()


def _prune_transitive_imports(
    imports: Sequence[str], module_imports: Dict[str, Sequence[str]]
) -> List[str]:
    """Drop imports that another import already provides transitively (Lean imports are transitive).

    E.g. a load/store oracle reuses `RegisterAccessCols` (owned by `RTypeReader`) through its
    `ITypeReader` row, but the generated `ITypeReader` module itself imports `RTypeReader`, so a
    direct `RTypeReader` import would be redundant. Only modules whose own import lists this run
    discovered (`module_imports`) provide anything; an unknown module provides nothing, so its
    dependents' imports are conservatively kept."""
    def closure(module: str, seen: Set[str]) -> Set[str]:
        for dep in module_imports.get(module, ()):
            if dep not in seen:
                seen.add(dep)
                closure(dep, seen)
        return seen

    provided: Set[str] = set()
    for module in imports:
        provided |= closure(module, set())
    return [module for module in imports if module not in provided]


def render_chip_oracle(
    chip: str, chip_body: str, discovery: Dict[str, str], import_modules: Sequence[str],
    module_imports: Dict[str, Sequence[str]],
) -> str:
    """Render one chip-namespaced Rust AIR oracle.

    The compiler fragment reuses canonical reader structs but deliberately calls helper definitions
    such as `AddOperation.asserts`. Embed chip-private helpers dependency-first into the same namespace,
    stripping their duplicate structs. Calls to canonical generated reader helpers are qualified back
    to their imported module instead of embedding a duplicate namespace. This keeps Rust's generated
    factoring available to Lean reduction without making operation modules part of the chip's theorem
    surface or cloning the shared reader substrate.
    """
    # SP1's Rust column structs are named `<Chip>Cols` for most chips but `<Chip>Columns` for the
    # control-flow/U-type chips (Jal/Jalr/UType); accept whichever the compiler emitted.
    markers = (f"namespace {chip}Cols", f"namespace {chip}Columns")
    marker = next((m for m in markers if m in chip_body), None)
    if marker is None:
        raise ValueError(f"compiler output for {chip} missing one of `{markers}`")
    before, found, after = chip_body.partition(marker)
    helpers = _chip_helper_order(chip, chip_body, discovery)
    embedded_helpers = [h for h in helpers if h not in CHIP_ORACLE_IMPORTED_HELPERS]
    shared_helpers = [h for h in helpers if h in CHIP_ORACLE_IMPORTED_HELPERS]
    # An imported helper's module is usually already present via shared-struct ownership (CPUState,
    # the reader modules). A helper that owns no struct — `ITypeReaderImmutable` operates on the
    # `ITypeReader` row — must still be imported so its qualified `asserts`/`interactions` calls
    # resolve; without this the oracle would reference an unimported module (or silently re-embed).
    import_modules = list(import_modules) + [
        h for h in shared_helpers if h not in import_modules
    ]
    native_open = _native_open(import_modules)
    import_modules = _prune_transitive_imports(import_modules, module_imports)
    helper_defs = "\n\n".join(
        _without_generated_structures(discovery[h]) for h in embedded_helpers
    )
    body = before.rstrip() + "\n\n" + helper_defs + "\n\n" + marker + after
    for helper in sorted(CHIP_ORACLE_IMPORTED_HELPERS):
        body = re.sub(
            rf"(?<![A-Za-z0-9_.]){re.escape(helper)}\.(asserts|interactions)\b",
            rf"SP1Clean.Extracted.{helper}.\1",
            body,
        )
    body = _preserve_raw_byte_opcodes(body)
    body = _bump_constraints_heartbeats(body.strip(), f"chip_oracle:{chip}")
    body = _expand_large_derives(body)
    _sanity_gate(f"{chip} (self-contained chip oracle)", body)
    helper_list = ", ".join(embedded_helpers) if embedded_helpers else "no private helpers"
    imported_list = ", ".join(import_modules) if import_modules else "no shared modules"
    doc = (
        f"/-! # AUTO-GENERATED whole-chip Rust AIR oracle — do not edit by hand.\n\n"
        f"Generated by `update_extracted.py` from `sp1-constraint-compiler --chip {chip} --format lean`.\n"
        f"Contains the complete Rust `{chip}` row shape, `assertZero` list, and interaction list,\n"
        f"reusing native columns and generated reader helpers imported above ({imported_list}).\n"
        f"The compiler's chip-private helper definitions ({helper_list}) are embedded in this namespace\n"
        f"rather than imported as operation-level verification artifacts. Regenerate with\n"
        f"`SP1_DIR=… python3 update_extracted.py`. -/"
    )
    return (
        COMMON_IMPORTS + "\n"
        + _render_imports(import_modules)
        + "\n" + doc + "\n\n" + LINTERS_OFF + "\n\n"
        + f"namespace SP1Clean.Extracted.{chip}Oracle\n"
        + "open SP1Clean\n" + native_open + "\n" + body + "\n\n"
        + f"end SP1Clean.Extracted.{chip}Oracle\n"
    )


def _write(out_path: str, content: str) -> None:
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, "w") as f:
        f.write(content)
    print(f"  ✓ Wrote {out_path}")


def render_provenance() -> str:
    """Render the single source of truth for checked-in extraction provenance."""
    return (
        "/-! # AUTO-GENERATED extraction provenance — do not edit by hand.\n\n"
        "The semantic revision is unmodified upstream SP1. The extractor revision is an audited\n"
        "descendant whose machine-source diff is reflection metadata only; exporter implementation\n"
        "changes live outside the AIR definitions. Regenerate with `update_extracted.py`. -/\n\n"
        + LINTERS_OFF + "\n\n"
        "namespace SP1Clean.Extracted\n\n"
        "/-- Exact two-revision boundary behind every checked-in extracted artifact. -/\n"
        "structure ExtractionProvenance where\n"
        "  semanticRevision : String\n"
        "  extractorRevision : String\n"
        "deriving DecidableEq, Repr\n\n"
        "/-- Provenance validated by the generator before it writes any AIR artifact. -/\n"
        "def checkedInProvenance : ExtractionProvenance where\n"
        f"  semanticRevision := \"{SP1_SEMANTIC_COMMIT}\"\n"
        f"  extractorRevision := \"{SP1_PINNED_COMMIT}\"\n\n"
        "end SP1Clean.Extracted\n"
    )


# ── Opcode-table pass ───────────────────────────────────────────────────────────────────────
# The instruction-alphabet anchor: SP1's `Opcode` enum (variant name → `#[repr(u8)]`
# discriminant) is the value every chip commits on the Program bus, and
# `SP1Clean/Model/Opcode.lean` hand-mirrors it. Extracting the table makes that mirror
# machine-checked (`opcodeTable_matchesExtracted`, `SP1Clean/FormalModel/OpcodeTable.lean`)
# instead of hand-verified. Like the manifest writers this is a text-level parse, not a compiler
# run — and it reads the file at `SP1_SEMANTIC_COMMIT` via `git show`, so it is independent of the
# checkout's working state and reproducible at the pin.

_OPCODE_VARIANT_RE = re.compile(r"^\s{4}([A-Z][A-Za-z0-9_]*)\s*=\s*(\d+),\s*$")


def read_opcode_table(sp1_dir: str) -> List[Tuple[str, int]]:
    """Parse the `pub enum Opcode` block of `crates/core/executor/src/opcode.rs` at the pinned
    semantic revision into ordered `(variant name, discriminant)` pairs. Fails loudly on any
    shape drift (missing enum, missing `#[repr(u8)]`, no variants, or non-consecutive
    discriminants)."""
    source = _git_output(
        sp1_dir, ["show", f"{SP1_SEMANTIC_COMMIT}:crates/core/executor/src/opcode.rs"])
    marker = "pub enum Opcode {"
    start = source.find(marker)
    if start == -1:
        raise SystemExit("opcode.rs: `pub enum Opcode {` not found — update the opcode parser")
    if not source[:start].rstrip().endswith("#[repr(u8)]"):
        raise SystemExit("opcode.rs: `#[repr(u8)]` no longer directly precedes `pub enum Opcode` "
                         "— the discriminant table would not be the committed u8 value")
    end = source.find("\n}", start)
    if end == -1:
        raise SystemExit("opcode.rs: unterminated `pub enum Opcode` block")
    entries = [
        (match.group(1), int(match.group(2)))
        for line in source[start + len(marker):end].splitlines()
        if (match := _OPCODE_VARIANT_RE.match(line))
    ]
    if not entries:
        raise SystemExit("opcode.rs: no `NAME = N,` variants parsed — update the opcode parser")
    if [value for _, value in entries] != list(range(len(entries))):
        raise SystemExit(f"opcode.rs: discriminants are not consecutive from 0: {entries}")
    return entries


def render_opcode_table(entries: Sequence[Tuple[str, int]]) -> str:
    """Render the extracted `Opcode` discriminant table as `Extracted/OpcodeTable.lean`."""
    rows = "\n".join(f'  ⟨"{name}", {value}⟩,' for name, value in entries)
    return (
        "import SP1Clean.Extracted.Provenance\n\n"
        "/-! # AUTO-GENERATED SP1 `Opcode` discriminant table — do not edit by hand.\n\n"
        "Parsed by `update_extracted.py` out of `crates/core/executor/src/opcode.rs` at the pinned\n"
        "semantic revision (`checkedInProvenance.semanticRevision`, read via `git show`): the\n"
        "variant name → `#[repr(u8)]` discriminant table, i.e. the opcode value each chip commits\n"
        "on the Program bus. The hand-maintained mirror (`SP1Clean/Model/Opcode.lean`) is\n"
        "cross-checked against this table by `opcodeTable_matchesExtracted`\n"
        "(`SP1Clean/FormalModel/OpcodeTable.lean`). -/\n\n"
        + LINTERS_OFF + "\n\n"
        + "namespace SP1Clean.Extracted\n\n"
        + "/-- One SP1 `Opcode` enum row: variant name and `#[repr(u8)]` discriminant. -/\n"
        + "structure OpcodeRow where\n"
        + "  name : String\n"
        + "  discriminant : Nat\n"
        + "deriving DecidableEq, Repr\n\n"
        + f"/-- The exact `Opcode` table at `checkedInProvenance.semanticRevision`: "
        + f"{len(entries)} variants,\ndiscriminants `0..{len(entries) - 1}` in declaration "
        + "order. -/\n"
        + "def currentOpcodeTable : List OpcodeRow := [\n"
        + rows + "\n]\n\n"
        + "end SP1Clean.Extracted\n"
    )


def _manifest_cluster(manifest: dict, expected_names: Sequence[str], label: str) -> List[dict]:
    """Select one exact machine cluster and reject malformed/ambiguous manifest data."""
    clusters = manifest.get("clusters")
    if not isinstance(clusters, list):
        raise RuntimeError("profile manifest has no `clusters` list")
    expected = set(expected_names)
    matches: List[List[dict]] = []
    for cluster in clusters:
        if not isinstance(cluster, list) or any(not isinstance(entry, dict) for entry in cluster):
            raise RuntimeError("profile manifest contains a malformed cluster")
        names = [entry.get("name") for entry in cluster]
        if len(names) != len(set(names)):
            raise RuntimeError(f"profile manifest cluster contains duplicate names: {names}")
        if set(names) == expected:
            matches.append(cluster)
    if len(matches) != 1:
        raise RuntimeError(
            f"expected exactly one {label} cluster with {sorted(expected)}, found {len(matches)}")
    selected = matches[0]
    for entry in selected:
        if not isinstance(entry.get("name"), str):
            raise RuntimeError(f"{label} cluster has a non-string name: {entry}")
        for width_key in ("main_width", "preprocessed_width"):
            width = entry.get(width_key)
            if not isinstance(width, int) or width < 0:
                raise RuntimeError(f"{label} cluster has invalid {width_key}: {entry}")
    return selected


def validate_profile_manifest(manifest: dict) -> Tuple[List[dict], List[dict]]:
    """Validate the public width and locate both exact theorem clusters."""
    if manifest.get("num_public_values") != 160:
        raise RuntimeError(
            "RiscvAir public-value width changed: expected 160, got "
            f"{manifest.get('num_public_values')}")
    core = _manifest_cluster(manifest, BASELINE_CORE_CLUSTER, "baseline Core")
    memory = _manifest_cluster(manifest, MEMORY_BOUNDARY_CLUSTER, "memory-boundary")

    seen: Dict[str, Tuple[int, int]] = {}
    for entry in [*core, *memory]:
        shape = (entry["main_width"], entry["preprocessed_width"])
        previous = seen.setdefault(entry["name"], shape)
        if previous != shape:
            raise RuntimeError(
                f"table {entry['name']} has inconsistent shapes {previous} and {shape}")
    return core, memory


def render_core_air_manifest(core: Sequence[dict], memory: Sequence[dict]) -> str:
    """Render the exact cluster membership and row widths obtained from Rust."""
    def render_cluster(entries: Sequence[dict]) -> str:
        rows = [
            f'  ⟨"{entry["name"]}", {entry["main_width"]}, '
            f'{entry["preprocessed_width"]}⟩,'
            for entry in entries
        ]
        return "[\n" + "\n".join(rows) + "\n]"

    return (
        "import SP1Clean.Extracted.Provenance\n\n"
        "/-! # AUTO-GENERATED Core AIR machine manifest — do not edit by hand.\n\n"
        "Generated directly from `RiscvAir::machine().shape().chip_clusters` by the pinned\n"
        "list-only extractor. Each entry records the runtime `MachineAir::name`, main width, and\n"
        "preprocessed width. Regeneration fails unless the two theorem clusters occur exactly once\n"
        "and the public-value width remains 160. -/\n\n"
        "set_option linter.all false  -- auto-generated: skip linters\n\n"
        "namespace SP1Clean.Extracted\n\n"
        "structure CoreAIRTableShape where\n"
        "  name : String\n"
        "  mainWidth : Nat\n"
        "  preprocessedWidth : Nat\n"
        "deriving DecidableEq, Repr\n\n"
        "/-- Exact baseline trusted Core cluster at `checkedInProvenance`. -/\n"
        "def currentCoreCluster : List CoreAIRTableShape := "
        + render_cluster(core)
        + "\n\n"
        "/-- Exact trusted memory-boundary cluster at `checkedInProvenance`. -/\n"
        "def currentMemoryBoundaryCluster : List CoreAIRTableShape := "
        + render_cluster(memory)
        + "\n\n"
        "/-- `RiscvAir::machine().num_pv_elts()` at the extraction revision. -/\n"
        "def currentCorePublicValuesWidth : Nat := 160\n\n"
        "end SP1Clean.Extracted\n"
    )


def _git_output(sp1_dir: str, args: Sequence[str]) -> str:
    result = subprocess.run(
        ["git", "-C", sp1_dir, *args], capture_output=True, text=True
    )
    if result.returncode != 0:
        raise SystemExit(
            f"git {' '.join(args)} failed in extractor checkout {sp1_dir}:\n{result.stderr}"
        )
    return result.stdout.strip()


def verify_extraction_branch_delta(sp1_dir: str, actual: str) -> None:
    """Check the two distinct surfaces of the pinned extraction branch.

    Machine AIR sources may differ only by line-checked reflection metadata. Constraint-compiler,
    shape, and symbolic-IR changes are instead confined to an explicit trusted-tooling allowlist and
    authenticated by the exact branch commit; this gate deliberately does not call those changes
    semantically inert.
    """
    merge_base = _git_output(sp1_dir, ["merge-base", SP1_SEMANTIC_COMMIT, actual])
    if merge_base != SP1_SEMANTIC_COMMIT:
        raise SystemExit(
            f"extractor {actual} is not based directly on semantic revision "
            f"{SP1_SEMANTIC_COMMIT} (merge base {merge_base})"
        )

    changed_text = _git_output(
        sp1_dir, ["diff", "--name-only", f"{SP1_SEMANTIC_COMMIT}..{actual}"]
    )
    changed = set(changed_text.splitlines()) if changed_text else set()
    allowed = TRUSTED_EXTRACTOR_FILES | EXTRACTOR_METADATA_FILES
    unexpected = sorted(
        path for path in changed
        if path not in allowed and not path.startswith(TRUSTED_EXTRACTOR_PREFIXES)
    )
    if unexpected:
        raise SystemExit(
            "extraction branch changes files outside the declared machine/tooling surfaces:\n  "
            + "\n  ".join(unexpected)
        )

    for path in sorted(changed & EXTRACTOR_METADATA_FILES):
        diff = _git_output(
            sp1_dir,
            ["diff", "--unified=0", f"{SP1_SEMANTIC_COMMIT}..{actual}", "--", path],
        )
        changed_lines = [
            line for line in diff.splitlines()
            if (line.startswith("+") or line.startswith("-"))
            and not line.startswith("+++") and not line.startswith("---")
        ]
        bad_lines = [
            line for line in changed_lines
            if not line[1:].lstrip().startswith(("use sp1_derive", "#[derive("))
        ]
        if bad_lines:
            raise SystemExit(
                f"extraction branch changes executable machine AIR source in {path}:\n  "
                + "\n  ".join(bad_lines)
            )

    machine_metadata = changed & EXTRACTOR_METADATA_FILES
    trusted_tooling = changed - machine_metadata
    print(
        f"Verified extraction branch {actual} over semantic base {SP1_SEMANTIC_COMMIT}: "
        f"{len(machine_metadata)} machine AIR file(s) have derive/import-only deltas; "
        f"{len(trusted_tooling)} extractor/shape/tooling file(s) are accepted at commit {actual} "
        "(trusted, not proven semantically inert)"
    )


def verify_extractor_clean(sp1_dir: str) -> None:
    """Require the extraction checkout to be clean: every extraction change is an ordinary commit
    on the pinned branch, so a dirty worktree means the artifacts would not be reproducible from
    the pin."""
    status = subprocess.run(
        ["git", "-C", sp1_dir, "status", "--porcelain=v1"],
        capture_output=True,
        text=True,
    )
    if status.returncode != 0:
        raise SystemExit(f"git status failed in extractor checkout {sp1_dir}:\n{status.stderr}")
    dirty = [line for line in status.stdout.splitlines() if not line.startswith("??")]
    if dirty:
        raise SystemExit(
            "extraction checkout has uncommitted changes (the pin covers commits only):\n  "
            + "\n  ".join(dirty)
        )
    print("Verified extraction checkout is clean at the pin")


def verify_no_mprotect(sp1_dir: str) -> None:
    """Pin the extraction profile: the `#[cfg(feature = "mprotect")]` assertions are deliberately
    outside the extracted lists (the trusted, non-mprotect build is what SP1 proves in production),
    and that exclusion must be an asserted property of the cargo feature resolution, not an
    accident of default features (external report F17)."""
    tree = subprocess.run(
        ["cargo", "tree", "-e", "features", "-p", "sp1-constraint-compiler", "--prefix", "none"],
        capture_output=True,
        text=True,
        cwd=sp1_dir,
    )
    if tree.returncode != 0:
        raise SystemExit(f"cargo tree failed in extractor checkout {sp1_dir}:\n{tree.stderr}")
    hits = [line for line in tree.stdout.splitlines() if "mprotect" in line]
    if hits:
        raise SystemExit(
            "the extraction build enables the mprotect feature; the extracted assertion lists "
            "would silently cover a different profile:\n  " + "\n  ".join(sorted(set(hits)))
        )
    print("Verified extraction profile excludes the mprotect feature")


# ── Orchestration ───────────────────────────────────────────────────────────────────────────

def main() -> None:
    global OPERATIONS, CHIPS, SYSTEM_TABLES

    sp1_dir = os.environ.get("SP1_DIR", DEFAULT_SP1_DIR)

    head = subprocess.run(["git", "-C", sp1_dir, "rev-parse", "HEAD"],
                          capture_output=True, text=True)
    actual = head.stdout.strip() if head.returncode == 0 else "<not a git checkout>"
    if actual != SP1_PINNED_COMMIT:
        msg = (f"SP1 checkout at {sp1_dir} is {actual}, but Extracted/ was generated from "
               f"pinned {SP1_PINNED_COMMIT}.")
        if os.environ.get("SP1_ALLOW_UNPINNED") == "1":
            print(f"WARNING: {msg} Proceeding (SP1_ALLOW_UNPINNED=1) — update SP1_PINNED_COMMIT "
                  f"when committing the regenerated files.")
        else:
            raise SystemExit(f"{msg} Set SP1_ALLOW_UNPINNED=1 to extract anyway.")

    verify_extraction_branch_delta(sp1_dir, actual)
    verify_extractor_clean(sp1_dir)
    verify_no_mprotect(sp1_dir)

    os.makedirs(EXTRACTED_DIR, exist_ok=True)

    # Profile extraction is unconditional, including `EXTRACT_ONLY` runs.  Otherwise a focused
    # regeneration could refresh row lists while retaining stale machine-shape metadata.
    try:
        profile_manifest = run_profile_manifest(sp1_dir)
        core_manifest, memory_manifest = validate_profile_manifest(profile_manifest)
        profile_output = render_core_air_manifest(core_manifest, memory_manifest)
    except Exception as error:  # noqa: BLE001
        raise SystemExit(f"Required Core AIR profile extraction failed: {error}") from error

    # The opcode discriminant table is likewise unconditional: it is cheap (a `git show` + text
    # parse, no cargo run) and pins the instruction alphabet the Model-layer mirror is checked
    # against.
    try:
        opcode_output = render_opcode_table(read_opcode_table(sp1_dir))
    except Exception as error:  # noqa: BLE001
        raise SystemExit(f"Required opcode-table extraction failed: {error}") from error

    extract_public_values = True

    # `EXTRACT_ONLY=Name1,Name2,…` restricts this run to a subset of OPERATIONS/CHIPS/
    # SYSTEM_TABLES (a closed composition group) — used to regenerate just the files that
    # changed without rewriting every module. Reuse wiring stays correct as long as the subset is
    # closed under sub-operation composition (e.g. `Add` needs `AddOperation,CPUState,RTypeReader`).
    only = os.environ.get("EXTRACT_ONLY")
    if only:
        wanted = {name.strip() for name in only.split(",") if name.strip()}
        OPERATIONS = [o for o in OPERATIONS if o in wanted]
        CHIPS = [c for c in CHIPS if c in wanted]
        SYSTEM_TABLES = [table for table in SYSTEM_TABLES if table in wanted]
        extract_public_values = "PublicValues" in wanted
        print(f"EXTRACT_ONLY → operations={OPERATIONS}, chips={CHIPS}, "
              f"system={SYSTEM_TABLES}, publicValues={extract_public_values}")

    # 1. Discovery pass: which structs does each module emit with no reuse? Tolerate per-target
    #    compiler failures (e.g. a chip whose `<Chip>Cols` shape isn't yet composed in the
    #    compiler) — skip them, keep going, and report at the end.
    print("Discovery pass (emitting with no reuse to map struct ownership)…")
    discovery: Dict[str, str] = {}   # module → no-reuse body (successful targets only)
    emitted: Dict[str, List[str]] = {}
    skipped: Dict[str, str] = {}     # module → first-line reason
    required_failures: List[str] = []
    for op in OPERATIONS:
        print(f"  · {op}")
        try:
            discovery[op] = run_constraint_compiler(sp1_dir, operation=op)
            emitted[op] = _emitted_structs(discovery[op])
        except Exception as e:  # noqa: BLE001
            skipped[op] = str(e).splitlines()[-1] if str(e).strip() else "compiler error"
            print(f"    ✗ skipped: {skipped[op]}")
    for chip in CHIPS:
        print(f"  · {chip} (chip)")
        try:
            discovery[chip] = run_constraint_compiler(sp1_dir, chip=chip)
            emitted[chip] = _emitted_structs(discovery[chip])
        except Exception as e:  # noqa: BLE001
            skipped[chip] = str(e).splitlines()[-1] if str(e).strip() else "compiler error"
            print(f"    ✗ skipped: {skipped[chip]}")
            if chip in CHIP_ORACLES:
                required_failures.append(f"chip oracle discovery {chip}: {skipped[chip]}")
    for table in SYSTEM_TABLES:
        print(f"  · {table} (system table)")
        try:
            discovery[table] = run_constraint_compiler(sp1_dir, chip=table)
            emitted[table] = _emitted_structs(discovery[table])
        except Exception as e:  # noqa: BLE001
            skipped[table] = str(e).splitlines()[-1] if str(e).strip() else "compiler error"
            print(f"    ✗ required system table failed: {skipped[table]}")
            required_failures.append(f"system-table discovery {table}: {skipped[table]}")

    public_body = None
    if extract_public_values:
        print("  · machine public values")
        try:
            public_body = run_constraint_compiler(sp1_dir, public_values=True)
        except Exception as e:  # noqa: BLE001
            reason = str(e).splitlines()[-1] if str(e).strip() else "compiler error"
            print(f"    ✗ required public-values block failed: {reason}")
            required_failures.append(f"public-values discovery: {reason}")

    validate_native_layouts(discovery, native_structs(), complete=not only)
    owner = resolve_ownership(emitted)
    print(f"Resolved ownership for {len(owner)} structs.")

    # Each generated operation module's own header imports — feeds the chip oracles'
    # transitive-import pruning (`_prune_transitive_imports`).
    operation_imports: Dict[str, Sequence[str]] = {
        op: reuse_for(op, emitted[op], owner, discovery[op])[1]
        for op in OPERATIONS if op in emitted
    }

    # Render every newly required system artifact before writing anything. This prevents a partial
    # regeneration from being mistaken for a complete Core AIR extraction.
    system_outputs: Dict[str, str] = {}
    for table in SYSTEM_TABLES:
        if table not in emitted:
            continue
        try:
            skips, imports = reuse_for(table, emitted[table], owner, discovery[table])
            body = (run_constraint_compiler(sp1_dir, chip=table, reuse=skips)
                    if skips else discovery[table])
            system_outputs[table] = render_system_table(table, imports, body)
        except Exception as e:  # noqa: BLE001
            required_failures.append(f"system-table render {table}: {e}")

    public_output = None
    if public_body is not None:
        try:
            public_output = render_public_values(public_body)
        except Exception as e:  # noqa: BLE001
            required_failures.append(f"public-values render: {e}")

    if required_failures:
        details = "\n".join(f"   - {failure}" for failure in required_failures)
        raise SystemExit(
            "\nRequired extraction artifacts failed before any file was written:\n" + details)

    # 2. Emit pass: re-run with the derived reuse, then render + write (successful targets only).
    _write(os.path.join(EXTRACTED_DIR, "Provenance.lean"), render_provenance())
    _write(os.path.join(EXTRACTED_DIR, "CoreAIRManifest.lean"), profile_output)
    _write(os.path.join(EXTRACTED_DIR, "OpcodeTable.lean"), opcode_output)
    written = 3
    # The native library now owns these columns; retire the old generated carrier.
    Path(EXTRACTED_DIR, "MemoryAccess.lean").unlink(missing_ok=True)
    for op in [o for o in OPERATIONS if o in emitted and o not in CHIP_ONLY_HELPERS]:
        print(f"Processing {op}")
        try:
            skips, imports = reuse_for(op, emitted[op], owner, discovery[op])
            body = run_constraint_compiler(sp1_dir, operation=op, reuse=skips) if skips else discovery[op]
            _write(os.path.join(EXTRACTED_DIR, f"{op}.lean"), render(op, imports, body))
            written += 1
        except Exception as e:  # noqa: BLE001 — best-effort, continue with the rest
            print(f"  ✗ Error: {e}")

    for chip in [c for c in CHIPS if c in emitted]:
        print(f"Processing chip {chip}")
        try:
            if chip not in CHIP_ORACLES:
                raise ValueError(
                    "not in CHIP_ORACLES — the legacy flat `Extracted/<Chip>Chip.lean` form was "
                    "retired with the 2026-07 whole-chip oracle migration; register the chip as "
                    "an oracle instead")
            oracle_reuse = [
                struct for struct in emitted[chip]
                if struct in CHIP_ORACLE_SHARED_STRUCTS
            ]
            oracle_imports: List[str] = []
            for struct in oracle_reuse:
                imported = _import_module(owner[struct])
                if imported not in oracle_imports:
                    oracle_imports.append(imported)
            oracle_body = (run_constraint_compiler(sp1_dir, chip=chip, reuse=oracle_reuse)
                           if oracle_reuse else discovery[chip])
            _write(os.path.join(EXTRACTED_DIR, "ChipOracle", f"{chip}.lean"),
                   render_chip_oracle(chip, oracle_body, discovery, oracle_imports,
                                      operation_imports))
            written += 1
        except Exception as e:  # noqa: BLE001 — best-effort, continue with the rest
            print(f"  ✗ Error: {e}")
            required_failures.append(f"chip oracle render {chip}: {e}")

    for table, output in system_outputs.items():
        print(f"Processing system table {table}")
        _write(os.path.join(EXTRACTED_DIR, "SystemOracle", f"{table}.lean"), output)
        written += 1

    if public_output is not None:
        print("Processing machine public values")
        _write(os.path.join(EXTRACTED_DIR, "SystemOracle", "PublicValues.lean"), public_output)
        written += 1

    # 3. Summary — what got written and which targets the compiler can't yet emit.
    print(f"\n== Wrote {written} module(s) to {EXTRACTED_DIR} ==")
    if skipped:
        print(f"== {len(skipped)} target(s) skipped (compiler can't emit yet): ==")
        for name, reason in skipped.items():
            print(f"   - {name}: {reason}")
    if required_failures:
        details = "\n".join(f"   - {failure}" for failure in required_failures)
        raise SystemExit(f"\nRequired extraction artifacts failed; no successful regeneration claim:\n{details}")


if __name__ == "__main__":
    main()
