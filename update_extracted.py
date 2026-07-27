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
`interactions`. Canonical reader structs are reused from their generated modules; chip-private
arithmetic structs/functions remain namespaced inside that chip oracle and are not public
operation-level faithfulness boundaries. `OPERATIONS` and `WITNESS_OPERATIONS` remain only to
support chips not yet migrated to this form. Native Clean circuits are hand-maintained under
`Native/`; this generator deliberately emits no circuit implementation.

**Why auto-derive?** Each `Extracted/` file must own exactly one column struct; a module that
composes sub-operations imports their already-generated modules (`--reuse-struct <Name>`)
instead of re-emitting them. Rather than hand-maintain a per-entry reuse list, this script:

  1. *Discovery pass* — runs the compiler for every module with NO reuse and parses which
     `structure <Name>` blocks each emits, building a global struct→owning-module map (seeded by
     `STRUCT_OWNERSHIP` for the struct≠module / shared-struct cases). Collisions fail loudly.
  2. *Emit pass* — for each module, reuse = every struct it emits that another module owns; those
     are passed as `--reuse-struct` and their owners are imported. The compiler re-runs and the
     file is written.

The shared interaction vocabulary lives in `SP1Clean/Extracted/ExtractionDSL.lean`; whole-chip
faithfulness anchors live in `SP1Clean/Faithful/`.

Usage: `SP1_DIR=/path/to/audited-extractor-overlay python3 update_extracted.py`.
`SP1_DIR` must be the pinned extraction-only overlay; its merge base is the unmodified semantic SP1
revision recorded below.  The ordinary sibling `../sp1` may remain checked out at that semantic
revision and is never modified by this script.
"""

import hashlib
import json
import os
import re
import subprocess
from typing import Dict, List, Sequence, Set, Tuple

# ── Registry ────────────────────────────────────────────────────────────────────────────────
# Flat lists of module names to emit (order is irrelevant — every compiler call is independent;
# grouped only for readability). A module's reuse of sub-structs is derived automatically.

# Operation / reader / compare-op modules → `Extracted/<name>.lean`.
OPERATIONS: List[str] = [
    # Instruction readers + CPU state. `RTypeReader` owns the nested register-access structs
    # (`RegisterAccessCols` / `RegisterAccessTimestamp`); the other readers reuse them.
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

# Transitional operation-level witness batteries. New conformance coverage belongs in `TRACE_CHIPS`,
# which compares complete rows produced by the chip circuit with Rust `generate_trace`. Keep an entry
# here only while an unmigrated chip still depends on the legacy operation boundary; shrink this list as
# chips acquire `ChipFaithful` anchors and whole-trace tests. An op here MUST also be in `OPERATIONS`.
WITNESS_OPERATIONS: List[str] = [
    "LtOperationUnsigned",
    "IsZeroOperation",
    "IsZeroWordOperation",
    "AddwOperation",
    "SubwOperation",
    "U16MSBOperation",
    "U16CompareOperation",
    "AddrAddOperation",
    "BitwiseOperation",
    "IsEqualWordOperation",
    "MulOperation",
]

# Per-op ordered list of the JSON keys that form the conformance tuple emitted to Lean (the operand
# columns + the witnessed columns to check). Each key's value is auto-rendered as a `#v[…]` literal
# (JSON array → `Vector ℕ <len>`) or a bare `ℕ` (JSON int — e.g. a field-inverse column). Keys like
# `inputs`/`output`/`events` are intentionally omitted (not part of the witness conformance check).
WITNESS_SCHEMA: Dict[str, List[str]] = {
    "LtOperationUnsigned": ["b_limbs", "cc_limbs", "comparison_limbs", "u16_flags", "not_eq_inv"],
    "IsZeroOperation": ["a_field", "inverse", "result"],
    "IsZeroWordOperation": ["a_limbs", "inv", "lresult", "first_half", "second_half", "result"],
    "AddwOperation": ["a_limbs", "b_limbs", "value", "msb"],
    "SubwOperation": ["a_limbs", "b_limbs", "value", "msb"],
    "U16MSBOperation": ["a", "msb"],
    "U16CompareOperation": ["b", "c", "bit"],
    "AddrAddOperation": ["a_limbs", "b_limbs", "value"],
    "BitwiseOperation": ["b_bytes", "c_bytes", "opcode", "result"],
    "IsEqualWordOperation": ["a_limbs", "b_limbs", "inv", "lresult", "first_half", "second_half", "result"],
    "MulOperation": ["b_limbs", "c_limbs", "is_mulh", "is_mulhsu", "is_mulw", "carry", "product",
                     "b_lower_byte", "c_lower_byte", "b_msb", "c_msb", "product_msb",
                     "b_sign_extend", "c_sign_extend"],
}

# Chips with a **whole-trace** dumper in the `witness_vectors` binary (`--chip <name>`) → an extra
# `SP1CleanTest/TraceGenTests/<name>ChipTraceVectors.lean` (the event battery + the full padded matrix from
# SP1's real `generate_trace`) plus a hand-written `SP1CleanTest/TraceGenTests/<name>ChipTraceWitness.lean`
# anchor that re-derives every row from the chip's own circuit (`TraceGenerator.lean` +
# `EventPopulate.lean`) and checks the matrices match. Value = (expected row width — a layout-drift
# tripwire; the dumper also asserts it, reader kind — picks the dumped record type and the Lean
# event mirror: "RType" → `AluEventRec`, "ALUType" → `AluTypeEventRec`; the `*Op` variants append
# the executor opcode discriminant — `AluEventOpRec` / `AluTypeOpEventRec` — for the hint-driven
# chips whose Lean anchors build the per-event flag `ProverHint` from it).
TRACE_CHIPS: Dict[str, Tuple[int, str]] = {
    "Add": (33, "RType"),
    "Sub": (33, "RType"),
    "Subw": (32, "RType"),
    "Mul": (82, "RTypeOp"),
    "DivRem": (246, "RTypeOp"),
    "Addw": (36, "ALUType"),
    "Bitwise": (51, "ALUTypeOp"),
    "Lt": (44, "ALUTypeOp"),
    "ShiftLeft": (65, "ALUTypeOp"),
    "ShiftRight": (69, "ALUTypeOp"),
}

# Ordered JSON keys of one dumped event, per reader kind = the field order of Lean's
# `AluEventRec` / `AluTypeEventRec` / `AluEventOpRec` / `AluTypeOpEventRec`
# (`SP1CleanTest/TraceGenTests/EventPopulate.lean`).
TRACE_EVENT_KEYS: Dict[str, List[str]] = {
    "RType": [
        "clk", "pc", "a", "b", "c", "opA", "opB", "opC",
        "tsA", "prevTsA", "prevA", "tsB", "prevTsB", "tsC", "prevTsC",
    ],
    "ALUType": [
        "clk", "pc", "a", "b", "c", "opA", "opB", "opC", "immC",
        "tsA", "prevTsA", "prevA", "tsB", "prevTsB", "tsC", "prevTsC",
    ],
    "RTypeOp": [
        "clk", "pc", "a", "b", "c", "opA", "opB", "opC",
        "tsA", "prevTsA", "prevA", "tsB", "prevTsB", "tsC", "prevTsC", "opcode",
    ],
    "ALUTypeOp": [
        "clk", "pc", "a", "b", "c", "opA", "opB", "opC", "immC",
        "tsA", "prevTsA", "prevA", "tsB", "prevTsB", "tsC", "prevTsC", "opcode",
    ],
}

# Reader kind → (Lean event mirror struct, dumped Rust record type for the doc string).
TRACE_EVENT_TYPES: Dict[str, Tuple[str, str]] = {
    "RType": ("AluEventRec", "RTypeRecord"),
    "ALUType": ("AluTypeEventRec", "ALUTypeRecord"),
    "RTypeOp": ("AluEventOpRec", "RTypeRecord"),
    "ALUTypeOp": ("AluTypeOpEventRec", "ALUTypeRecord"),
}

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

# Chips migrated to a chip-namespaced oracle under `Extracted/ChipOracle/<Chip>.lean`. Canonical
# reader structs and their generated `asserts`/`interactions` functions are reused, while
# chip-private arithmetic structs and functions stay in the oracle.
# Grow this set one chip at a time, deleting the corresponding legacy `Extracted/<Chip>Chip.lean`
# file after its native reconfiguration lands.
CHIP_ORACLES: Set[str] = {
    "Add", "Sub", "Subw", "Mul", "DivRem", "Addi", "Jalr", "Jal", "UType", "Addw",
    "Bitwise", "Lt", "ShiftLeft", "ShiftRight", "AluX0", "Branch", "LoadByte", "LoadHalf",
    "LoadWord", "LoadDouble", "LoadX0", "StoreByte", "StoreHalf", "StoreWord",
    "StoreDouble",
}

# Stable generated reader substrate shared by native chip rows and whole-chip Rust oracles. Reusing
# these types avoids creating a fresh CPU/register-reader hierarchy per oracle while keeping Rust
# arithmetic operation structs chip-private. Extend this set when a new canonical reader lands.
CHIP_ORACLE_SHARED_STRUCTS: Set[str] = {
    "CPUState", "RTypeReader", "ITypeReader", "JTypeReader", "ALUTypeReader",
    "RegisterAccessCols", "RegisterAccessTimestamp",
    # The memory-access blocks nested in every load/store row, owned by the `MemoryAccess`
    # struct-carrier module (see `STRUCT_CARRIERS`).
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

# Explicit struct→owning-module overrides, ONLY for cases the default rules can't infer:
#   * struct name ≠ its owning module's name, or
#   * a struct emitted by several modules (shared column layout) where one module is canonical.
# The default owner rules (no entry needed) are:
#   * a struct named exactly like an OPERATIONS module → that module owns it;
#   * a `<Chip>Cols` struct → the chip `<Chip>` owns it.
STRUCT_OWNERSHIP: Dict[str, str] = {
    # The byte-decomposition column struct `U16toU8Operation` backs BOTH the `Unsafe` and `Safe`
    # operation builders (same Rust column struct). Canonical owner = the `Unsafe` module; the
    # `Safe` module emits only its `constraints` def and imports the struct.
    "U16toU8Operation": "U16toU8OperationUnsafe",
    # The register-access column structs are owned by `RTypeReader`; every other reader reuses them
    # (and importing `RTypeReader` provides both, so they need not be imported separately).
    "RegisterAccessCols": "RTypeReader",
    "RegisterAccessTimestamp": "RTypeReader",
    # The memory-access column structs (`MemoryAccessCols`/`MemoryAccessTimestamp`) are nested only
    # in the Load/Store chip column structs (no standalone operation emits them), so they have no
    # natural operation owner. They used to fall to the first-emitting chip (LoadByte), but a chip
    # oracle cannot be a struct definition site (every load/store eventually migrates), so they are
    # owned by the dedicated struct-carrier module `MemoryAccess` (see `STRUCT_CARRIERS`).
    "MemoryAccessCols": "MemoryAccess",
    "MemoryAccessTimestamp": "MemoryAccess",
}

# Struct-carrier modules: canonical definition sites for structs with no operation owner whose
# definition must outlive the chip files that emit them. Each entry maps a carrier module name to
# `(donor, struct names in emission order)`: the carrier file is rendered by carving those struct
# declarations byte-for-byte out of the donor chip's no-reuse discovery body (so the definitions
# remain compiler-derived, never hand-written). The carrier is written only on runs that discover
# the donor. `STRUCT_OWNERSHIP` must point each carried struct at its carrier module.
STRUCT_CARRIERS: Dict[str, Tuple[str, Tuple[str, ...]]] = {
    "MemoryAccess": ("LoadByte", ("MemoryAccessTimestamp", "MemoryAccessCols")),
}

DEFAULT_SP1_DIR = "../sp1"
# Exact unmodified SP1 source whose AIR semantics are being formalized.
SP1_SEMANTIC_COMMIT = "a630089d9ff484ec6f2feade8d0afbb1447eed11"
# Audited extraction-only overlay used to generate the checked-in artifacts. Its merge base is
# `SP1_SEMANTIC_COMMIT`; runtime chip-source changes are restricted to reflection/`IntoShape`
# metadata and are checked below. A full 25-chip AIR-only regeneration was byte-for-byte identical
# to the previous v6.2.2 artifacts before this pin was advanced.
SP1_PINNED_COMMIT = "69a8377c6e5550451f40c81fca17459687cd0a8f"

# The committed exporter still contained a transitional direct-to-Clean-circuit backend and lacked
# flat system rows, complete interaction kinds, machine-level public-value extraction, and a
# machine-shape manifest. The two reviewable patches apply in order; the combined diff digest must
# match the extractor worktree byte-for-byte.
EXTRACTOR_COMPONENT_PATCHES: Tuple[Tuple[str, str], ...] = (
    (os.path.join("scripts", "extractor-patches", "core-air-lists.patch"),
     "73ab50273532362ba88330c9046a95c0812b03c9fd2c2c0cd30850672f52cf8d"),
    (os.path.join("scripts", "extractor-patches", "core-air-manifest.patch"),
     "bb62d4cfcaea5f0d8abf96e794522f48c688fe27e609e60082e9de0aba824e52"),
)
EXTRACTOR_PATCH_SHA256 = "a2c43cfab00280f5331a15ec251a8341a26ecf3baedcda22fec182915fbcf108"
EXTRACTOR_PATCHED_FILES: Tuple[str, ...] = (
    "crates/core/compiler/src/main.rs",
    "crates/hypercube/src/ir/ast.rs",
    "crates/hypercube/src/ir/expr.rs",
    "crates/hypercube/src/ir/lean.rs",
)

# The only semantic-tree files the extractor overlay may touch. The checker below additionally
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
EXTRACTOR_ONLY_PREFIXES: Tuple[str, ...] = (
    "crates/core/compiler/",
    "crates/hypercube/src/ir/",
)
EXTRACTOR_ONLY_FILES: Set[str] = {
    "Cargo.lock",
    "crates/derive/src/into_shape.rs",
}
EXTRACTED_DIR = os.path.join("SP1Clean", "Extracted")
# The witness/trace conformance vectors are test-only data: they live in the top-level
# `SP1CleanTest` test library (built by `lake test`), not the main `SP1Clean` library — which is
# gated `native_decide`-free (the anchors that consume these vectors are the only `native_decide`).
WITNESS_DIR = os.path.join("SP1CleanTest", "WitnessTests", "Vectors")
TRACEGEN_DIR = os.path.join("SP1CleanTest", "TraceGenTests")

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
    """Owner of a struct under the default rules (no `STRUCT_OWNERSHIP` entry)."""
    if struct in OPERATIONS:
        return struct
    if struct.endswith("Cols") and struct[:-len("Cols")] in [*CHIPS, *SYSTEM_TABLES]:
        return struct[:-len("Cols")]
    return None


def resolve_ownership(emitted: Dict[str, List[str]]) -> Dict[str, str]:
    """Build the global struct→owning-module map, failing loudly on unresolved collisions.

    `emitted` maps each module name to the structs it emits with no reuse."""
    owner: Dict[str, str] = {}
    for struct in {s for structs in emitted.values() for s in structs}:
        if struct in STRUCT_OWNERSHIP:
            owner[struct] = STRUCT_OWNERSHIP[struct]
            continue
        default = _default_owner(struct)
        if default is not None:
            owner[struct] = default
            continue
        emitters = [m for m, structs in emitted.items() if struct in structs]
        if len(emitters) == 1:
            owner[struct] = emitters[0]
        else:
            # A struct emitted by several modules with no operation/STRUCT_OWNERSHIP owner (e.g.
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
    """The `Extracted.<…>` module file name for an owner — a chip owner lives in `<chip>Chip`."""
    if owner in CHIPS:
        return f"{owner}Chip"
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
        if len(fields) <= _LARGE_STRUCT_FIELD_THRESHOLD:
            return m.group(0)
        return _explicit_provable_struct(name, fields)
    return _DERIVE_STRUCT_RE.sub(repl, body)


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
    reuse_imports = "".join(f"import SP1Clean.Extracted.{m}\n" for m in import_modules)
    return (
        COMMON_IMPORTS + "\n" + reuse_imports + "\n"
        + doc + "\n\n"
        + LINTERS_OFF + "\n\n"
        + "namespace SP1Clean.Extracted\nopen SP1Clean\n"
    )


def render(operation: str, import_modules: Sequence[str], body: str) -> str:
    """Wrap an operation's compiler body in the clean-native module header/footer."""
    # Operations can be very large (MulOperation's ~460-`let` product chain exceeds 1M heartbeats),
    # so give them a generous limit.
    body = _preserve_raw_byte_opcodes(body)
    body = _bump_constraints_heartbeats(body.strip(), 8000000)
    body = _expand_large_derives(body)
    _sanity_gate(operation, body)
    reused = ", ".join(import_modules) if import_modules else "no"
    doc = (
        f"/-! # AUTO-GENERATED — do not edit by hand.\n\n"
        f"Generated by `update_extracted.py` from the `sp1-constraint-compiler`\n"
        f"(`--operation {operation} --format lean`). Contains SP1's `{operation}` operation\n"
        f"constraints (reusing the {reused} column-struct module(s), imported above). Regenerate\n"
        f"with `SP1_DIR=… python3 update_extracted.py`; the faithfulness anchor lives under\n"
        f"`SP1Clean/Faithful/`. -/"
    )
    return _header(import_modules, doc) + "\n" + body + "\n\n" + FOOTER


def _bump_constraints_heartbeats(body: str, heartbeats: int = 1000000) -> str:
    """Prefix **each** generated `@[irreducible] def` (`asserts` / `interactions` / `value`) with a
    raised `maxHeartbeats`. Each def's `let` chain (with nested `#v[…][k]` projections through the
    column structs) is whnf-expensive and exceeds the 200k default; the largest operations (e.g.
    `MulOperation`, ~460 lets) exceed even 1M. Harmless where the default already suffices (Add/Sub)."""
    needle = "@[irreducible] def "
    return body.replace(needle, f"set_option maxHeartbeats {heartbeats} in\n{needle}")


def render_struct_carrier(carrier: str, donor: str, struct_names: Sequence[str],
                          donor_body: str) -> str:
    """Render a struct-carrier module (see `STRUCT_CARRIERS`): the named struct declarations are
    carved byte-for-byte out of the donor chip's no-reuse discovery body, so the canonical
    definitions stay compiler-derived while outliving the donor's legacy chip file."""
    blocks: Dict[str, str] = {
        match.group(1): match.group(0) for match in _DERIVE_STRUCT_RE.finditer(donor_body)
    }
    missing = [name for name in struct_names if name not in blocks]
    if missing:
        raise ValueError(
            f"struct carrier {carrier}: donor {donor} discovery body does not declare {missing}")
    body = "\n\n".join(_expand_large_derives(blocks[name]) for name in struct_names)
    struct_list = ", ".join(f"`{name}`" for name in struct_names)
    doc = (
        f"/-! # AUTO-GENERATED — do not edit by hand.\n\n"
        f"Struct-carrier module: the canonical definition site for {struct_list}.\n"
        f"Carved by `update_extracted.py` out of the `sp1-constraint-compiler --chip {donor}`\n"
        f"discovery output (no standalone operation emits these structs; every load/store chip\n"
        f"row nests them). Regenerate with `SP1_DIR=… python3 update_extracted.py`. -/"
    )
    return _header([], doc) + "\n" + body + "\n\n" + FOOTER


def render_chip(chip: str, import_modules: Sequence[str], body: str) -> str:
    """Wrap a chip's compiler body in a module header that imports the reused operation
    column-struct modules."""
    body = _preserve_raw_byte_opcodes(body)
    body = _bump_constraints_heartbeats(body.strip(), 8000000)
    body = _expand_large_derives(body)
    _sanity_gate(f"{chip} (chip)", body)
    reused = ", ".join(import_modules) if import_modules else "no"
    doc = (
        f"/-! # AUTO-GENERATED — do not edit by hand.\n\n"
        f"Generated by `update_extracted.py` from the `sp1-constraint-compiler`\n"
        f"(`--chip {chip} --format lean --reuse-struct …`). Contains SP1's `{chip}` chip column\n"
        f"struct plus the chip's composed-operation constraints, reusing the {reused}\n"
        f"column-struct module(s) (imported above, not re-emitted). Regenerate with\n"
        f"`SP1_DIR=… python3 update_extracted.py`. -/"
    )
    return _header(import_modules, doc) + "\n" + body + "\n\n" + FOOTER


def render_system_table(
    table: str, import_modules: Sequence[str], body: str
) -> str:
    """Wrap a non-instruction table's exact flat-row assertion and interaction lists."""
    # The list-only backend already chunks large AIR bodies into irreducible parts.  Keep only the
    # recursion allowance needed to elaborate the generated `let` chains; adding one heartbeat
    # override per data definition would hide a chunk-size regression from the repository's
    # no-new-heartbeat audit gate.
    body = _preserve_raw_byte_opcodes(body)
    body = body.strip().replace(
        "@[irreducible] def ",
        "set_option maxRecDepth 100000 in\n@[irreducible] def ",
    )
    body = _expand_large_derives(body)
    _sanity_gate(f"{table} (system table)", body)
    reused = ", ".join(import_modules) if import_modules else "no"
    doc = (
        f"/-! # AUTO-GENERATED system-table Rust AIR oracle — do not edit by hand.\n\n"
        f"Generated by `update_extracted.py` from `sp1-constraint-compiler --chip {table} "
        f"--format lean`. Contains every `{table}` main-trace column in upstream index order, "
        f"the complete per-row `assertZero` list, and the complete interaction list. The flat "
        f"vector deliberately avoids inventing semantic field names in the extraction layer; "
        f"audited adapters may name selected indices above this anchor. Reuses the {reused} "
        f"helper module(s). -/"
    )
    # `Global` contains a Poseidon-style algebraic closure in which a single output depends on
    # roughly 1,300 shared bindings.  Entry-list chunking cannot make that one term smaller (and
    # finer chunks only duplicate it), so this is the sole new term-intrinsic heartbeat exception.
    intrinsic_limit = "set_option maxHeartbeats 1000000\n\n" if table == "Global" else ""
    return _header(import_modules, doc) + "\n" + intrinsic_limit + body + "\n\n" + FOOTER


def render_public_values(body: str) -> str:
    """Wrap `MachineRecord::eval_public_values`, the non-row AIR block in every Core shard."""
    body = _preserve_raw_byte_opcodes(body)
    body = body.strip().replace(
        "@[irreducible] def ",
        "set_option maxRecDepth 100000 in\n@[irreducible] def ",
    )
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


def render_chip_oracle(
    chip: str, chip_body: str, discovery: Dict[str, str], import_modules: Sequence[str]
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
    body = _bump_constraints_heartbeats(body.strip(), 8000000)
    body = _expand_large_derives(body)
    _sanity_gate(f"{chip} (self-contained chip oracle)", body)
    helper_list = ", ".join(embedded_helpers) if embedded_helpers else "no private helpers"
    shared_list = ", ".join(shared_helpers) if shared_helpers else "no shared helpers"
    doc = (
        f"/-! # AUTO-GENERATED whole-chip Rust AIR oracle — do not edit by hand.\n\n"
        f"Generated by `update_extracted.py` from `sp1-constraint-compiler --chip {chip} --format lean`.\n"
        f"Contains the complete Rust `{chip}` row shape, `assertZero` list, and interaction list,\n"
        f"reusing canonical generated reader structs and functions where available ({shared_list}).\n"
        f"The compiler's chip-private helper definitions ({helper_list}) are embedded in this namespace\n"
        f"rather than imported as operation-level verification artifacts. Regenerate with\n"
        f"`SP1_DIR=… python3 update_extracted.py`. -/"
    )
    return (
        COMMON_IMPORTS + "\n"
        + "".join(f"import SP1Clean.Extracted.{m}\n" for m in import_modules)
        + "\n" + doc + "\n\n" + LINTERS_OFF + "\n\n"
        + f"namespace SP1Clean.Extracted.{chip}Oracle\n"
        + "open SP1Clean\n\n" + body + "\n\n"
        + f"end SP1Clean.Extracted.{chip}Oracle\n"
    )


# ── Witness-vector pass ───────────────────────────────────────────────────────────────────────
# The completeness/conformance companion to the constraint pass: dump SP1's real `populate`
# outputs on a fixed input battery (via the `witness_vectors` binary) and render them as Lean data
# the `WitnessTests/<Op>Witness.lean` anchor `#guard`s the native `witness` function against.

def run_witness_vectors(sp1_dir: str, operation: str) -> dict:
    """Run the `witness_vectors` binary for one operation and return its parsed JSON."""
    cmd = ["cargo", "run", "-q", "-p", "sp1-constraint-compiler", "--bin", "witness_vectors",
           "--", "--operation", operation]
    result = subprocess.run(cmd, cwd=sp1_dir, capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(f"witness_vectors failed for {operation}:\n{result.stderr}")
    return json.loads(result.stdout)


def _vec_lean(xs: Sequence[int]) -> str:
    """Render a list of ints as a Clean `#v[...]` vector literal."""
    return "#v[" + ", ".join(str(x) for x in xs) + "]"


def _lean_elem_type(val) -> str:
    """The Lean type of one schema column: a JSON array → `Vector ℕ <len>`, a JSON int → `ℕ`."""
    return f"Vector ℕ {len(val)}" if isinstance(val, list) else "ℕ"


def _lean_elem(val) -> str:
    """Render one schema column value: a JSON array → `#v[…]`, a JSON int → its literal."""
    return _vec_lean(val) if isinstance(val, list) else str(val)


def render_witness_vectors(operation: str, data: dict) -> str:
    """Render an operation's witness-conformance vectors as a Lean `def` of tuples, one column per
    `WITNESS_SCHEMA[operation]` key (auto-typed `Vector ℕ n` / `ℕ` from the dumped JSON)."""
    keys = WITNESS_SCHEMA[operation]
    vectors = data["vectors"]
    first = vectors[0]
    prod_type = " × ".join(_lean_elem_type(first[k]) for k in keys)
    tuple_desc = "(" + ", ".join(keys) + ")"
    rows = [
        "  (" + ", ".join(_lean_elem(v[k]) for k in keys) + "),"
        for v in vectors
    ]
    body = "\n".join(rows)
    doc = (
        f"/-! # AUTO-GENERATED — do not edit by hand.\n\n"
        f"Witness-generation conformance vectors for SP1's `{operation}`, dumped from the **real**\n"
        f"`{operation}::populate` by `update_extracted.py` (the `witness_vectors` binary,\n"
        f"`--operation {operation}`). Unlike the constraint (`eval`) extraction, `populate` is native\n"
        f"imperative code and cannot be symbolically extracted; these vectors instead tie the Lean\n"
        f"witness function to the Rust source by **conformance** (agreement on the sampled inputs —\n"
        f"edge cases + a seeded LCG — not an all-inputs proof). Each entry is `{tuple_desc}`. The\n"
        f"check lives in `SP1CleanTest/WitnessTests/{operation}Witness.lean`. Regenerate with\n"
        f"`SP1_DIR=… python3 update_extracted.py`. -/"
    )
    return (
        "import SP1Clean.Math.Word\n\n"
        + doc + "\n\n"
        + "namespace SP1Clean.WitnessTests\nopen SP1Clean\n\n"
        + LINTERS_OFF + "\n\n"
        + "set_option maxHeartbeats 4000000 in\n"
        + "set_option maxRecDepth 64000 in\n"
        + f"/-- {len(vectors)} conformance vectors for `{operation}` (`{tuple_desc}`). -/\n"
        + f"def {operation}WitnessVectors : List ({prod_type}) := [\n"
        + body + "\n]\n\n"
        + "end SP1Clean.WitnessTests\n"
    )


def run_trace_vectors(sp1_dir: str, chip: str) -> dict:
    """Run the `witness_vectors` binary in `--chip` (whole-trace) mode and return its JSON."""
    cmd = ["cargo", "run", "-q", "-p", "sp1-constraint-compiler", "--bin", "witness_vectors",
           "--", "--chip", chip]
    result = subprocess.run(cmd, cwd=sp1_dir, capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(f"witness_vectors --chip failed for {chip}:\n{result.stderr}")
    return json.loads(result.stdout)


def render_trace_vectors(chip: str, width: int, kind: str, data: dict) -> str:
    """Render one chip's whole-trace conformance battery: the event list (as `AluEventRec` /
    `AluTypeEventRec` anonymous-constructor literals, field order = `TRACE_EVENT_KEYS[kind]`), the
    padded height, and the full row-major matrix from SP1's real `generate_trace` (canonical ℕ per
    cell)."""
    if data["width"] != width:
        raise RuntimeError(f"{chip}: dumped width {data['width']} != expected {width}")
    rows = data["rows"]
    if data["height"] != len(rows) or any(len(r) != width for r in rows):
        raise RuntimeError(f"{chip}: dumped matrix shape is inconsistent")
    events = data["events"]
    event_keys = TRACE_EVENT_KEYS[kind]
    event_type, record_type = TRACE_EVENT_TYPES[kind]
    event_rows = [
        "  ⟨" + ", ".join(str(e[k]) for k in event_keys) + "⟩,"
        for e in events
    ]
    matrix_rows = ["  " + _vec_lean(r) + "," for r in rows]
    doc = (
        f"/-! # AUTO-GENERATED — do not edit by hand.\n\n"
        f"Whole-trace conformance battery for SP1's `{chip}Chip`, dumped from the **real**\n"
        f"`MachineAir::generate_trace` by `update_extracted.py` (the `witness_vectors` binary,\n"
        f"`--chip {chip}`): the deterministic event battery and the full padded {width}-column\n"
        f"row-major matrix (including SP1's zero padding rows). The anchor\n"
        f"`SP1CleanTest/TraceGenTests/{chip}ChipTraceWitness.lean` re-derives every row from the\n"
        f"chip's own circuit (`TraceGenerator.lean`) and checks the matrices match. Regenerate\n"
        f"with `SP1_DIR=… python3 update_extracted.py`. -/"
    )
    return (
        "import SP1CleanTest.TraceGenTests.EventPopulate\n\n"
        + doc + "\n\n"
        + "namespace SP1Clean.TraceGenTests\nopen SP1Clean\n\n"
        + LINTERS_OFF + "\n\n"
        + f"/-- The {len(events)} dumped `(AluEvent, {record_type})` battery rows. -/\n"
        + f"def {chip}ChipTraceEvents : List {event_type} := [\n"
        + "\n".join(event_rows) + "\n]\n\n"
        + f"/-- The padded trace height SP1 chose (`next_multiple_of_32`). -/\n"
        + f"def {chip}ChipTraceHeight : ℕ := {data['height']}\n\n"
        + "set_option maxHeartbeats 4000000 in\n"
        + "set_option maxRecDepth 64000 in\n"
        + f"/-- SP1's real `generate_trace` output: {data['height']} × {width}, canonical values. -/\n"
        + f"def {chip}ChipTraceRows : List (Vector ℕ {width}) := [\n"
        + "\n".join(matrix_rows) + "\n]\n\n"
        + "end SP1Clean.TraceGenTests\n"
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
        "namespace SP1Clean.Extracted\n\n"
        "/-- Exact two-revision boundary behind every checked-in extracted artifact. -/\n"
        "structure ExtractionProvenance where\n"
        "  semanticRevision : String\n"
        "  extractorRevision : String\n"
        "  extractorPatchSha256 : String\n"
        "deriving DecidableEq, Repr\n\n"
        "/-- Provenance validated by the generator before it writes any AIR artifact. -/\n"
        "def checkedInProvenance : ExtractionProvenance where\n"
        f"  semanticRevision := \"{SP1_SEMANTIC_COMMIT}\"\n"
        f"  extractorRevision := \"{SP1_PINNED_COMMIT}\"\n"
        f"  extractorPatchSha256 := \"{EXTRACTOR_PATCH_SHA256}\"\n\n"
        "end SP1Clean.Extracted\n"
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


def verify_extractor_overlay(sp1_dir: str, actual: str) -> None:
    """Check that the pinned exporter is based on the exact semantic revision and that its only
    machine-source edits are non-operational reflection metadata."""
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
    allowed = EXTRACTOR_ONLY_FILES | EXTRACTOR_METADATA_FILES
    unexpected = sorted(
        path for path in changed
        if path not in allowed and not path.startswith(EXTRACTOR_ONLY_PREFIXES)
    )
    if unexpected:
        raise SystemExit(
            "extractor overlay changes files outside the audited exporter surface:\n  "
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
                f"extractor overlay changes runtime source in {path}:\n  "
                + "\n  ".join(bad_lines)
            )

    print(
        f"Verified extractor overlay {actual}: semantic base {SP1_SEMANTIC_COMMIT}, "
        f"{len(changed)} audited file(s), runtime AIR source unchanged"
    )


def verify_extractor_patch(sp1_dir: str) -> None:
    """Require the extractor worktree to carry exactly the checked-in list-only patch set.

    A merely dirty exporter is not provenance. Requiring byte equality with the checked-in patch
    makes the four uncommitted compiler/IR edits explicit, reviewable, and reproducible while the
    corresponding Rust change awaits an upstream commit.
    """
    for patch_path, expected_hash in EXTRACTOR_COMPONENT_PATCHES:
        with open(patch_path, "rb") as patch_file:
            actual_hash = hashlib.sha256(patch_file.read()).hexdigest()
        if actual_hash != expected_hash:
            raise SystemExit(
                f"extractor component patch {patch_path} has digest {actual_hash}, expected "
                f"{expected_hash}; update the audited patch set deliberately")

    status = subprocess.run(
        ["git", "-C", sp1_dir, "status", "--porcelain=v1", "--untracked-files=all"],
        capture_output=True,
        text=True,
    )
    if status.returncode != 0:
        raise SystemExit(f"git status failed in extractor checkout {sp1_dir}:\n{status.stderr}")
    expected_status = [f" M {path}" for path in EXTRACTOR_PATCHED_FILES]
    actual_status = status.stdout.splitlines()
    if actual_status != expected_status:
        raise SystemExit(
            "extractor worktree is not the exact audited list-only patch; expected:\n  "
            + "\n  ".join(expected_status)
            + "\nactual:\n  "
            + ("\n  ".join(actual_status) if actual_status else "<clean worktree>")
        )

    diff = subprocess.run(
        ["git", "-C", sp1_dir, "diff", "--binary", "HEAD", "--",
         *EXTRACTOR_PATCHED_FILES],
        capture_output=True,
    )
    if diff.returncode != 0:
        raise SystemExit(f"git diff failed in extractor checkout {sp1_dir}")
    actual_diff_hash = hashlib.sha256(diff.stdout).hexdigest()
    if actual_diff_hash != EXTRACTOR_PATCH_SHA256:
        raise SystemExit(
            "extractor worktree touches the expected files but its combined byte-level diff has "
            f"digest {actual_diff_hash}, expected {EXTRACTOR_PATCH_SHA256}"
        )
    print(f"Verified exact list-only extractor patch set {EXTRACTOR_PATCH_SHA256}")


# ── Orchestration ───────────────────────────────────────────────────────────────────────────

def main() -> None:
    global OPERATIONS, CHIPS, SYSTEM_TABLES, WITNESS_OPERATIONS, TRACE_CHIPS

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

    verify_extractor_overlay(sp1_dir, actual)
    verify_extractor_patch(sp1_dir)

    os.makedirs(EXTRACTED_DIR, exist_ok=True)

    # Profile extraction is unconditional, including `EXTRACT_ONLY` runs.  Otherwise a focused
    # regeneration could refresh row lists while retaining stale machine-shape metadata.
    try:
        profile_manifest = run_profile_manifest(sp1_dir)
        core_manifest, memory_manifest = validate_profile_manifest(profile_manifest)
        profile_output = render_core_air_manifest(core_manifest, memory_manifest)
    except Exception as error:  # noqa: BLE001
        raise SystemExit(f"Required Core AIR profile extraction failed: {error}") from error

    # `EXTRACT_AIR_ONLY=1` runs the complete symbolic AIR extraction while skipping the independent
    # witness/trace batteries. This is the conservative first
    # phase of a Rust-pin migration: compare every row shape/assertion/interaction artifact before
    # allowing populate/conformance churn to obscure the diff.
    if os.environ.get("EXTRACT_AIR_ONLY") == "1":
        WITNESS_OPERATIONS = []
        TRACE_CHIPS = {}
        print("EXTRACT_AIR_ONLY → skipping witness and trace-vector passes")

    extract_public_values = True

    # `EXTRACT_ONLY=Name1,Name2,…` restricts this run to a subset of OPERATIONS/CHIPS/
    # WITNESS_OPERATIONS (a closed composition group) — used to regenerate just the files that
    # changed without rewriting every module. Reuse wiring stays correct as long as the subset is
    # closed under sub-operation composition (e.g. `Add` needs `AddOperation,CPUState,RTypeReader`).
    only = os.environ.get("EXTRACT_ONLY")
    if only:
        wanted = {name.strip() for name in only.split(",") if name.strip()}
        OPERATIONS = [o for o in OPERATIONS if o in wanted]
        CHIPS = [c for c in CHIPS if c in wanted]
        SYSTEM_TABLES = [table for table in SYSTEM_TABLES if table in wanted]
        extract_public_values = "PublicValues" in wanted
        WITNESS_OPERATIONS = [o for o in WITNESS_OPERATIONS if o in wanted]
        TRACE_CHIPS = {c: w for c, w in TRACE_CHIPS.items() if f"{c}Trace" in wanted}
        print(f"EXTRACT_ONLY → operations={OPERATIONS}, chips={CHIPS}, "
              f"system={SYSTEM_TABLES}, publicValues={extract_public_values}, "
              f"witness={WITNESS_OPERATIONS}, trace={list(TRACE_CHIPS)}")

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

    owner = resolve_ownership(emitted)
    print(f"Resolved ownership for {len(owner)} structs.")

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
    written = 2
    for carrier, (carrier_donor, carrier_structs) in STRUCT_CARRIERS.items():
        if carrier_donor not in discovery:
            continue
        print(f"Processing struct carrier {carrier}")
        try:
            _write(os.path.join(EXTRACTED_DIR, f"{carrier}.lean"),
                   render_struct_carrier(carrier, carrier_donor, carrier_structs,
                                         discovery[carrier_donor]))
            written += 1
        except Exception as e:  # noqa: BLE001
            raise SystemExit(f"struct-carrier render {carrier} failed: {e}")
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
            if chip in CHIP_ORACLES:
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
                       render_chip_oracle(chip, oracle_body, discovery, oracle_imports))
            else:
                skips, imports = reuse_for(chip, emitted[chip], owner, discovery[chip])
                body = run_constraint_compiler(sp1_dir, chip=chip, reuse=skips) if skips else discovery[chip]
                _write(os.path.join(EXTRACTED_DIR, f"{chip}Chip.lean"), render_chip(chip, imports, body))
            written += 1
        except Exception as e:  # noqa: BLE001 — best-effort, continue with the rest
            print(f"  ✗ Error: {e}")
            if chip in CHIP_ORACLES:
                required_failures.append(f"chip oracle render {chip}: {e}")

    for table, output in system_outputs.items():
        print(f"Processing system table {table}")
        _write(os.path.join(EXTRACTED_DIR, "SystemOracle", f"{table}.lean"), output)
        written += 1

    if public_output is not None:
        print("Processing machine public values")
        _write(os.path.join(EXTRACTED_DIR, "SystemOracle", "PublicValues.lean"), public_output)
        written += 1

    # 2b. Transitional operation witness-vector pass. New conformance batteries belong in the
    #     whole-chip pass below; this list only supports unmigrated consumers.
    for op in WITNESS_OPERATIONS:
        print(f"Processing witness vectors for {op}")
        try:
            data = run_witness_vectors(sp1_dir, op)
            _write(os.path.join(WITNESS_DIR, f"{op}.lean"),
                   render_witness_vectors(op, data))
            written += 1
        except Exception as e:  # noqa: BLE001 — best-effort, continue with the rest
            print(f"  ✗ Error: {e}")

    # 2d. Whole-trace pass: dump the real-`generate_trace` conformance battery for the chips in
    #     `TRACE_CHIPS` (the `--chip` mode of the same binary). A requested trace failure is fatal:
    #     silently retaining stale vectors would undermine the extraction/conformance boundary. Under
    #     `EXTRACT_ONLY`, select these with `<Chip>Trace` (e.g. `AddTrace`) so they don't collide
    #     with the `CHIPS` constraint-extraction entries of the same name.
    for chip, (width, kind) in TRACE_CHIPS.items():
        print(f"Processing trace vectors for {chip}Chip")
        try:
            data = run_trace_vectors(sp1_dir, chip)
            _write(os.path.join(TRACEGEN_DIR, f"{chip}ChipTraceVectors.lean"),
                   render_trace_vectors(chip, width, kind, data))
            written += 1
        except Exception as e:  # noqa: BLE001 — best-effort, continue with the rest
            print(f"  ✗ Error: {e}")
            required_failures.append(f"whole-trace extraction {chip}: {e}")

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
