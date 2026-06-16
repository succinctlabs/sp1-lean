#!/usr/bin/env python3

"""Regenerate `SP1Clean/Extracted/<Operation>.lean` and `…/<Chip>Chip.lean` from the
upstream sp1-constraint-compiler — with **auto-derived** sub-struct reuse.

Adapted from sp1-lean's `update_constraints.py`. The upstream compiler emits field-generic,
clean-native-ready Lean directly — both the operation/chip **column struct** and the
**`constraints` def** (`{F : Type} [Field F] [CoeHead F ℕ]`, `Word F`, `SP1ConstraintList F`,
`.send (.byte (ByteOpcode.ofNat n) …) mult`). This script runs the compiler, sandwiches its
output between a fixed clean-native header (imports + `namespace SP1Clean.Extracted` +
`open SP1Clean`) and footer, and writes the whole file.

**Why auto-derive?** Each `Extracted/` file must own exactly one column struct; a module that
composes sub-operations imports their already-generated modules (`--reuse-struct <Name>`)
instead of re-emitting them. Rather than hand-maintain a per-entry reuse list, this script:

  1. *Discovery pass* — runs the compiler for every module with NO reuse and parses which
     `structure <Name>` blocks each emits, building a global struct→owning-module map (seeded by
     `STRUCT_OWNERSHIP` for the struct≠module / shared-struct cases). Collisions fail loudly.
  2. *Emit pass* — for each module, reuse = every struct it emits that another module owns; those
     are passed as `--reuse-struct` and their owners are imported. The compiler re-runs and the
     file is written.

So **adding a chip is one line** in `CHIPS` (and any new sub-ops in `OPERATIONS`); the reuse
wiring is computed. The shared `SP1Constraint`/`ByteOpcode`/`Opcode` datatype lives in
`SP1Clean/Foundations/SP1Constraint.lean` (already models every emitted opcode +
interaction); the faithfulness anchors that tie each generated `constraints` to the native
gadget's spec live in `SP1Clean/Faithful/`.

Usage: `SP1_DIR=/path/to/sp1 python3 update_extracted.py`
(default `SP1_DIR` is `../sp1`, a sibling checkout of the sp1 repo).
"""

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

# Operation modules with a witness-vector dumper in the `witness_vectors` binary → an extra
# `WitnessTests/<name>WitnessVectors.lean` (conformance vectors from SP1's real `populate`) plus a
# `WitnessTests/<name>Witness.lean` anchor (hand-written). An op here MUST also be in `OPERATIONS`.
# Tying `populate` is a *completeness/conformance* property: it cannot be symbolically extracted
# like `eval` (native imperative code, data-dependent control flow), so we dump real-`populate`
# outputs on a fixed input battery and `#guard` the Lean witness reproduces them. Grow as the
# binary's per-op dispatch grows (Add first, then Sub/Bitwise, then Mul/Lt).
WITNESS_OPERATIONS: List[str] = [
    "AddOperation",
    "SubOperation",
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
    "AddOperation": ["a_limbs", "b_limbs", "value"],
    "SubOperation": ["a_limbs", "b_limbs", "value"],
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

# Operation modules emitted ALSO as the Clean-native **circuit form** (`Inputs` + `main` +
# `ElaboratedCircuit`) → an extra `Extracted/<name>Circuit.lean`. Only pure-assertion, byte-bus
# **leaf** operations (Rust `eval` returns `Shape::Unit`, composes no sub-ops) qualify: the emitted
# `main` IS the extracted artifact, so the gadget's soundness/completeness are faithful **by
# construction** (no separate `asserts`/`interactions` bridge — the bridge stays only as a helper for
# the not-yet-migrated chip-level faithfulness). An op here MUST also be in `OPERATIONS`. Grow as
# more byte-bus leaves migrate.
CIRCUIT_OPERATIONS: List[str] = [
    "AddOperation",
    "SubOperation",
    "U16CompareOperation",
    "U16MSBOperation",
    "BitwiseOperation",
    # Composition chain (`IsEqualWord` composes `IsZeroWord` composes `IsZeroOperation`): each emits
    # `assertion <sub>.circuit ⟨…⟩` for its sub-operation (the first composed circuit-form ops).
    "IsZeroOperation",
    "IsZeroWordOperation",
    "IsEqualWordOperation",
    # Word add/sub W-variants: each composes `U16MSBOperation.circuit` (`assertion`) on the high result
    # limb + two byte-bus range pulls + two gated carries (same composed circuit-form as the chain above).
    "AddwOperation",
    "SubwOperation",
    # 48-bit (3-limb) address add: `Add`-shaped but the high carry runs against `0` and only the three
    # low limbs are byte-bus range-pulled (the result keeps 48 bits).
    "AddrAddOperation",
    # Unsigned word less-than: composes `U16CompareOperation.circuit` (`assertion`) on the
    # most-significant differing limb pair; the flag/limb-selection constraints carry no byte pulls of
    # their own (all byte-bus activity lives inside the composed `U16CompareOperation`).
    "LtOperationUnsigned",
    # Signed/unsigned word less-than: composes two `U16MSBOperation.circuit` (`assertion`, gated by
    # `is_signed`) on the high limbs + one `LtOperationUnsigned.circuit` (`assertion`, free `is_real`) on
    # the sign-adjusted words; the own tail is the five selector/gate asserts, no byte pulls of its own.
    "LtOperationSigned",
]

# Chip modules → `Extracted/<chip>Chip.lean` (column struct `<chip>Cols` + composed constraints).
CHIPS: List[str] = [
    "Add", "Addi", "Addw", "Sub", "Subw", "Bitwise", "Lt", "Mul", "DivRem", "AluX0",
    "ShiftLeft", "ShiftRight", "Branch", "Jal", "Jalr", "UType",
    "LoadByte", "LoadHalf", "LoadWord", "LoadDouble", "LoadX0",
    "StoreByte", "StoreHalf", "StoreWord", "StoreDouble",
]

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
    # natural operation owner — the collision handler in `resolve_ownership` assigns them to the
    # first emitting chip (LoadByte) and the rest import that chip module.
}

DEFAULT_SP1_DIR = "../sp1"
# The SP1 commit the checked-in `Extracted/`/`WitnessTests/` files were generated from
# (`dtumad/clean-native`, v6.2.2-20-g9d249b8d4). `main()` refuses to extract from a different
# checkout unless `SP1_ALLOW_UNPINNED=1` is set — bump this constant together with the
# regenerated files so the extraction provenance is always recorded in-repo.
SP1_PINNED_COMMIT = "9d249b8d4fb7d00156bf77f5d295d1dbcaaf4136"
EXTRACTED_DIR = os.path.join("SP1Clean", "Extracted")
WITNESS_DIR = os.path.join("SP1Clean", "Extracted", "WitnessVectors")

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


# ── Compiler driver ─────────────────────────────────────────────────────────────────────────

def run_constraint_compiler(
    sp1_dir: str,
    chip: str = None,
    operation: str = None,
    reuse: Sequence[str] = (),
    fmt: str = "lean",
) -> str:
    """Run the sp1-constraint-compiler and return its stdout. Pass `operation` to extract an
    operation standalone (searched across all chips), or `chip` to extract a chip. `fmt` selects the
    output format — `lean` (the two-list `asserts`/`interactions` form) or `lean-circuit` (the
    `Inputs` + `main` + `ElaboratedCircuit` form, operation-only)."""
    cmd = ["cargo", "run", "-q", "-p", "sp1-constraint-compiler", "--bin", "sp1-constraint-compiler",
           "--", "--format", fmt]
    if chip is not None:
        cmd += ["--chip", chip]
    if operation is not None:
        cmd += ["--operation", operation]
    for name in reuse:
        cmd += ["--reuse-struct", name]
    result = subprocess.run(cmd, cwd=sp1_dir, capture_output=True, text=True)
    if result.returncode != 0:
        target = operation if operation is not None else f"{chip} (chip)"
        raise RuntimeError(f"compiler failed for {target}:\n{result.stderr}")
    return result.stdout


def _emitted_structs(body: str) -> List[str]:
    """The column-struct names a compiler fragment emits (in source order)."""
    return _STRUCT_RE.findall(body)


# ── Ownership resolution ────────────────────────────────────────────────────────────────────

def _default_owner(struct: str) -> str:
    """Owner of a struct under the default rules (no `STRUCT_OWNERSHIP` entry)."""
    if struct in OPERATIONS:
        return struct
    if struct.endswith("Cols") and struct[:-len("Cols")] in CHIPS:
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
            order = {name: i for i, name in enumerate([*OPERATIONS, *CHIPS])}
            owner[struct] = min(emitters, key=lambda m: order.get(m, len(order)))
    return owner


def _import_module(owner: str) -> str:
    """The `Extracted.<…>` module file name for an owner — a chip owner lives in `<chip>Chip`."""
    return f"{owner}Chip" if owner in CHIPS else owner


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
        if called in OPERATIONS:
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


# Ops whose `channelsLawful` the Clean default tactic cannot close (composed sub-assertion channel
# lists need unfolding); the normalizer injects the override since the emitter never produces one.
CHANNELS_LAWFUL_OVERRIDES: Dict[str, str] = {
    "LtOperationSigned":
        "  channelsLawful := by\n"
        "    simp [circuit_norm, main, LtOperationUnsigned.circuit, U16MSBOperation.circuit]\n",
}


def _normalize_circuit_api(operation: str, body: str) -> str:
    """Post-process the compiler's circuit-form output onto the pinned Clean API (closes the
    release-audit TB-9 reproducibility gap). The `sp1-constraint-compiler` at the SP1 pin emits

    1. an `ElaboratedCircuit` instance with `name`/`main` **fields** — an API from a transient window
       of Clean main (`60665ed0`, later reworked); the pinned Clean (PR #398 head) takes `main` as a
       class *parameter* and has no `name` field;
    2. `channelsWith*_eq` rfl-lemmas in bare `(ElaboratedCircuit.<field> Inputs unit : …)` form, which
       does not elaborate against the parameterized instance; and
    3. the pre-#398 custom gating names (`byteChannel.gatedReceive`/`byteChannel.toRawGated`), which
       the W9 migration replaced with the upstream primitives (`pullIf` / gated `toRaw`).
    """
    body = body.replace(
        "instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where\n"
        f"  name := \"SP1CleanNative.{operation}\"\n"
        "  main := main\n",
        "instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where\n"
        + CHANNELS_LAWFUL_OVERRIDES.get(operation, ""))
    for which in ("channelsWithGuarantees", "channelsWithRequirements"):
        body = body.replace(
            f"    (ElaboratedCircuit.{which} Inputs unit : List (RawChannel (ZMod p)))",
            f"    ((elaborated (p := p)).{which} : List (RawChannel (ZMod p)))")
    body = body.replace("byteChannel.gatedReceive", "byteChannel.pullIf")
    body = body.replace("byteChannel.toRawGated", "byteChannel.toRaw")
    # A bare numeral seeding an accumulator chain (`let E16 := 0 + cols…`) fails to elaborate (the
    # `0`'s type can't be synthesized bottom-up inside the un-ascribed `let`); pin it explicitly.
    body = body.replace(":= 0 + ", ":= (0 : Expression (ZMod p)) + ")
    return body


def render_circuit(operation: str, body: str) -> str:
    """Wrap an operation's `--format lean-circuit` body (the `Inputs` + `main` + `ElaboratedCircuit`)
    in the clean-native circuit-module header/footer. Written to `Operations/<op>/Extracted.lean` (the
    auto-generated member of the op's four-file directory). It imports the op's already-extracted column
    struct (`Extracted.<op>`, the nested `cols` field type) plus the byte/channel foundations and
    Clean's circuit machinery, opens `Extracted` so the bare `cols` struct type resolves, and binds
    the `variable {p}` field block the `main`/`ElaboratedCircuit` need. The `namespace
    SP1Clean.<op>` is independent of the file path, so this body is location-agnostic."""
    body = _normalize_circuit_api(operation, body.strip())
    doc = (
        f"/-! # AUTO-GENERATED circuit form — do not edit by hand.\n\n"
        f"SP1's `{operation}::eval` as a Clean `Circuit`: the `Inputs` struct (the `eval` params\n"
        f"verbatim — the column struct nested as `cols`), the `main` do-block, and the\n"
        f"`ElaboratedCircuit` instance + `@[circuit_norm]` rfl-lemmas. Generated by\n"
        f"`update_extracted.py` from the `sp1-constraint-compiler` (`--operation {operation} --format\n"
        f"lean-circuit`). This *is* the faithful artifact the gadget's soundness/completeness run\n"
        f"against — no separate `asserts`/`interactions` bridge. Regenerate with\n"
        f"`SP1_DIR=… python3 update_extracted.py`. -/"
    )
    # A composed op's `main` calls `assertion <Sub>.circuit ⟨…⟩`; import each such sub-op's `Formal`
    # module (where `<Sub>.circuit : FormalAssertion` lives). Leaf ops have none.
    sub_circuits = sorted(set(re.findall(r"assertion\s+([A-Za-z_][A-Za-z0-9_]*)\.circuit", body)))
    # Byte-channel propagation: the compiler sets `channelsWith* := []` from the op's *own* byte pulls
    # only — it does not aggregate a composed sub-op's bus. So an op with no own pulls that composes a
    # bus-carrying sub (e.g. `LtOperationUnsigned` composing `U16CompareOperation`) is emitted with an
    # empty channel list, and Clean's `channelsLawful` then fails (the sub's `byteChannel` pull is live
    # in `main` but undeclared). Detect a bus-carrying sub from its already-emitted `Extracted.lean` and
    # promote the parent's channel lists + rfl-lemmas to `[byteChannel.toRaw]`.
    if "byteChannel.toRaw" not in body:
        for s in sub_circuits:
            sub_path = os.path.join("SP1Clean", "Extracted", "Circuit", f"{s}.lean")
            try:
                with open(sub_path, encoding="utf-8") as f:
                    sub_text = f.read()
                if "byteChannel.toRaw" in sub_text:
                    body = (body
                            .replace("channelsWithGuarantees := []",
                                     "channelsWithGuarantees := [byteChannel.toRaw]")
                            .replace("channelsWithRequirements := []",
                                     "channelsWithRequirements := [byteChannel.toRaw]")
                            .replace("= [] := rfl", "= [byteChannel.toRaw] := rfl"))
                    break
            except FileNotFoundError:
                pass
    sub_imports = "".join(
        f"import SP1Clean.Operations.{s}.Formal\n" for s in sub_circuits
    )
    header = (
        "import SP1Clean.Math.Word\n"
        "import SP1Clean.Model.Channels\n"
        "import SP1Clean.Model.ByteTable\n"
        f"import SP1Clean.Extracted.{operation}\n"
        + sub_imports
        + "import Clean.Circuit.Basic\n"
        "import Clean.Circuit.Subcircuit\n"
        "import Clean.Circuit.Channel\n"
        "import Clean.Gadgets.Equality\n"
        "import Clean.Utils.Tactics.ProvableStructDeriving\n\n"
        + doc + "\n\n"
        + LINTERS_OFF + "\n\n"
        + f"namespace SP1Clean.{operation}\n\n"
        + "open Circuit\n"
        + "open SP1Clean.Channels (byteChannel)\n"
        + "open SP1Clean.Extracted\n\n"
        + "variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]\n"
    )
    return header + "\n" + body + "\n\n" + f"end SP1Clean.{operation}\n"


def _bump_constraints_heartbeats(body: str, heartbeats: int = 1000000) -> str:
    """Prefix **each** generated `@[irreducible] def` (`asserts` / `interactions` / `value`) with a
    raised `maxHeartbeats`. Each def's `let` chain (with nested `#v[…][k]` projections through the
    column structs) is whnf-expensive and exceeds the 200k default; the largest operations (e.g.
    `MulOperation`, ~460 lets) exceed even 1M. Harmless where the default already suffices (Add/Sub)."""
    needle = "@[irreducible] def "
    return body.replace(needle, f"set_option maxHeartbeats {heartbeats} in\n{needle}")


def render_chip(chip: str, import_modules: Sequence[str], body: str) -> str:
    """Wrap a chip's compiler body in a module header that imports the reused operation
    column-struct modules."""
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
        f"check lives in `SP1Clean/WitnessTests/{operation}Witness.lean`. Regenerate with\n"
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


def _write(out_path: str, content: str) -> None:
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, "w") as f:
        f.write(content)
    print(f"  ✓ Wrote {out_path}")


# ── Orchestration ───────────────────────────────────────────────────────────────────────────

def main() -> None:
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

    os.makedirs(EXTRACTED_DIR, exist_ok=True)

    # `EXTRACT_ONLY=Name1,Name2,…` restricts this run to a subset of OPERATIONS/CHIPS/
    # WITNESS_OPERATIONS (a closed composition group) — used to regenerate just the files that
    # changed without rewriting every module. Reuse wiring stays correct as long as the subset is
    # closed under sub-operation composition (e.g. `Add` needs `AddOperation,CPUState,RTypeReader`).
    only = os.environ.get("EXTRACT_ONLY")
    if only:
        wanted = {name.strip() for name in only.split(",") if name.strip()}
        global OPERATIONS, CHIPS, WITNESS_OPERATIONS, CIRCUIT_OPERATIONS
        OPERATIONS = [o for o in OPERATIONS if o in wanted]
        CHIPS = [c for c in CHIPS if c in wanted]
        WITNESS_OPERATIONS = [o for o in WITNESS_OPERATIONS if o in wanted]
        CIRCUIT_OPERATIONS = [o for o in CIRCUIT_OPERATIONS if o in wanted]
        print(f"EXTRACT_ONLY → operations={OPERATIONS}, chips={CHIPS}, "
              f"witness={WITNESS_OPERATIONS}, circuit={CIRCUIT_OPERATIONS}")

    # 1. Discovery pass: which structs does each module emit with no reuse? Tolerate per-target
    #    compiler failures (e.g. a chip whose `<Chip>Cols` shape isn't yet composed in the
    #    compiler) — skip them, keep going, and report at the end.
    print("Discovery pass (emitting with no reuse to map struct ownership)…")
    discovery: Dict[str, str] = {}   # module → no-reuse body (successful targets only)
    emitted: Dict[str, List[str]] = {}
    skipped: Dict[str, str] = {}     # module → first-line reason
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

    owner = resolve_ownership(emitted)
    print(f"Resolved ownership for {len(owner)} structs.")

    # 2. Emit pass: re-run with the derived reuse, then render + write (successful targets only).
    written = 0
    for op in [o for o in OPERATIONS if o in emitted]:
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
            skips, imports = reuse_for(chip, emitted[chip], owner, discovery[chip])
            body = run_constraint_compiler(sp1_dir, chip=chip, reuse=skips) if skips else discovery[chip]
            _write(os.path.join(EXTRACTED_DIR, f"{chip}Chip.lean"), render_chip(chip, imports, body))
            written += 1
        except Exception as e:  # noqa: BLE001 — best-effort, continue with the rest
            print(f"  ✗ Error: {e}")

    # 2b. Witness-vector pass: dump real-`populate` conformance vectors for the ops that have a
    #     dumper in the `witness_vectors` binary. Best-effort per op (an op without a dumper just
    #     skips), so the constraint pass above is never blocked by this companion pass.
    for op in WITNESS_OPERATIONS:
        print(f"Processing witness vectors for {op}")
        try:
            data = run_witness_vectors(sp1_dir, op)
            _write(os.path.join(WITNESS_DIR, f"{op}.lean"),
                   render_witness_vectors(op, data))
            written += 1
        except Exception as e:  # noqa: BLE001 — best-effort, continue with the rest
            print(f"  ✗ Error: {e}")

    # 2c. Circuit-form pass: emit `Operations/<op>/Extracted.lean` (the `Inputs` + `main` +
    #     `ElaboratedCircuit`) for the byte-bus, pure-assertion leaf operations — the auto-generated
    #     member of the op's four-file directory (alongside the hand-written `Populate`/`RawSpec`/
    #     `Formal`). The nested `cols` column struct still comes from the op's shared
    #     `Extracted/<op>.lean` (imported), so this pass relies on the constraint pass above having
    #     written it. Best-effort per op.
    for op in CIRCUIT_OPERATIONS:
        print(f"Processing circuit form for {op}")
        try:
            body = run_constraint_compiler(sp1_dir, operation=op, fmt="lean-circuit")
            _write(os.path.join("SP1Clean", "Extracted", "Circuit", f"{op}.lean"),
                   render_circuit(op, body))
            written += 1
        except Exception as e:  # noqa: BLE001 — best-effort, continue with the rest
            print(f"  ✗ Error: {e}")

    # 3. Summary — what got written and which targets the compiler can't yet emit.
    print(f"\n== Wrote {written} module(s) to {EXTRACTED_DIR} ==")
    if skipped:
        print(f"== {len(skipped)} target(s) skipped (compiler can't emit yet): ==")
        for name, reason in skipped.items():
            print(f"   - {name}: {reason}")


if __name__ == "__main__":
    main()
