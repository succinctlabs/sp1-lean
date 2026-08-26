#!/usr/bin/env python3
"""Fail closed when the supported 25-chip release surface drifts.

This is a source/inventory gate, not a semantic proof.  Kernel-checked coverage, faithfulness,
soundness, and real-row satisfiability remain in Lean; this script makes sure every physical chip
still has every one of those audit entry points and every committed conformance artifact.
"""

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parent.parent

# Canonical order is intentionally repeated from `InstructionChipId.all`: disagreement is the
# failure mode this independent inventory gate is meant to catch.
CHIPS = [
    ("add", "Add", "add_real_row_satisfiable"),
    ("addi", "Addi", "addi_real_row_satisfiable"),
    ("addw", "Addw", "addw_real_row_satisfiable"),
    ("sub", "Sub", "sub_real_row_satisfiable"),
    ("subw", "Subw", "subw_real_row_satisfiable"),
    ("bitwise", "Bitwise", "bitwise_and_real_row_satisfiable"),
    ("lt", "Lt", "lt_slt_true_real_row_satisfiable"),
    ("shiftLeft", "ShiftLeft", "shiftleft_sll_real_row_satisfiable"),
    ("shiftRight", "ShiftRight", "shiftright_srl_real_row_satisfiable"),
    ("jal", "Jal", "jal_real_row_satisfiable"),
    ("jalr", "Jalr", "jalr_real_row_satisfiable"),
    ("branch", "Branch", "branch_beq_taken_real_row_satisfiable"),
    ("uType", "UType", "utype_lui_real_row_satisfiable"),
    ("loadByte", "LoadByte", "loadbyte_real_row_satisfiable"),
    ("loadHalf", "LoadHalf", "loadhalf_real_row_satisfiable"),
    ("loadWord", "LoadWord", "loadword_real_row_satisfiable"),
    ("loadDouble", "LoadDouble", "loaddouble_real_row_satisfiable"),
    ("loadX0", "LoadX0", "loadx0_real_row_satisfiable"),
    ("storeByte", "StoreByte", "storebyte_real_row_satisfiable"),
    ("storeHalf", "StoreHalf", "storehalf_real_row_satisfiable"),
    ("storeWord", "StoreWord", "storeword_real_row_satisfiable"),
    ("storeDouble", "StoreDouble", "storedouble_real_row_satisfiable"),
    ("mul", "Mul", "mul_real_row_satisfiable"),
    ("divRem", "DivRem", "divrem_divu_real_row_satisfiable"),
    ("aluX0", "AluX0", "alux0_real_row_satisfiable"),
]


def fail(message: str) -> None:
    print(f"FAIL: {message}")
    failures.append(message)


def require(path: Path, role: str) -> None:
    if not path.is_file():
        fail(f"missing {role}: {path.relative_to(ROOT)}")


failures: list[str] = []
expected_ids = [chip_id for chip_id, _, _ in CHIPS]
expected_names = {name for _, name, _ in CHIPS}

identity_source = (ROOT / "SP1Clean/Model/InstructionChipId.lean").read_text()
enum_match = re.search(
    r"inductive InstructionChipId where\n(?P<body>.*?)\nderiving", identity_source, re.S
)
if enum_match is None:
    fail("could not parse InstructionChipId constructors")
else:
    actual_ids = re.findall(r"^\s*\|\s*([A-Za-z0-9_]+)\s*$", enum_match.group("body"), re.M)
    if actual_ids != expected_ids:
        fail(f"InstructionChipId order is {actual_ids}, expected {expected_ids}")

oracle_dir = ROOT / "SP1Clean/Extracted/ChipOracle"
actual_oracles = {path.stem for path in oracle_dir.glob("*.lean")}
if actual_oracles != expected_names:
    fail(
        "whole-chip oracle inventory differs: "
        f"missing={sorted(expected_names - actual_oracles)}, "
        f"extra={sorted(actual_oracles - expected_names)}"
    )

dump_names = {path.name.removesuffix(".dump.json") for path in
              (ROOT / "export/sp1dump").glob("*.dump.json")}
if dump_names != expected_names:
    fail(
        "SP1 dump inventory differs: "
        f"missing={sorted(expected_names - dump_names)}, extra={sorted(dump_names - expected_names)}"
    )

for suffix in ("manifest.json", "rowmap.json", "witgen.json"):
    actual = {path.name.removesuffix(f".{suffix}") for path in
              (ROOT / "export/witgen").glob(f"*.{suffix}")}
    if actual != expected_names:
        fail(
            f"witgen {suffix} inventory differs: "
            f"missing={sorted(expected_names - actual)}, extra={sorted(actual - expected_names)}"
        )

nonvacuity_source = (ROOT / "SP1CleanTest/NonVacuityReal.lean").read_text()
for _, name, anchor in CHIPS:
    chip = f"{name}Chip"
    require(ROOT / f"SP1Clean/Extracted/ChipOracle/{name}.lean", "whole-chip oracle")
    require(ROOT / f"SP1Clean/Faithful/{chip}.lean", "whole-chip faithfulness anchor")
    require(ROOT / f"SP1Clean/Proofs/Chips/{chip}/Formal.lean", "formal chip proof")
    require(ROOT / f"SP1Clean/Proofs/Chips/{chip}/Bridge.lean", "Sail bridge")
    require(ROOT / f"SP1Clean/Proofs/Chips/{chip}/Complete.lean", "trace compiler realization")
    if name in {"ShiftLeft", "ShiftRight", "DivRem"}:
        require(ROOT / f"SP1Clean/Proofs/Chips/{chip}/Defs.lean", "documented chip definition")
    else:
        require(ROOT / f"SP1Clean/Native/Chips/{chip}/Defs.lean", "native chip definition")
    if re.search(rf"^theorem\s+{re.escape(anchor)}\b", nonvacuity_source, re.M) is None:
        fail(f"missing real-row satisfiability anchor `{anchor}` for {chip}")

if failures:
    print(f"FAIL: release surface has {len(failures)} issue(s)")
    sys.exit(1)

print(
    "PASS: 25-chip release surface is complete "
    "(identity/order, native definitions, formal/bridge/completeness proofs, whole-chip oracles, "
    "faithfulness anchors, real-row models, dumps, and witgen artifacts)"
)
