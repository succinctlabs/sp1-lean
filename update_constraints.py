#!/usr/bin/env python3

"""Regenerate every `<section constraints> … <end constraints>` block in
SP1Chips and SP1Operations from the upstream constraint compiler.

The upstream compiler emits field-generic Lean directly (`{F : Type} [Field F]
[CoeHead F ℕ] (Main : Vector F N) : SP1ConstraintList F`) — this script is a
verbatim writer: run the compiler, splice the output back in. The old
`PARAMETRIC_OPS`/`PARAMETRIC_CHIPS` post-process was removed once upstream
became field-generic on its own (`crates/hypercube/src/ir/shape.rs`,
`func.rs`, `expr.rs`, `ast.rs`, `var.rs`, plus the binary in
`crates/core/compiler/src/main.rs`).
"""

import os
import subprocess
from typing import List, Optional, Tuple

# List of (chip_name, optional_operation_name, prefix_path)
CONSTRAINTS_LIST: List[Tuple[str, Optional[str], str]] = [
    # Chip-level constraints
    ("Add", None, ""),
    ("Addi", None, ""),
    ("Addw", None, ""),
    ("Bitwise", None, ""),
    ("Branch", None, ""),
    ("Jal", None, ""),
    ("Jalr", None, ""),
    ("ShiftLeft", None, ""),
    ("ShiftRight", None, ""),
    ("DivRem", None, ""),
    ("Lt", None, ""),
    ("Mul", None, ""),
    ("Sub", None, ""),
    ("Subw", None, ""),
    ("UType", None, ""),
    ("LoadByte", None, "Load"),
    ("LoadHalf", None, "Load"),
    ("LoadWord", None, "Load"),
    ("LoadDouble", None, "Load"),
    ("LoadX0", None, "Load"),
    ("StoreByte", None, "Store"),
    ("StoreHalf", None, "Store"),
    ("StoreWord", None, "Store"),
    ("StoreDouble", None, "Store"),

    # Operations
    ("Add", "AddOperation", "Operation"),
    ("Addw", "AddwOperation", "Operation"),
    ("Bitwise", "BitwiseOperation", "Operation"),
    ("Bitwise", "BitwiseU16Operation", "Operation"),
    ("Mul", "MulOperation", "Operation"),
    ("Sub", "SubOperation", "Operation"),
    ("Subw", "SubwOperation", "Operation"),
    ("Mul", "U16MSBOperation", "Operation"),
    ("Mul", "U16toU8OperationSafe", "Operation"),
    ("Bitwise", "U16toU8OperationUnsafe", "Operation"),
    ("LoadByte", "AddrAddOperation", "Operation"),
    ("LoadByte", "AddressOperation", "Operation"),

    # Compare operations
    ("DivRem", "IsEqualWordOperation", "Compare"),
    ("DivRem", "IsZeroWordOperation", "Compare"),
    ("DivRem", "IsZeroOperation", "Compare"),
    ("Lt", "LtOperationSigned", "Compare"),
    ("Lt", "LtOperationUnsigned", "Compare"),
    ("Lt", "U16CompareOperation", "Compare"),

    # Adapters/readers
    ("Add", "RTypeReader", "Reader"),
    ("Add", "CPUState", "Reader"),
    ("Addi", "ITypeReader", "Reader"),
    ("Branch", "ITypeReaderImmutable", "Reader"),
    ("Bitwise", "ALUTypeReader", "Reader"),
    ("UType", "JTypeReader", "Reader"),
]


def run_constraint_compiler(sp1_dir: str, chip: str, operation: Optional[str] = None) -> str:
    """Run the sp1-constraint-compiler and return its stdout."""
    cmd = ["cargo", "run", "-p", "sp1-constraint-compiler", "--", "--chip", chip, "--format", "lean"]
    if operation:
        cmd.extend(["--operation", operation])

    result = subprocess.run(cmd, cwd=sp1_dir, capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(f"Command failed: {result.stderr}")
    return result.stdout


def update_constraints_in_file(file_path: str, new_constraints: str):
    """Replace content between 'section constraints' and 'end constraints' markers."""
    with open(file_path, 'r') as f:
        lines = f.readlines()

    start_idx = None
    end_idx = None
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped == "section constraints":
            start_idx = i
        elif stripped == "end constraints" and start_idx is not None:
            end_idx = i
            break

    if start_idx is None:
        raise ValueError(f"Could not find 'section constraints' marker in {file_path}")
    if end_idx is None:
        raise ValueError(
            f"Could not find 'end constraints' marker after 'section constraints' in {file_path}"
        )

    if new_constraints and not new_constraints.endswith('\n'):
        new_constraints += '\n'

    new_lines = lines[:start_idx + 1] + [new_constraints] + lines[end_idx:]
    with open(file_path, 'w') as f:
        f.writelines(new_lines)


def main():
    sp1_dir = os.environ.get('SP1_DIR')
    if not sp1_dir:
        raise ValueError("SP1_DIR environment variable not set.")

    for chip, operation, prefix in CONSTRAINTS_LIST:
        print(f"Processing {chip}" + (f" - {operation}" if operation else ""))

        try:
            constraints_output = run_constraint_compiler(sp1_dir, chip, operation)

            if operation is None:
                file_path = os.path.join("SP1Chips", prefix, chip, "Constraints.lean")
            elif prefix:
                file_path = f"SP1Operations/{prefix}/{operation}/Constraints.lean"
            else:
                file_path = f"SP1Operations/{operation}/Constraints.lean"

            update_constraints_in_file(file_path, constraints_output)
            print(f"  ✓ Updated {file_path}")
        except Exception as e:
            print(f"  ✗ Error: {e}")


if __name__ == "__main__":
    main()
