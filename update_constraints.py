#!/usr/bin/env python3

# Use gzgz/rv64-operationize branch for sp1-wip!

import os
import subprocess
import re
from typing import List, Tuple, Optional

# List of (chip_name, optional_operation_name, prefix_path)
CONSTRAINTS_LIST: List[Tuple[str, Optional[str], str]] = [
    # Add your chips and operations here
    # Example entries:
    ("Add", None, ""),  # Chip-level constraints
    ("Addi", None, ""),
    ("Addw", None, ""),
    ("Bitwise", None, ""),
    ("Jalr", None, ""),
    ("ShiftLeft", None, ""),
    ("ShiftRight", None, ""),
    ("DivRem", None, ""),
    ("Lt", None, ""),
    ("Mul", None, ""),
    ("Sub", None, ""),
    ("Subw", None, ""),

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
    ("Bitwise", "ALUTypeReader", "Reader"),
]

def run_constraint_compiler(sp1_dir: str, chip: str, operation: Optional[str] = None) -> str:
    """Run the sp1-constraint-compiler and return its output."""
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

    # Find the start and end markers
    start_idx = None
    end_idx = None

    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped == "section constraints":
            start_idx = i
        elif stripped == "end constraints" and start_idx is not None:
            end_idx = i
            break

    # Validate we found both markers
    if start_idx is None:
        raise ValueError(f"Could not find 'section constraints' marker in {file_path}")
    if end_idx is None:
        raise ValueError(f"Could not find 'end constraints' marker after 'section constraints' in {file_path}")

    # Ensure new_constraints ends with newline
    if new_constraints and not new_constraints.endswith('\n'):
        new_constraints += '\n'

    # Reconstruct the file with new constraints
    new_lines = lines[:start_idx + 1] + [new_constraints] + lines[end_idx:]

    with open(file_path, 'w') as f:
        f.writelines(new_lines)

def main():
    # Get SP1_DIR from environment
    sp1_dir = os.environ.get('SP1_DIR')
    if not sp1_dir:
        raise ValueError("SP1_DIR environment variable not set. Also make sure sp1-wip is gzgz/rv64-operationize")

    for chip, operation, prefix in CONSTRAINTS_LIST:
        print(f"Processing {chip}" + (f" - {operation}" if operation else ""))

        try:
            # Run the constraint compiler
            constraints_output = run_constraint_compiler(sp1_dir, chip, operation)

            # Determine the output file path
            if operation is None:
                # Chip-level constraints
                file_path = f"SP1Chips/{chip}/Constraints.lean"
            else:
                # Operation-level constraints
                if prefix:
                    file_path = f"SP1Operations/{prefix}/{operation}/Constraints.lean"
                else:
                    file_path = f"SP1Operations/{operation}/Constraints.lean"

            # Update the constraints in the file
            update_constraints_in_file(file_path, constraints_output)
            print(f"  ✓ Updated {file_path}")

        except Exception as e:
            print(f"  ✗ Error: {e}")

if __name__ == "__main__":
    main()
