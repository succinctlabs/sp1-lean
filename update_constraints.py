#!/usr/bin/env python3

import os
import subprocess
import re
from typing import Dict, List, Tuple, Optional

# Operations/readers whose `Constraints.lean` is emitted as parametric over
# `{F : <universe>} [Field F]` instead of `Fin KB`-bound. The struct files
# (in `<op>/Operation.lean`) are hand-written and parameterized over
# `(F : <universe>)` already; this post-processor rewrites the upstream's
# `Fin KB` output to match. Two universes occur because `Word T` is defined
# over `T : Type 0`, so any operation taking a `Word` parameter must use
# `Type` (not `Type*`).
# Readers with `program` clauses also need `[CoeHead F ℕ]` so
# `Opcode.ofNat opcode` (which takes `ℕ`) elaborates against generic `F`;
# `Coe (Fin n) ℕ` and `Coe (ZMod p) ℕ` instances live in `Field.lean`.
# Keyed by `(chip, operation)`. Value is `(universe, needs_coe_head)`.
PARAMETRIC_OPS: Dict[Tuple[str, str], Tuple[str, bool]] = {
    ("DivRem", "IsZeroOperation"): ("Type*", False),
    ("DivRem", "IsZeroWordOperation"): ("Type", False),
    ("DivRem", "IsEqualWordOperation"): ("Type", False),
    ("Lt", "U16CompareOperation"): ("Type*", False),
    ("Mul", "U16MSBOperation"): ("Type*", False),
    ("Add", "CPUState"): ("Type*", False),
    ("Add", "RTypeReader"): ("Type", True),
    ("Addi", "ITypeReader"): ("Type", True),
    ("UType", "JTypeReader"): ("Type", True),
    ("Bitwise", "ALUTypeReader"): ("Type", True),
}

# List of (chip_name, optional_operation_name, prefix_path)
CONSTRAINTS_LIST: List[Tuple[str, Optional[str], str]] = [
    # Add your chips and operations here
    
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
    """Run the sp1-constraint-compiler and return its output."""
    cmd = ["cargo", "run", "-p", "sp1-constraint-compiler", "--", "--chip", chip, "--format", "lean"]

    if operation:
        cmd.extend(["--operation", operation])

    result = subprocess.run(cmd, cwd=sp1_dir, capture_output=True, text=True)

    if result.returncode != 0:
        raise RuntimeError(f"Command failed: {result.stderr}")

    return result.stdout

def apply_parametric_post_process(
    text: str, op_name: str, universe: str, needs_coe_head: bool
) -> str:
    """Rewrite Fin KB-typed upstream output into `{F : universe} [Field F]`-parametric form.

    The operations/readers in `PARAMETRIC_OPS` have hand-written struct files
    declared over `(F : <universe>)`. The upstream emitter still produces
    `Fin KB`-bound Lean for them (parametric emission lives here, not upstream,
    until upstream grows a corresponding flag). Substitutions:

    1. `(Fin KB)` → `F` — covers `Word (Fin KB)`, `Vector (Fin KB) N`,
       `SP1ConstraintList (Fin KB)`, and parenthesized field-type uses.
    2. `Fin KB` → `F` — covers bare `let X : Fin KB := ...` annotations after
       step 1 has handled all parenthesized forms.
    3. Add `{F : <universe>} [Field F]` (and `[CoeHead F ℕ]` for readers
       with `program` clauses) to the `def constraints` line.
    4. Add ` F` to the cols struct parameter so `cols : <op_name>` becomes
       `cols : <op_name> F`.
    """
    text = text.replace("(Fin KB)", "F")
    text = text.replace("Fin KB", "F")
    sig_extras = f"{{F : {universe}}} [Field F]"
    if needs_coe_head:
        sig_extras += " [CoeHead F ℕ]"
    text = text.replace(
        "@[irreducible] def constraints",
        f"@[irreducible] def constraints {sig_extras}",
    )
    text = text.replace(
        f"(cols : {op_name})",
        f"(cols : {op_name} F)",
    )
    return text

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
        raise ValueError("SP1_DIR environment variable not set.")

    for chip, operation, prefix in CONSTRAINTS_LIST:
        print(f"Processing {chip}" + (f" - {operation}" if operation else ""))

        try:
            # Run the constraint compiler
            constraints_output = run_constraint_compiler(sp1_dir, chip, operation)

            # Apply field-parametric post-process for ops/readers in PARAMETRIC_OPS
            if operation is not None:
                entry = PARAMETRIC_OPS.get((chip, operation))
                if entry is not None:
                    universe, needs_coe_head = entry
                    constraints_output = apply_parametric_post_process(
                        constraints_output, operation, universe, needs_coe_head
                    )

            # Determine the output file path
            if operation is None:
                # Chip-level constraints
                # file_path = f"SP1Chips/{chip}/{prefix}/Constraints.lean"
                file_path = os.path.join("SP1Chips", prefix, chip, "Constraints.lean")
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
