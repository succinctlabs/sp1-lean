<div align="center">

![SP1 Lean](./.github/assets/header.png)

Formal verification of SP1 zkVM arithmetization

</div>

## Overview

This repository provides **formal proofs for the arithmetization of the SP1 zkVM**, a zero-knowledge virtual machine for verifying RISC-V 64-bit computations. Using the Lean 4 theorem prover, we formally verify that the constraint systems used in SP1's AIR (Algebraic Intermediate Representation) correctly implement the RISC-V ISA semantics.

## What is SP1?

[SP1](https://github.com/succinctlabs/sp1) is a zero-knowledge virtual machine that generates proofs of RISC-V program execution. It uses AIR-based arithmetization to encode the computation into polynomial constraints that can be proven using cryptographic proof systems.

This repository focuses on **proving the correctness of those constraints** - ensuring that the polynomial equations actually enforce the intended RISC-V semantics.

## Repository Structure

The codebase is organized into three main libraries:

### SP1Foundations
Foundational definitions and utilities used throughout the verification:
- **Field arithmetic**: Finite field operations over the KoalaBear field
- **BitVec operations**: Bit vector manipulation and properties
- **Constraints**: Framework for defining and reasoning about AIR constraints
- **Register model**: RISC-V register state and operations
- **SailM monad**: Integration with RISC-V formal semantics from Sail
- **Memory model**: Memory consistency and checking infrastructure

### SP1Operations
Definitions of RISC-V instruction operations and their constraint encodings:
- **Readers**: Instruction decoding for different RISC-V types (R-type, I-type, J-type, etc.)
- **Operations**: Constraint definitions for individual operations (add, mul, shift, etc.)
- **CPU state management**: Program counter and state transitions

### SP1Chips
Formal correctness proofs for individual instruction chips:
- **Arithmetic**: Add, Sub, Mul, DivRem, Addw, Subw
- **Logical**: Bitwise operations (AND, OR, XOR)
- **Comparison**: Lt (less than) operations
- **Shifts**: ShiftLeft, ShiftRight
- **Memory**: Load/Store operations (byte, half, word, double)
- **Control flow**: Jal, Jalr, Branch instructions
- **Immediate**: Addi, UType instructions

Each chip contains:
- Constraint definitions that encode the operation
- A `spec_*` function defining the RISC-V semantics
- An `sp1_*` function defining the SP1 operation
- A `correct_*` theorem proving equivalence

## How It Works

For each RISC-V instruction, we prove that:

1. **The constraints are satisfiable**: When the instruction executes correctly, there exists an assignment to the constraint variables
2. **The constraints are sound**: Any satisfying assignment corresponds to a valid RISC-V execution

The proofs connect two representations:
- **RISC-V Semantics**: Formal specification from the Sail RISC-V model
- **SP1 Constraints**: Polynomial constraints used in the SP1 zkVM

Example from `AddChip.lean`:
```lean
theorem correct_add
  (Main : Vector (Fin KB) 34)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[33] = 1)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_add (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_add Main).run s
```

This theorem states that when all constraints hold, the SP1 add operation produces the same result as the RISC-V specification.

## Building

### Prerequisites
- [Lean 4](https://github.com/leanprover/lean4) (v4.23.0-rc2)
- [Lake](https://github.com/leanprover/lake) (Lean's build tool)

### Build Instructions

```bash
# Clone the repository
git clone https://github.com/succinctlabs/sp1-lean
cd sp1-lean

# Build the project
lake build
```

## Dependencies

- **[Mathlib](https://github.com/leanprover-community/mathlib4)**: Lean's mathematics library (v4.23.0-rc2)
- **[Lean_RV64D](https://github.com/succinctlabs/sail-riscv-lean)**: Formal RISC-V semantics extracted from Sail

## Current Status

The repository currently includes formal verification for:
- ✅ Arithmetic operations (add, sub, mul, div/rem)
- ✅ Bitwise operations
- ✅ Shift operations
- ✅ Comparison operations
- ✅ Memory operations (load/store)
- ✅ Control flow (branches, jumps)
- ✅ Immediate operations

## Contributing

Contributions are welcome! Please see the [contributing guidelines](CONTRIBUTING.md) for more information.

## Acknowledgments

This work builds on:
- The [Sail RISC-V specification](https://github.com/rems-project/sail-riscv)
- The [Lean 4 theorem prover](https://github.com/leanprover/lean4)
- The [Mathlib](https://github.com/leanprover-community/mathlib4) mathematics library
