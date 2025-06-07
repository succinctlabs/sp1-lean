# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

SP1-Lean is a formal verification framework for the SP1 zkVM (Zero-Knowledge Virtual Machine) written in Lean 4. It formally verifies the correctness of SP1's RISC-V execution model and constraint system using mathematical proofs.

## Build and Development Commands

```bash
# Build entire project
lake build

# Compile single file with full output
lake lean -q <file.lean>

# Check specific module
lake build SP1Foundations
lake build SP1Operations  
lake build SP1Chips
```

## Architecture Overview

The codebase is organized into three layered libraries:

### 1. SP1Foundations - Core Mathematical Abstractions
- **Field.lean**: BabyBear finite field (prime 2013265921) with arithmetic operations
- **Unsigned.lean**: Constrained unsigned types (U1, U8, U16) wrapping BabyBear elements
- **Word.lean**: 32-bit words as pairs of limbs with conversion functions
- **Constraint.lean**: SP1Constraint system with `assertZero` and `sendAirInteraction_byte`
- **Interaction.lean**: Air interaction datatypes for lookup arguments
- **ByteOpcode.lean**: Byte-level operation specifications

### 2. SP1Operations - Individual CPU Operations
Each operation follows the constraint-specification pattern:
- Structure holding outputs/intermediates
- `spec` function defining mathematical correctness
- `constraints` function producing field constraints
- Correctness theorem proving constraints imply specification

Key operations: AddOperation, AndOperation, IsZeroOperation, SubOperation, OrOperation, XorOperation, MSBOperation

### 3. SP1Chips - Integrated Chip Implementations
- **AddChip.lean**: Combines CPUState, RTypeReader, and AddOperation for complete ADD instruction verification
- Integrates with RISC-V specification via Lean_RV32D dependency

## Design Patterns

### Constraint-Specification Pattern
Every operation uses this structure:
```lean
structure Operation where
  -- fields for outputs/intermediates

def spec (op : Operation) (inputs) (is_real : U1) : Prop := -- mathematical spec
def constraints (op : Operation) (inputs) (is_real : U1) : List SP1Constraint := -- field constraints  
theorem correct : constraints → spec -- correctness proof
```

### Conditional Execution
All constraints are gated by `is_real : U1` parameter to handle both real execution and padding in the same constraint system.

### Air Interactions  
Byte-level operations use algebraic intermediate representation (AIR) with lookup tables for efficient constraint verification.

## Proof Strategy Guidelines

Based on PROMPT.md, follow these practices:
- Use structured case analysis with `sorry` placeholders for complex proofs
- Apply automated tactics: `omega`, `aesop`, `linarith`, `ring` for arithmetic
- Convert BabyBear operations to natural numbers before automation
- Prove constraint equivalence to idealized mathematical properties

## Key Dependencies

- **mathlib**: Lean's mathematical library
- **Lean_RV32D**: RISC-V specification from sail-rv32d-lean  
- **aesop**: Automated proof search
- Lean toolchain: 4.21.0-rc3

## Working with Field Elements

BabyBear field elements require careful handling:
- Prime: 2013265921
- Use `.val` to extract underlying natural number
- Apply field simplification lemmas before automated tactics
- Unsigned types (U1, U8, U16) wrap BabyBear with range constraints