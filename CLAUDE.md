# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

SP1-Lean is a formal verification framework for the SP1 zkVM (Zero-Knowledge Virtual Machine) written in Lean 4. It formally verifies the correctness of SP1's RISC-V execution model and constraint system using mathematical proofs.

## Build and Development Commands

```bash
# Build entire project
lake build

# Build specific modules
lake build SP1Foundations
lake build SP1Operations  
lake build SP1Chips

# Compile single file with full output (useful for debugging)
lake lean -q <file.lean>

# Run tests
lake test

# Clean build artifacts
lake clean
```

## Architecture Overview

The codebase is organized into three main libraries plus RISC-V specifications:

### 1. SP1Foundations - Core Mathematical Abstractions
Located in `SP1Foundations/`:
- **Field.lean**: Defines `Fin BB` finite field where BB = 2013265921 (BabyBear prime)
- **Unsigned.lean**: Constrained unsigned types (U1, U8, U16) wrapping field elements
- **Word.lean**: 32-bit words as 4-element vectors with U64 bounds
- **Constraint.lean**: SP1Constraint system with `assertZero`, `send`, and `receive` operations
- **ByteOpcode.lean**: Byte-level operation specifications for AIR interactions
- **Opcode.lean**: RISC-V opcode definitions
- **Register.lean**: Register definitions and utilities
- **SP1State.lean**: SP1 execution state definitions
- **SailM.lean**: Monadic interface for RISC-V semantics
- **Tactics.lean**: Custom tactics like `extract_from_and`
- **BitVec.lean**: BitVector utilities
- **MemoryConsistency.lean**: Memory consistency model
- **Misc.lean**: Miscellaneous utilities

### 2. SP1Operations - Individual CPU Operations
Located in `SP1Operations/`:

#### Operation Pattern
Each operation follows a consistent structure:
- `Operation/` subfolder containing:
  - `Operation.lean`: Structure definition and specification
  - `Constraints.lean`: Field constraints and correctness theorem

#### Reader Pattern
Readers extract instruction fields:
- `Reader/` subfolder with similar structure
- Types: CPUState, RTypeReader, ITypeReader, ITypeReaderImmutable, JTypeReader, ALUTypeReader

#### Operation Categories:
- **Arithmetic**: AddOperation, SubOperation, MulOperation, AddwOperation, SubwOperation
- **Bitwise**: BitwiseOperation, BitwiseU16Operation  
- **Comparison**: IsZeroOperation, IsEqualWordOperation, IsZeroWordOperation, LtOperationSigned/Unsigned, U16CompareOperation
- **Conversion**: U16MSBOperation, U16toU8OperationSafe/Unsafe

### 3. SP1Chips - Integrated Chip Implementations
Located in `SP1Chips/`:

Each chip combines:
- CPU state management
- Instruction decoding (via readers)
- Operation execution
- Constraint generation

Chip structure:
- `<ChipName>Chip.lean`: Main chip implementation
- `<ChipName>/Constraints.lean`: Constraint definitions
- `<ChipName>/U16Composition.lean`: U16 bounds proofs (when applicable)

Available chips:
- **Arithmetic**: AddChip, AddiChip, AddwChip, SubChip, SubwChip, MulChip, DivRemChip
- **Bitwise**: BitwiseChip (handles AND/OR/XOR via selectors)
- **Branch**: BranchChip (handles BEQ, BNE, BLT, BGE, BLTU, BGEU)
- **Jump**: JalChip, JalrChip
- **Comparison**: LtChip
- **Shift**: ShiftLeftChip, ShiftRightChip
- **Upper**: UTypeChip (LUI/AUIPC)

### 4. RISC-V Specifications
Three variants from sail-generated specifications:
- **LeanRV32D/**: Full RV32 with double-precision floating point
- **LeanRV32IM/**: RV32 with integer and multiply extensions
- **LeanRV64IM/**: RV64 with integer and multiply extensions

## Design Patterns

### Constraint-Specification Pattern
Every operation uses this structure:
```lean
structure Operation where
  -- fields for outputs/intermediates

def spec (op : Operation) (inputs) (is_real : U1) : Prop := 
  -- mathematical specification

def constraints (op : Operation) (inputs) (is_real : U1) : List SP1Constraint := 
  -- field constraints that enforce the spec

theorem correct : constraints → spec  -- correctness proof
```

### Conditional Execution
All constraints are gated by `is_real : U1` parameter to handle both real execution and padding in the same constraint system.

### Air Interactions  
Four types of interactions for efficient constraint verification:
- **byte**: Lookup tables for byte operations
- **memory**: Memory read/write operations with address and data
- **program**: Instruction fetch with PC and decoded fields
- **state**: CPU state transitions

### U16 Composition Proofs
These proofs verify that all field elements respect 16-bit bounds when `is_real = 1`. 
**IMPORTANT**: If working on U16 composition proofs, see `U16_COMPOSITION_PROOF_GUIDE.md` for detailed patterns and examples.

## MCP Tool Integration

The project uses two MCP (Model Context Protocol) servers for enhanced Lean support:

1. **lean-lsp-mcp**: Provides LSP functionality
   - `lean_goal`: Check proof state at cursor
   - `lean_diagnostic_messages`: Get errors/warnings
   - `lean_hover_info`: Get type/documentation info
   - `lean_completions`: Code completion suggestions
   - `lean_build`: Build project and restart LSP

2. **LeanExplore**: Search mathlib theorems
   - `search`: Natural language theorem search
   - `get_by_id`: Retrieve specific theorems
   - `get_dependencies`: Find theorem dependencies

See `CLAUDE_SETUP.md` for installation instructions.

## Common Development Tasks

### Adding a New Operation
1. Create structure in `SP1Operations/Operation/<Name>Operation/Operation.lean`
2. Define `spec` function for mathematical behavior
3. Implement `constraints` in `SP1Operations/Operation/<Name>Operation/Constraints.lean`
4. Prove `correct` theorem showing constraints imply spec

### Adding a New Chip
1. Create main file `SP1Chips/<Name>Chip.lean`
2. Define `constraints` combining reader + operation constraints
3. Create `SP1Chips/<Name>/Constraints.lean` with constraint definitions
4. If needed, add `SP1Chips/<Name>/U16Composition.lean` for bounds proofs
5. Prove chip correctly implements RISC-V instruction semantics

### Working on U16 Composition Proofs
See `U16_COMPOSITION_PROOF_GUIDE.md` for comprehensive guidance on:
- Proof structure patterns
- Handling multi-operation chips with selectors
- Common tactics and lemmas
- Debugging strategies
- Examples from existing proofs

## Proof Strategy Guidelines

Based on PROMPT.md, follow these practices:
- Use structured case analysis with `sorry` placeholders for complex proofs
- Apply automated tactics: `omega`, `aesop`, `linarith`, `ring` for arithmetic
- Convert Fin BB operations to natural numbers before automation
- Prove constraint equivalence to idealized mathematical properties
- Use custom tactics like `extract_from_and` for decomposing hypotheses

## Key Dependencies

- **mathlib** (v4.22.0-rc2): Lean's mathematical library
- **Lean toolchain**: 4.21.0-rc3
- **aesop**: Automated proof search
- Python tools: `update_constraints.py` for constraint code generation

## Working with Field Elements

Fin BB field elements require careful handling:
- Prime: 2013265921 (BabyBear prime)
- Use `.val` to extract underlying natural number
- Apply field simplification lemmas before automated tactics
- Common bounds: 256 (U8), 65536 (U16), 2^32 (Word)
- Unsigned types (U1, U8, U16) wrap Fin BB with range constraints

## Important Files

- `lakefile.toml`: Build configuration
- `lean-toolchain`: Lean version specification  
- `U16_COMPOSITION_PROOF_GUIDE.md`: Comprehensive guide for U16 composition proofs
- `CLAUDE_SETUP.md`: MCP server setup instructions
- `requirements.txt`: Python dependencies
- `update_constraints.py`: Constraint code generation tool