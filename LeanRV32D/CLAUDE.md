# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a RV32D RISC-V specification and model implementation in Lean 4, generated from the official [riscv/sail-riscv](https://github.com/riscv/sail-riscv) repository. The codebase contains a complete 32-bit RISC-V processor model with double-precision floating-point support (RV32D).

## Build System and Common Commands

This project uses Lake (Lean's build system):

- **Build the project**: `lake build`
- **Run the main executable**: `lake exe run`
- **Check all files**: `lake build LeanRV32D`

## Architecture Overview

### Core Structure
- **Main entry point**: `LeanRV32D.lean` - imports all modules and sets up the execution environment with custom options for large computations
- **Execution entry**: `LeanRV32D/Main.lean` - contains the main RISC-V processor loop and initialization

### Key Components
- **Sail Framework**: Located in `LeanRV32D/Sail/` - provides the foundational BitVec operations, monadic state management, and other utilities that the generated RISC-V model depends on
- **RISC-V Instructions**: Multiple `RiscvInsts*.lean` files implement instruction semantics for different extensions (base, M, F, D, V extensions, Zba, Zbb, etc.)
- **RISC-V Types**: `RiscvTypes*.lean` files define processor state, register types, and ISA-specific data structures
- **Memory System**: `RiscvVmem*.lean` files implement virtual memory, TLB, and page table walking
- **Register Management**: `RiscvRegs.lean`, `RiscvExtRegs.lean`, etc. handle different register file access patterns

### Generated Code Characteristics
- Generated from Sail specification language, so code patterns follow Sail conventions
- Heavy use of monadic operations (`SailM` monad) for state management
- Extensive bit vector operations for instruction encoding/decoding
- Custom memory and register access primitives

## Development Notes

### Performance Configuration
The project requires increased Lean limits due to the complexity of the processor model:
- `maxHeartbeats`: 1,000,000,000
- `maxRecDepth`: 1,000,000
- Stack size: 400,000 (via `--tstack=400000`)

### Linting Configuration
- Unused variable linting is disabled
- Style name checking is disabled for the library
- Unused match alternatives are ignored

These settings are necessary because the generated code from Sail may not follow typical Lean style guidelines.