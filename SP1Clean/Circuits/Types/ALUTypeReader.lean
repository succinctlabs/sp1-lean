module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas
public import SP1Clean.Math.Word
public import SP1Clean.Circuits.Types.RegisterAccess

/-! # Native ALUTypeReader columns

These circuit value types are owned by the native library. The transitional Rust
extractor checks their field order and shapes before reusing them in its oracles.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `ALUTypeReader`. -/
structure ALUTypeReader (F : Type) where
  /-- Destination register index. -/
  op_a : F
  /-- Previous destination value and access timestamp. -/
  op_a_memory : (RegisterAccessCols F)
  /-- Selector for a destination of register x0. -/
  op_a_0 : F
  /-- First source register index. -/
  op_b : F
  /-- First source value and access timestamp. -/
  op_b_memory : (RegisterAccessCols F)
  /-- Second operand encoding: immediate word or register index. -/
  op_c : (Word F)
  /-- Second source value and access timestamp. -/
  op_c_memory : (RegisterAccessCols F)
  /-- Selector for an immediate second source operand. -/
  imm_c : F
deriving ProvableStruct
provable_struct_eval_lemmas ALUTypeReader

-- Preserve Rust field spelling for independent layout checks while reverse extraction remains.
attribute [nolint defsWithUnderscore]
  ALUTypeReader.op_a
  ALUTypeReader.op_a_memory
  ALUTypeReader.op_a_0
  ALUTypeReader.op_b
  ALUTypeReader.op_b_memory
  ALUTypeReader.op_c
  ALUTypeReader.op_c_memory
  ALUTypeReader.imm_c

end SP1Clean.Circuits.Types
