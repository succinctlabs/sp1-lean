module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas
public import SP1Clean.Math.Word
public import SP1Clean.Circuits.Types.RegisterAccess

/-! # Native JTypeReader columns

These circuit value types are owned by the native library. The transitional Rust
extractor checks their field order and shapes before reusing them in its oracles.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `JTypeReader`. -/
structure JTypeReader (F : Type) where
  /-- Destination register index. -/
  op_a : F
  /-- Previous destination value and access timestamp. -/
  op_a_memory : (RegisterAccessCols F)
  /-- Selector for a destination of register x0. -/
  op_a_0 : F
  /-- First immediate operand in four little-endian 16-bit limbs. -/
  op_b_imm : (Word F)
  /-- Second immediate operand in four little-endian 16-bit limbs. -/
  op_c_imm : (Word F)
deriving ProvableStruct
provable_struct_eval_lemmas JTypeReader

-- Preserve Rust field spelling for independent layout checks while reverse extraction remains.
attribute [nolint defsWithUnderscore]
  JTypeReader.op_a
  JTypeReader.op_a_memory
  JTypeReader.op_a_0
  JTypeReader.op_b_imm
  JTypeReader.op_c_imm

end SP1Clean.Circuits.Types
