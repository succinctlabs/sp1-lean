module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas
public import SP1Clean.Math.Word
public import SP1Clean.Circuits.Types.RegisterAccess

/-! # Native ITypeReader columns

These circuit value types are owned by the native library. The transitional Rust
extractor checks their field order and shapes before reusing them in its oracles.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `ITypeReader`. -/
structure ITypeReader (F : Type) where
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
  /-- Second immediate operand in four little-endian 16-bit limbs. -/
  op_c_imm : (Word F)
deriving ProvableStruct
provable_struct_eval_lemmas ITypeReader

-- Preserve Rust field spelling for independent layout checks while reverse extraction remains.
attribute [nolint defsWithUnderscore]
  ITypeReader.op_a
  ITypeReader.op_a_memory
  ITypeReader.op_a_0
  ITypeReader.op_b
  ITypeReader.op_b_memory
  ITypeReader.op_c_imm

end SP1Clean.Circuits.Types
