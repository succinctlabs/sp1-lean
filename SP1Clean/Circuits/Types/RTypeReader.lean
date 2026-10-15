module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas
public import SP1Clean.Circuits.Types.RegisterAccess

/-! # Native RTypeReader columns

These circuit value types are owned by the native library. The transitional Rust
extractor checks their field order and shapes before reusing them in its oracles.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `RTypeReader`. -/
structure RTypeReader (F : Type) where
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
  /-- Second source register index. -/
  op_c : F
  /-- Second source value and access timestamp. -/
  op_c_memory : (RegisterAccessCols F)
deriving ProvableStruct
provable_struct_eval_lemmas RTypeReader

-- Preserve Rust field spelling for independent layout checks while reverse extraction remains.
attribute [nolint defsWithUnderscore]
  RTypeReader.op_a
  RTypeReader.op_a_memory
  RTypeReader.op_a_0
  RTypeReader.op_b
  RTypeReader.op_b_memory
  RTypeReader.op_c
  RTypeReader.op_c_memory

end SP1Clean.Circuits.Types
