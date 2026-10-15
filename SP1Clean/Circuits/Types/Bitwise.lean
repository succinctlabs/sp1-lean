module

public import SP1Clean.Circuits.Types.U16toU8Operation

/-! # Native bitwise gadget columns

Byte-result columns and their word-level operand decompositions share the same physical layout
across contracts, circuits and transitional Rust faithfulness.
-/

@[expose] public section

namespace SP1Clean.BitwiseOperation

/-- Proof-oriented local columns for the bytewise bitwise gadget: the eight witnessed result bytes.
The assembled chip faithfulness map is the only place that relates this shape to SP1 Rust's
helper-operation columns. -/
structure Columns (F : Type) where
  /-- Eight little-endian result bytes. -/
  result : Vector F 8
deriving ProvableStruct
provable_struct_eval_lemmas Columns

end SP1Clean.BitwiseOperation

namespace SP1Clean.BitwiseU16Operation

/-- Proof-oriented local columns for the composed u16 bitwise gadget: the two low-byte decomposition
blocks (the shared `Circuits.Types.U16toU8Operation` struct, kept because the decomposition is the shared
native column type) plus the native `BitwiseOperation.Columns` result block. The assembled chip
faithfulness map is the only place that relates this shape to SP1 Rust's helper-operation columns. -/
structure Columns (F : Type) where
  /-- Low bytes of the first operand's four limbs. -/
  b_low_bytes : Circuits.Types.U16toU8Operation F
  /-- Low bytes of the second operand's four limbs. -/
  c_low_bytes : Circuits.Types.U16toU8Operation F
  /-- Eight result bytes supplied to the bytewise assertion. -/
  bitwise_operation : BitwiseOperation.Columns F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

end SP1Clean.BitwiseU16Operation
