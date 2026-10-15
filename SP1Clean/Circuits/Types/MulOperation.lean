module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas
public import SP1Clean.Circuits.Types.U16MSBOperation
public import SP1Clean.Circuits.Types.U16toU8Operation

/-! # Native MulOperation columns

These circuit value types are owned by the native library. The transitional Rust
extractor checks their field order and shapes before reusing them in its oracles.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `MulOperation`. -/
structure MulOperation (F : Type) where
  /-- Sixteen carry witnesses for bytewise product accumulation. -/
  carry : (Vector F 16)
  /-- Sixteen product bytes after carry propagation. -/
  product : (Vector F 16)
  /-- Low bytes of the four 16-bit limbs of the first operand. -/
  b_lower_byte : (U16toU8Operation F)
  /-- Low bytes of the four 16-bit limbs of the second operand. -/
  c_lower_byte : (U16toU8Operation F)
  /-- Most significant bit of the first operand. -/
  b_msb : F
  /-- Most significant bit of the second operand. -/
  c_msb : F
  /-- Most significant bit of the selected product limb. -/
  product_msb : (U16MSBOperation F)
  /-- Sign-extension selector for the first operand. -/
  b_sign_extend : F
  /-- Sign-extension selector for the second operand. -/
  c_sign_extend : F
deriving ProvableStruct
provable_struct_eval_lemmas MulOperation

-- Preserve Rust field spelling for independent layout checks while reverse extraction remains.
attribute [nolint defsWithUnderscore]
  MulOperation.b_lower_byte
  MulOperation.c_lower_byte
  MulOperation.b_msb
  MulOperation.c_msb
  MulOperation.product_msb
  MulOperation.b_sign_extend
  MulOperation.c_sign_extend

end SP1Clean.Circuits.Types
