module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas
public import SP1Clean.Circuits.Types.U16CompareOperation

/-! # Native LtOperationUnsigned columns

These circuit value types are owned by the native library. The transitional Rust
extractor checks their field order and shapes before reusing them in its oracles.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `LtOperationUnsigned`. -/
structure LtOperationUnsigned (F : Type) where
  /-- Comparison result for the selected 16-bit limb pair. -/
  u16_compare_operation : (U16CompareOperation F)
  /-- Selectors for the most significant differing limb pair. -/
  u16_flags : (Vector F 4)
  /-- Inverse witness for the selected limb difference. -/
  not_eq_inv : F
  /-- Selected left and right operand limbs. -/
  comparison_limbs : (Vector F 2)
deriving ProvableStruct
provable_struct_eval_lemmas LtOperationUnsigned

-- Preserve Rust field spelling for independent layout checks while reverse extraction remains.
attribute [nolint defsWithUnderscore]
  LtOperationUnsigned.u16_compare_operation
  LtOperationUnsigned.u16_flags
  LtOperationUnsigned.not_eq_inv
  LtOperationUnsigned.comparison_limbs

end SP1Clean.Circuits.Types
