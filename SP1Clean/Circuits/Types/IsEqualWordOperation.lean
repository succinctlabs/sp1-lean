module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas
public import SP1Clean.Circuits.Types.IsZeroWordOperation

/-! # Native IsEqualWordOperation columns

These circuit value types are owned by the native library. The transitional Rust
extractor checks their field order and shapes before reusing them in its oracles.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `IsEqualWordOperation`. -/
structure IsEqualWordOperation (F : Type) where
  /-- Zero tests for the four limb differences. -/
  is_diff_zero : (IsZeroWordOperation F)
deriving ProvableStruct
provable_struct_eval_lemmas IsEqualWordOperation

-- Preserve Rust field spelling for independent layout checks while reverse extraction remains.
attribute [nolint defsWithUnderscore]
  IsEqualWordOperation.is_diff_zero

end SP1Clean.Circuits.Types
