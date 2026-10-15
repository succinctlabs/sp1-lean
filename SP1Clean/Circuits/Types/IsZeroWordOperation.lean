module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas
public import SP1Clean.Circuits.Types.IsZeroOperation

/-! # Native IsZeroWordOperation columns

These circuit value types are owned by the native library. The transitional Rust
extractor checks their field order and shapes before reusing them in its oracles.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `IsZeroWordOperation`. -/
structure IsZeroWordOperation (F : Type) where
  /-- Zero test for limb 0. -/
  is_zero_limb_0 : (IsZeroOperation F)
  /-- Zero test for limb 1. -/
  is_zero_limb_1 : (IsZeroOperation F)
  /-- Zero test for limb 2. -/
  is_zero_limb_2 : (IsZeroOperation F)
  /-- Zero test for limb 3. -/
  is_zero_limb_3 : (IsZeroOperation F)
  /-- Conjunction of the low two limb zero-test results. -/
  is_zero_first_half : F
  /-- Conjunction of the high two limb zero-test results. -/
  is_zero_second_half : F
  /-- Boolean result of the zero test. -/
  result : F
deriving ProvableStruct
provable_struct_eval_lemmas IsZeroWordOperation

-- Preserve Rust field spelling for independent layout checks while reverse extraction remains.
attribute [nolint defsWithUnderscore]
  IsZeroWordOperation.is_zero_limb_0
  IsZeroWordOperation.is_zero_limb_1
  IsZeroWordOperation.is_zero_limb_2
  IsZeroWordOperation.is_zero_limb_3
  IsZeroWordOperation.is_zero_first_half
  IsZeroWordOperation.is_zero_second_half

end SP1Clean.Circuits.Types
