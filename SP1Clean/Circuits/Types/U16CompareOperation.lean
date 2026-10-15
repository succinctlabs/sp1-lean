module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas

/-! # Native U16CompareOperation columns

These circuit value types are owned by the native library. The transitional Rust
extractor checks their field order and shapes before reusing them in its oracles.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `U16CompareOperation`. -/
structure U16CompareOperation (F : Type) where
  /-- Unsigned less-than result for the input limb pair. -/
  bit : F
deriving ProvableStruct
provable_struct_eval_lemmas U16CompareOperation

end SP1Clean.Circuits.Types
