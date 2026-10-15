module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas

/-! # Native IsZeroOperation columns

These circuit value types are owned by the native library. The transitional Rust
extractor checks their field order and shapes before reusing them in its oracles.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `IsZeroOperation`. -/
structure IsZeroOperation (F : Type) where
  /-- Inverse of the tested field value when it is nonzero. -/
  inverse : F
  /-- Boolean result of the zero test. -/
  result : F
deriving ProvableStruct
provable_struct_eval_lemmas IsZeroOperation

end SP1Clean.Circuits.Types
