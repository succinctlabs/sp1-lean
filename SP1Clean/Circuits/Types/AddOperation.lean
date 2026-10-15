module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas
public import SP1Clean.Math.Word

/-! # Native AddOperation columns

These circuit value types are owned by the native library. The transitional Rust
extractor checks their field order and shapes before reusing them in its oracles.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `AddOperation`. -/
structure AddOperation (F : Type) where
  /-- Low 64 bits of the sum, in four 16-bit limbs. -/
  value : (Word F)
deriving ProvableStruct
provable_struct_eval_lemmas AddOperation

end SP1Clean.Circuits.Types
