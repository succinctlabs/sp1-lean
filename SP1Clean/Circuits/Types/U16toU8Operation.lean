module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas

/-! # Native U16toU8Operation columns

These circuit value types are owned by the native library. The transitional Rust
extractor checks their field order and shapes before reusing them in its oracles.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `U16toU8Operation`. -/
structure U16toU8Operation (F : Type) where
  /-- Low byte of each of the four input 16-bit limbs. -/
  low_bytes : (Vector F 4)
deriving ProvableStruct
provable_struct_eval_lemmas U16toU8Operation

-- Preserve Rust field spelling for independent layout checks while reverse extraction remains.
attribute [nolint defsWithUnderscore]
  U16toU8Operation.low_bytes

end SP1Clean.Circuits.Types
