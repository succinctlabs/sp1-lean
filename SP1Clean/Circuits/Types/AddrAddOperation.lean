module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas

/-! # Native AddrAddOperation columns

These circuit value types are owned by the native library. The transitional Rust
extractor checks their field order and shapes before reusing them in its oracles.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `AddrAddOperation`. -/
structure AddrAddOperation (F : Type) where
  /-- Low 48 bits of the effective address, in three 16-bit limbs. -/
  value : (Vector F 3)
deriving ProvableStruct
provable_struct_eval_lemmas AddrAddOperation

end SP1Clean.Circuits.Types
