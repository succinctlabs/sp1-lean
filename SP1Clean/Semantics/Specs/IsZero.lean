module

public import SP1Clean.Circuits.Types.IsZeroOperation

/-! # Field zero-test contract

On an active row, the result indicates whether the input is zero. For a nonzero input the
inverse column is its multiplicative inverse. Padding imposes no condition on those columns.
This contract contains no circuit implementation or generated Rust oracle.
-/

@[expose] public section

namespace SP1Clean.IsZeroOperation

/-- Inputs for the native field-zero test. -/
structure Inputs (F : Type) where
  /-- The value being tested. -/
  a : F
  /-- The inverse and zero-indicator columns. -/
  cols : Circuits.Types.IsZeroOperation F
  /-- One for an active row, zero for padding. -/
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

variable {p : ℕ} [Fact p.Prime]

/-- The activity flag is binary; the operand can be any field element. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

/-- On an active row, the result indicates whether the input is zero. Nonzero inputs require a
multiplicative inverse; the inverse of zero and all padding columns are unrestricted. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 1 →
    (input.cols.result = if input.a = 0 then 1 else 0) ∧
    (input.a ≠ 0 → input.cols.inverse * input.a = 1)

end SP1Clean.IsZeroOperation
