module

public import SP1Clean.Circuits.Types.U16CompareOperation

/-! # 16-bit comparison contract

The public input and semantic relation are independent of the circuit and its range lookup.
Result bits are binary even on padding; operand range assumptions apply only to active rows.
-/

@[expose] public section

namespace SP1Clean.U16CompareOperation

variable {p : ℕ} [Fact p.Prime]

/-- Proof-oriented inputs for the native 16-bit comparison gadget. -/
structure Inputs (F : Type) where
  /-- The input limb. -/
  a : F
  /-- The limb compared with the input. -/
  b : F
  /-- The committed result column. -/
  cols : Circuits.Types.U16CompareOperation F
  /-- One for an active row, zero for padding. -/
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The result is binary on every row. Active rows report the strict less-than comparison of the two limbs;
padding leaves its value unconstrained apart from binariness. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.cols.bit = 0 ∨ input.cols.bit = 1) ∧
  (input.is_real = 1 → input.cols.bit = if input.a.val < input.b.val then 1 else 0)

/-- `a`, `b` are genuine 16-bit values on a real row (gated), and `is_real` is binary (the latter
discharged by the composing operation's gate). `bit`'s booleanness is carried by the `Spec`, not here, since SP1's
`eval` asserts it ungated (so it must hold on padding too, where the `Spec`'s order equation is vacuous). -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 1 → input.a.val < 2 ^ 16 ∧ input.b.val < 2 ^ 16) ∧
  (input.is_real = 0 ∨ input.is_real = 1)

end SP1Clean.U16CompareOperation
