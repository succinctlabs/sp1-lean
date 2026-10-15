module

public import SP1Clean.Circuits.Types.U16MSBOperation

/-! # 16-bit high-bit contract

The public input and semantic relation are independent of the circuit and its range lookup.
Result bits are binary even on padding; operand range assumptions apply only to active rows.
-/

@[expose] public section

namespace SP1Clean.U16MSBOperation

variable {p : ℕ} [Fact p.Prime]

/-- Proof-oriented inputs for the native MSB gadget. The native library owns both the
column type and this semantic interface; Rust layout agreement is checked separately. -/
structure Inputs (F : Type) where
  /-- The input limb. -/
  a : F
  /-- The committed result column. -/
  cols : Circuits.Types.U16MSBOperation F
  /-- One for an active row, zero for padding. -/
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The result is binary on every row. Active rows report the high bit of the input limb;
padding leaves its value unconstrained apart from binariness. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.cols.msb = 0 ∨ input.cols.msb = 1) ∧
  (input.is_real = 1 → input.cols.msb = if input.a.val ≥ 32768 then 1 else 0)

/-- `a` is a genuine 16-bit value on a real row (gated), and `is_real` is binary (the latter
discharged by the composing operation's gate). `msb`'s booleanness is carried by the `Spec`, not here,
since SP1's `eval_msb` asserts it ungated (so it must hold on padding too, where the `Spec`'s high-bit
equation is vacuous). -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 1 → input.a.val < 2 ^ 16) ∧ (input.is_real = 0 ∨ input.is_real = 1)

end SP1Clean.U16MSBOperation
