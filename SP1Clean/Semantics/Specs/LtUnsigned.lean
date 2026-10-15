module

public import SP1Clean.Math.Word
public import SP1Clean.Circuits.Types.LtOperationUnsigned
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Unsigned word comparison contract

Active rows select the most significant differing limb, or select nothing when the words
are equal. Inactive rows may select a limb only when it and all lower limbs agree; the
inverse and binary result bit are then unconstrained. This is a value-level description
of the accepted certificates, independent of the AIR equations and witness generator.
-/

@[expose] public section

namespace SP1Clean.LtOperationUnsigned

/-- Inputs for the native unsigned word comparison gadget. -/
structure Inputs (F : Type) where
  /-- Left operand, in little-endian 16-bit limbs. -/
  b : Word F
  /-- Right operand. -/
  cc : Word F
  /-- Committed comparison certificate. -/
  cols : Circuits.Types.LtOperationUnsigned F
  /-- One for an active row, zero for padding. -/
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

variable {p : ℕ} [Fact p.Prime]

/-- On a real row (`is_real = 1`) the operands are genuine 64-bit values, and `is_real` is binary. The
`isU64` precondition is **gated on `is_real`**: a padding row owes nothing, so a chip feeding *witnessed*
operands whose range checks are themselves `is_real`-gated (e.g. DivRem's `abs_remainder`/`max_abs_c_or_1`)
can still discharge this assumption. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 1 → Word.isU64 input.b ∧ Word.isU64 input.cc) ∧ (input.is_real = 0 ∨ input.is_real = 1)

/-- Select one limb: the highest differing limb on an active row, or the end of an equal
lower prefix on padding. The inverse certifies the active difference. -/
def Pivot (input : Inputs (ZMod p)) (i : Fin 4) : Prop :=
  input.cols.u16_flags = Vector.ofFn (fun j => if j = i then 1 else 0) ∧
  input.cols.comparison_limbs = #v[input.b[i], input.cc[i]] ∧
  (input.is_real = 1 →
    (∀ j : Fin 4, i < j → input.b[j] = input.cc[j]) ∧
    input.b[i] ≠ input.cc[i] ∧
    input.cols.not_eq_inv = (input.b[i] - input.cc[i])⁻¹) ∧
  (input.is_real = 0 → ∀ j : Fin 4, j ≤ i → input.b[j] = input.cc[j])

/-- Either no limb is selected, or exactly one limb is selected. -/
def Selection (input : Inputs (ZMod p)) : Prop :=
  (input.cols.u16_flags = #v[0, 0, 0, 0] ∧
    input.cols.comparison_limbs = #v[0, 0] ∧
    (input.is_real = 1 → input.b = input.cc)) ∨ ∃ i, Pivot input i

/-- The selected limb certificate and the unsigned whole-word comparison agree. Result bits
are binary even on padding. The certificate describes every auxiliary column, including the
permitted inactive-row selections, so the assertion remains complete for arbitrary accepted rows. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.cols.u16_compare_operation.bit = 0 ∨ input.cols.u16_compare_operation.bit = 1) ∧
  Selection input ∧
  (input.is_real = 1 →
    (input.cols.u16_compare_operation.bit =
      if Word.toNat input.b < Word.toNat input.cc then 1 else 0) ∧
    ((input.cols.u16_flags[0] + input.cols.u16_flags[1] + input.cols.u16_flags[2]
      + input.cols.u16_flags[3] = 0) ↔ Word.toNat input.b = Word.toNat input.cc))

/-- Active rows expose the whole-word ordering and equality directly. -/
theorem result_semantic {input : Inputs (ZMod p)} (hs : Spec input)
    (hir : input.is_real = 1) :
    (input.cols.u16_compare_operation.bit =
      if Word.toNat input.b < Word.toNat input.cc then 1 else 0) ∧
    ((input.cols.u16_flags[0] + input.cols.u16_flags[1] + input.cols.u16_flags[2]
      + input.cols.u16_flags[3] = 0) ↔ Word.toNat input.b = Word.toNat input.cc) := hs.2.2 hir

/-- A valid certificate selects zero or one limb, including on padding. -/
theorem flags_sum_binary {input : Inputs (ZMod p)} (hs : Spec input) :
    input.cols.u16_flags[0] + input.cols.u16_flags[1] + input.cols.u16_flags[2]
      + input.cols.u16_flags[3] = 0 ∨
    input.cols.u16_flags[0] + input.cols.u16_flags[1] + input.cols.u16_flags[2]
      + input.cols.u16_flags[3] = 1 := by
  rcases hs.2.1 with ⟨hf, _, _⟩ | ⟨i, hf, _, _, _⟩
  · simp [hf]
  · fin_cases i <;> simp [hf]

end SP1Clean.LtOperationUnsigned
