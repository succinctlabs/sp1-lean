module

public import SP1Clean.Circuits.Types.ShiftLeftChip
public import SP1Clean.Semantics.ISA.RV64

/-! # Shift-left instruction semantics

On active rows, the selected SLL or SLLW variant computes the RV64 result. Reader,
clock, and binary-selector obligations are enforced by the circuit and used by its
trace-level contracts; they are not restated in this result specification.
-/

@[expose] public section

namespace SP1Clean.ShiftLeftChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The selected RV64 shift-left result; padding has no result obligation. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  input.is_real = 1 →
    (cols.is_sll = 1 →
      Word.toBitVec64 cols.a = RV64.sll (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_sllw = 1 →
      Word.toBitVec64 cols.a = RV64.sllw (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))

end SP1Clean.ShiftLeftChip
