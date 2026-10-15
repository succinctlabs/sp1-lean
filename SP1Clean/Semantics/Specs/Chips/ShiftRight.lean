module

public import SP1Clean.Circuits.Types.ShiftRightChip
public import SP1Clean.Semantics.ISA.RV64

/-! # Shift-right instruction semantics

On active rows, the selected SRL, SRA, SRLW, or SRAW variant computes the RV64 result.
Reader, clock, and binary-selector obligations belong to the circuit contracts.
-/

@[expose] public section

namespace SP1Clean.ShiftRightChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The selected RV64 shift-right result; padding has no result obligation. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  let rs1 := input.adapter.op_b_memory.prev_value
  let rs2 := input.adapter.op_c_memory.prev_value
  input.is_real = 1 →
    (cols.is_srl = 1 →
      Word.toBitVec64 cols.a = RV64.srl (Word.toBitVec64 rs2) (Word.toBitVec64 rs1)) ∧
    (cols.is_sra = 1 →
      Word.toBitVec64 cols.a = RV64.sra (Word.toBitVec64 rs2) (Word.toBitVec64 rs1)) ∧
    (cols.is_srlw = 1 →
      Word.toBitVec64 cols.a = RV64.srlw (Word.toBitVec64 rs2) (Word.toBitVec64 rs1)) ∧
    (cols.is_sraw = 1 →
      Word.toBitVec64 cols.a = RV64.sraw (Word.toBitVec64 rs2) (Word.toBitVec64 rs1))

end SP1Clean.ShiftRightChip
