module

public import SP1Clean.Circuits.Types.LtChip
public import SP1Clean.FormalModel.Contracts.Readers
public import SP1Clean.Semantics.ISA.RV64

/-! # Less-than instruction semantics

The public contract combines the ALU reader obligations with signed or unsigned RV64
comparison. Activity is the selector sum. Comparison witnesses and circuit proofs remain
outside this semantic boundary.
-/

@[expose] public section

namespace SP1Clean.LtChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The comparison bit in the low limb, with zero upper limbs. -/
def resultWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0]

/-- Reader obligations, binary activity, and the selected signed or unsigned RV64 result. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.ALUTypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc, opcode := cols.is_slt * 9 + cols.is_sltu * 10,
      wv0 := (resultWord cols)[0], wv1 := (resultWord cols)[1],
      wv2 := (resultWord cols)[2], wv3 := (resultWord cols)[3] } ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    (cols.is_slt = 1 →
      Word.toBitVec64 (resultWord cols)
        = RV64.slt (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_sltu = 1 →
      Word.toBitVec64 (resultWord cols)
        = RV64.sltu (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)))

end SP1Clean.LtChip
