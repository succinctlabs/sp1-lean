import SP1Clean.Chips.ALU.ShiftRightChip.Multiplicity.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Operations.U16MSBOperation
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `ShiftRightChip` Clean circuit + `FormalAssertion` (scaffold)

Composes the Rust subcircuit graph for `ShiftRightChip::eval`:
- `U16MSBOp.assertion` ×3 (b_high MSB for SRA, b_low MSB for SRAW,
  result_high MSB for SRLW/SRAW sign-extend),
- `CPUState.assertion`,
- `ALUTypeReader.assertion` (opcode 4-term sum),
- 4 selector booleans, 4-way sum-binary, `op_a_0`,
- 6-bit shift decomp booleans,
- `is_w_imm = (is_srlw + is_sraw) * imm_c` bridge,
- inline limb-shift arithmetic (omitted from this scaffold; only the
  bit booleans / sum gates / msb-related bridges appear). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftRightChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var ShiftRightCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter, result,
       b_msb, srw_msb, c_bits,
       _v_01, _v_012, _v_0123,
       _shifted_intermediates, _limb_result, _shift_u16,
       is_srl, is_sra, is_srlw, is_sraw, is_w_imm, _adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let opcode := is_srl * 7 + is_sra * 8 + is_srlw * 22 + is_sraw * 23
  -- 3 U16MSB sub-circuits (per Rust nesting in ShiftRight.constraints):
  SP1Clean.U16MSBOp.assertion
    (⟨adapter.op_b_memory.prev_value[3], b_msb⟩ : Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨adapter.op_b_memory.prev_value[1], b_msb⟩ : Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨result[1], srw_msb⟩ : Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ALUTypeReader.assertion
    (⟨clk_high, clk_low, opcode, pc, result, adapter⟩ :
      Var SP1Clean.ALUTypeReader.Inputs (ZMod p))
  -- 4 selector booleans:
  is_srl * (is_srl - 1) === 0
  is_sra * (is_sra - 1) === 0
  is_srlw * (is_srlw - 1) === 0
  is_sraw * (is_sraw - 1) === 0
  -- Sum-of-selectors is boolean (at most one variant active per row):
  let is_real := is_srl + is_sra + is_srlw + is_sraw
  is_real * (is_real - 1) === 0
  adapter.op_a_0 === 0
  -- 6 c-bit booleans:
  c_bits[0] * (c_bits[0] - 1) === 0
  c_bits[1] * (c_bits[1] - 1) === 0
  c_bits[2] * (c_bits[2] - 1) === 0
  c_bits[3] * (c_bits[3] - 1) === 0
  c_bits[4] * (c_bits[4] - 1) === 0
  c_bits[5] * (c_bits[5] - 1) === 0
  -- is_w_imm = (is_srlw + is_sraw) * imm_c.
  (is_w_imm - (is_srlw + is_sraw) * adapter.imm_c) === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) ShiftRightCols unit where
  name := "SP1Clean.ShiftRight"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq _ _ := by sorry
  subcircuitsConsistent _ _ := by sorry

def Assumptions (_ : ShiftRightCols (ZMod p)) : Prop := True

abbrev FormalSpec := @SP1Clean.ShiftRightChip.FormalSpec p

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

/-- The full Clean `FormalAssertion` for `ShiftRightChip`. -/
def assertion : FormalAssertion (ZMod p) ShiftRightCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.ShiftRightChip
