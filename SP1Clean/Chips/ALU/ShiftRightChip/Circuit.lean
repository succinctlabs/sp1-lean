import SP1Clean.Chips.ALU.ShiftRightChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `ShiftRightChip` Clean circuit + `FormalAssertion`

Path-2 main lifted from `Aggregate.lean`. Soundness/completeness
sorry'd. 4-variant: `srl`/`sra`/`srlw`/`sraw`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftRight

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var ShiftRightCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c⟩,
       _op_a_write_value,
       _b_msb, _srw_msb, _c_bits, _sra_msb_v0123, _v_0123, _v_012, _v_01,
       _lower_limb, _higher_limb, _limb_result, _shift_u16,
       is_srl, is_sra, is_srlw, is_sraw, _is_w_imm, _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  let opcode_e := is_srl * 7 + is_sra * 8 + is_srlw * 22 + is_sraw * 23
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode_e, op_a, #v[op_b, 0, 0, 0], op_c, op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_srl * (is_srl - 1) === 0
  is_sra * (is_sra - 1) === 0
  is_srlw * (is_srlw - 1) === 0
  is_sraw * (is_sraw - 1) === 0
  let sum := is_srl + is_sra + is_srlw + is_sraw
  sum * (sum - 1) === 0
  op_a_0 === 0
  let clk_low := clk_0_16 + clk_16_24 * 65536
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low,
       op_a_memory.access_timestamp.diff_low_limb, op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 3, op_b_memory.access_timestamp.prev_low,
       op_b_memory.access_timestamp.diff_low_limb, op_b_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 2, op_c_memory.access_timestamp.prev_low,
       op_c_memory.access_timestamp.diff_low_limb, op_c_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))

set_option maxHeartbeats 800000 in
-- 26 input fields + 4 subcircuit calls + 3 OperandAccess calls push
-- localLength_eq synthesis past the default 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) ShiftRightCols unit where
  name := "SP1Clean.ShiftRight"
  main := main
  localLength _ := 0

def Assumptions (cols : ShiftRightCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted =
    cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw ∧
  cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 1

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

def assertion : FormalAssertion (ZMod p) ShiftRightCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.ShiftRight
