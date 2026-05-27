import SP1Clean.Chips.ALU.MulChip.Lemmas
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

/-! # `MulChip` Clean circuit + `FormalAssertion`

Canonical (a)-shape main composing `CPUState.Gated` +
`RTypeReader.Gated` + `MulOp.assertion` + scalar gates. Soundness /
completeness sorry'd. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Mul

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

variable [Fact (2 ^ 24 < p)]

@[reducible]
def main (cols : Var MulCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       adapter, op_a_write_value, mul_op,
       is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw, adapter_cols⟩ := cols
  let is_real_e := is_mul + is_mulh + is_mulw + is_mulhsu + is_mulhu
  let opcode_e  := is_mul * 11 + is_mulh * 12 + is_mulw * 13
                    + is_mulhsu * 14 + is_mulhu * 24
  let clk_low   := clk_0_16 + clk_16_24 * 65536
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       #v[pc[0] + 4, pc[1], pc[2]], 8, is_real_e⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.RTypeReader.Gated.assertion
    (⟨clk_high, clk_low, opcode_e, pc, op_a_write_value, adapter,
       is_real_e, adapter_cols.is_trusted⟩ :
      Var SP1Clean.RTypeReader.Gated.Inputs (ZMod p))
  SP1Clean.MulOp.assertion
    (⟨op_a_write_value,
       adapter.op_b_memory.prev_value,
       adapter.op_c_memory.prev_value,
       mul_op.carry, mul_op.product,
       mul_op.b_lower_byte.low_bytes, mul_op.c_lower_byte.low_bytes,
       mul_op.b_msb, mul_op.c_msb, mul_op.product_msb.msb,
       mul_op.b_sign_extend, mul_op.c_sign_extend,
       is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw⟩ :
      Var SP1Clean.MulOp.Inputs (ZMod p))
  is_mul    * (is_mul    - 1) === 0
  is_mulh   * (is_mulh   - 1) === 0
  is_mulhu  * (is_mulhu  - 1) === 0
  is_mulhsu * (is_mulhsu - 1) === 0
  is_mulw   * (is_mulw   - 1) === 0
  is_real_e * (is_real_e - 1) === 0
  adapter.op_a_0 === 0

set_option maxHeartbeats 6400000 in
-- 6.4M heartbeats: `localLength_eq` synthesizes against a 4-subcircuit
-- main (CPUState.Gated + RTypeReader.Gated + MulOp + scalar gates)
-- where MulOp itself wraps 3 sub-circuits + 68 inline gates.
-- `subcircuitsConsistent` sorry'd in same spirit as legacy aggregate.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) MulCols unit where
  name := "SP1Clean.Mul"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent _ _ := by sorry

def Assumptions (_ : MulCols (ZMod p)) : Prop := True

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

def assertion [Fact (2 ^ 24 < p)] : FormalAssertion (ZMod p) MulCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Mul
