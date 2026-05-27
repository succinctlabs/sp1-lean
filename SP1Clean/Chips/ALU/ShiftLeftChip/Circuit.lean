import SP1Clean.Chips.ALU.ShiftLeftChip.Lemmas
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

/-! # `ShiftLeftChip` Clean circuit + `FormalAssertion`

Path-2 main lifted from `Aggregate.lean`. Soundness/completeness
sorry'd pending an operation-level bridge (Shift operation is
inline-only — no separate module). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftLeft

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var ShiftLeftCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c⟩,
       _result, _c_bits, _v_01, _v_012, _v_0123, _shift_u16, _lower_limb,
       _higher_limb, _limb_result, _sllw_msb, is_sll, is_sllw, _is_sllw_imm,
       _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_sll * 8 + is_sllw * 14,
      op_a, #v[op_b, 0, 0, 0], op_c, op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_sll * (is_sll - 1) === 0
  is_sllw * (is_sllw - 1) === 0
  (is_sll + is_sllw) * (is_sll + is_sllw - 1) === 0
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
-- 31 input fields + 4 subcircuit calls + 3 OperandAccess calls push
-- localLength_eq synthesis past the default 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) ShiftLeftCols unit where
  name := "SP1Clean.ShiftLeft"
  main := main
  localLength _ := 0

def Assumptions (cols : ShiftLeftCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_sll + cols.is_sllw ∧
  cols.is_sll + cols.is_sllw = 1

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

def assertion : FormalAssertion (ZMod p) ShiftLeftCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.ShiftLeft
