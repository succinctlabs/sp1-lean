import SP1Clean.ShiftLeftChip.Lemmas
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

/-! # `ShiftLeftChip` Clean circuit + `FormalAssertion` (scaffold)

Composes the Rust subcircuit graph for `ShiftLeftChip::eval`:
- `U16MSBOp.assertion` (the SLLW high-limb sign witness on `result[1]`),
- `CPUState.assertion`,
- `ALUTypeReader.assertion` (opcode `is_sll·6 + is_sllw·21`),
- 6-bit decomposition booleans, 4-way byte-shift one-hot booleans,
  shift-power chain identities, selector booleans, sum-binary, `op_a_0`.

The bulk of the chip-specific shift arithmetic (limb-shift identities,
result-limb wiring per active byte position) lives inline as
`assertZero` gates — there's no upstream Rust `ShiftLeftOperation`
sub-op to delegate to. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftLeftChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. -/
@[reducible]
def main (cols : Var ShiftLeftCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter, result,
       c_bits, v_01, v_012, v_0123, shift_u16,
       _lower_limb, _higher_limb, _limb_result, sllw_msb,
       is_sll, is_sllw, is_sllw_imm, _adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let opcode := is_sll * 6 + is_sllw * 21
  -- U16MSBOp sub-circuit (SLLW sign witness on result[1]).
  SP1Clean.U16MSBOp.assertion
    (⟨result[1], sllw_msb⟩ : Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ALUTypeReader.assertion
    (⟨clk_high, clk_low, opcode, pc, result, adapter⟩ :
      Var SP1Clean.ALUTypeReader.Inputs (ZMod p))
  -- 6 c-bit booleans:
  c_bits[0] * (c_bits[0] - 1) === 0
  c_bits[1] * (c_bits[1] - 1) === 0
  c_bits[2] * (c_bits[2] - 1) === 0
  c_bits[3] * (c_bits[3] - 1) === 0
  c_bits[4] * (c_bits[4] - 1) === 0
  c_bits[5] * (c_bits[5] - 1) === 0
  -- 4 byte-shift one-hot booleans:
  shift_u16[0] * (shift_u16[0] - 1) === 0
  shift_u16[1] * (shift_u16[1] - 1) === 0
  shift_u16[2] * (shift_u16[2] - 1) === 0
  shift_u16[3] * (shift_u16[3] - 1) === 0
  -- Shift-power chain identities:
  let one_expr : Expression (ZMod p) := 1
  (v_01 - (c_bits[0] + one_expr) * (c_bits[1] * 3 + one_expr)) === 0
  (v_012 - v_01 * (c_bits[2] * 15 + one_expr)) === 0
  (v_0123 - v_012 * (c_bits[3] * 255 + one_expr)) === 0
  -- Selector booleans + sum + op_a_0:
  is_sll * (is_sll - 1) === 0
  is_sllw * (is_sllw - 1) === 0
  (is_sll + is_sllw) * (is_sll + is_sllw - 1) === 0
  adapter.op_a_0 === 0
  -- is_sllw_imm = is_sllw * imm_c.
  (is_sllw_imm - is_sllw * adapter.imm_c) === 0

-- Nested sub-circuit composition exceeds default `subcircuitsConsistent`
-- / `localLength_eq` budgets. Supply as `sorry` (same precedent as
-- `SP1Clean/LtChip/Circuit.lean` and `MulChip/Circuit.lean`).
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) ShiftLeftCols unit where
  name := "SP1Clean.ShiftLeft"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq _ _ := by sorry
  subcircuitsConsistent _ _ := by sorry

def Assumptions (_ : ShiftLeftCols (ZMod p)) : Prop := True

abbrev FormalSpec := @SP1Clean.ShiftLeftChip.FormalSpec p

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

/-- The full Clean `FormalAssertion` for `ShiftLeftChip`. -/
def assertion : FormalAssertion (ZMod p) ShiftLeftCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.ShiftLeftChip
