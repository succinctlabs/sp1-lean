import SP1Clean.LtChip.Lemmas
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
import SP1Clean.Operations.LtOperationSigned
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `LtChip` Clean circuit + `FormalAssertion` (directory-form scaffold)

Composes the Rust subcircuit graph for `LtChip::eval`:
- `LtSignedOp.assertion` (the comparison arithmetic — itself wrapping
  `U16MSBOp.assertion` ×2 + `LtUnsignedOp.assertion`),
- `CPUState.assertion`,
- `ALUTypeReader.assertion` (program + memory + imm_c switch),
- 4 trailing scalar gates (2 selector binaries + sum binary + op_a_0).

`is_real = is_slt + is_sltu`. The `is_signed` toggle for the
`LtSignedOp` sub-call is `cols.is_slt` (only the signed SLT/SLTI
variants need the sign-flip — SLTU/SLTIU use is_signed=0).

Soundness/completeness bodies are `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LtChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. -/
@[reducible]
def main (cols : Var LtCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter,
       compare_bit, u16_flags, not_eq_inv, comparison_limbs,
       b_msb, c_msb, is_slt, is_sltu, _adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let op_a_write_value : Vector (Expression (ZMod p)) 4 := #v[compare_bit, 0, 0, 0]
  SP1Clean.LtSignedOp.assertion
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
       is_slt,
       compare_bit, u16_flags, not_eq_inv, comparison_limbs,
       b_msb, c_msb⟩ : Var SP1Clean.LtSignedOp.Inputs (ZMod p))
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ALUTypeReader.assertion
    (⟨clk_high, clk_low, is_slt * 9 + is_sltu * 10, pc, op_a_write_value, adapter⟩ :
      Var SP1Clean.ALUTypeReader.Inputs (ZMod p))
  is_slt * (is_slt - 1) === 0
  is_sltu * (is_sltu - 1) === 0
  (is_slt + is_sltu) * (is_slt + is_sltu - 1) === 0
  adapter.op_a_0 === 0

-- 3 subcircuits (one recursively composing 3 more — LtSignedOp) + 4
-- scalar gates. The default `subcircuitsConsistent` derivation
-- exponentially times out on this nesting depth; supply it as `sorry`
-- for the scaffold (along with the other proof bodies).
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) LtCols unit where
  name := "SP1Clean.Lt"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq _ _ := by sorry
  subcircuitsConsistent _ _ := by sorry

def Assumptions (_ : LtCols (ZMod p)) : Prop := True

/-- The unified chip Spec is defined in `Cols.lean`
(`SP1Clean.LtChip.FormalSpec`). -/
abbrev FormalSpec := @SP1Clean.LtChip.FormalSpec p

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

/-- The full Clean `FormalAssertion` for `LtChip`. -/
def assertion : FormalAssertion (ZMod p) LtCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.LtChip
