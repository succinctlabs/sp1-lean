import SP1Clean.MulChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.Reader.RTypeReader
import SP1Clean.Operations.MulOperation
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `MulChip` Clean circuit + `FormalAssertion` (directory-form scaffold)

Composes the Rust subcircuit graph for `MulChip::eval`:
- `MulOp.assertion` (the 16-byte product carry-chain + sign-extend
  discipline — itself wrapping `U16toU8OpSafe.assertion` ×2 +
  `U16MSBOp.assertion` ×1),
- `CPUState.assertion`,
- `RTypeReader.assertion`,
- 7 trailing scalar gates (5 selector binaries + sum binary + op_a_0).

Opcode formula `is_mul·11 + is_mulh·12 + is_mulhu·13 + is_mulhsu·14 + is_mulw·24`.
`is_real = is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw`.

The default `subcircuitsConsistent` derivation exponentially times out on
this nesting depth (`MulOp.assertion` recursively composes 3 sub-circuits);
supply it as `sorry` for the scaffold along with the other proof
bodies. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.MulChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. -/
@[reducible]
def main (cols : Var MulCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter,
       a_word, carry, product, b_low_bytes, c_low_bytes,
       b_msb, c_msb, product_msb, b_sign_extend, c_sign_extend,
       is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw, _adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let is_real := is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw
  let opcode := is_mul * 11 + is_mulh * 12 + is_mulhu * 13 +
    is_mulhsu * 14 + is_mulw * 24
  SP1Clean.MulOp.assertion
    (⟨a_word, adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
       carry, product, b_low_bytes, c_low_bytes,
       b_msb, c_msb, product_msb, b_sign_extend, c_sign_extend,
       is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw⟩ :
      Var SP1Clean.MulOp.Inputs (ZMod p))
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.RTypeReader.assertion
    (⟨clk_high, clk_low, opcode, pc, a_word, adapter⟩ :
      Var SP1Clean.RTypeReader.Inputs (ZMod p))
  is_mul * (is_mul - 1) === 0
  is_mulh * (is_mulh - 1) === 0
  is_mulhu * (is_mulhu - 1) === 0
  is_mulhsu * (is_mulhsu - 1) === 0
  is_mulw * (is_mulw - 1) === 0
  is_real * (is_real - 1) === 0
  adapter.op_a_0 === 0

-- 3 subcircuits + 7 scalar gates. `MulOp.assertion` recursively composes
-- 3 sub-subcircuits, so default `subcircuitsConsistent` / `localLength_eq`
-- derivation times out. Supply as `sorry` for the scaffold.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) MulCols unit where
  name := "SP1Clean.Mul"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq _ _ := by sorry
  subcircuitsConsistent _ _ := by sorry

def Assumptions (_ : MulCols (ZMod p)) : Prop := True

/-- The unified chip Spec is defined in `Cols.lean`
(`SP1Clean.MulChip.FormalSpec`). -/
abbrev FormalSpec := @SP1Clean.MulChip.FormalSpec p

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

/-- The full Clean `FormalAssertion` for `MulChip`. -/
def assertion : FormalAssertion (ZMod p) MulCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.MulChip
