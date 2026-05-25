import SP1Clean.SubwChip.Lemmas
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
import SP1Clean.Operations.SubwOperation
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `SubwChip` Clean circuit + `FormalAssertion` (directory-form scaffold)

Mirrors `SP1Clean/AddwChip/Circuit.lean` but with `RTypeReader` in place
of `ALUTypeReader` (no `imm_c` switch — Subw is RType-only):
- one `SubwOp.assertion` subcircuit (32-bit borrow chain + sign-extension MSB),
- one `CPUState.assertion`,
- one `RTypeReader.assertion` (opcode 20 for SUBW),
- two trailing scalar gates.

Soundness/completeness bodies are `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.SubwChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Composes `SubwOp.assertion` + `CPUState.assertion`
+ `RTypeReader.assertion` (opcode 20 = SUBW) + two trailing scalar gates.
The sign-extended 4-limb word fed into RTypeReader is
`[subw_value[0], subw_value[1], subw_msb * 65535, subw_msb * 65535]`. -/
@[reducible]
def main (cols : Var SubwCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter,
       subw_value, subw_msb, is_real, _adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let op_a_write_value : Vector (Expression (ZMod p)) 4 :=
    #v[subw_value[0], subw_value[1], subw_msb * 65535, subw_msb * 65535]
  SP1Clean.SubwOp.assertion
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
       subw_value, subw_msb⟩ :
      Var SP1Clean.SubwOp.Inputs (ZMod p))
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.RTypeReader.assertion
    (⟨clk_high, clk_low, 20, pc, op_a_write_value, adapter⟩ :
      Var SP1Clean.RTypeReader.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  adapter.op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) SubwCols unit where
  name := "SP1Clean.Subw"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : SubwCols (ZMod p)) : Prop := True

/-- The unified chip Spec is defined in `Cols.lean`
(`SP1Clean.SubwChip.FormalSpec`). -/
abbrev FormalSpec := @SP1Clean.SubwChip.FormalSpec p

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

/-- The full Clean `FormalAssertion` for `SubwChip`. -/
def assertion : FormalAssertion (ZMod p) SubwCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.SubwChip
