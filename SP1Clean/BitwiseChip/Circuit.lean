import SP1Clean.BitwiseChip.Lemmas
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
import SP1Clean.Operations.BitwiseOperation
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `BitwiseChip` Clean circuit + `FormalAssertion` (directory-form scaffold)

Composes the Rust subcircuit graph for `BitwiseChip::eval`:
- `CPUState.assertion` (clk byte bounds + pc progression),
- `ALUTypeReader.assertion` (ProgramTable + 3 gated OperandAccess + imm_c
  switch), with the opcode selector `is_xor*3 + is_or*4 + is_and*5`
  encoding the 6 variants and `op_a_write_value` reconstructed from
  `bitwise_operation.bitwise_operation.result[0..7]` as 4 u16 limbs,
- 5 trailing scalar gates (3 selectors binary + sum binary + op_a_0).

**TODO: BitwiseU16Operation subcircuit.** The Rust nesting also includes
a call to `BitwiseU16Operation::eval` (the AND/OR/XOR byte-table lookups
on the 8-byte decomposition). There's no Clean wrapper for that yet —
once `SP1Clean.BitwiseU16Op.assertion` lands, replace the propositional
clause in `FormalSpec` with a `SP1Clean.BitwiseU16Op.assertion` subcircuit
call here.

Soundness/completeness bodies are `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.BitwiseChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1 Rust's `BitwiseChip::eval(builder, cols)`.
The reconstructed 4-limb `op_a_write_value` is wired into `ALUTypeReader.assertion`,
matching the Rust upstream. Lookup of the AND/OR/XOR byte tables (the
`BitwiseU16Operation` sub-fragment) is currently absent — see TODO above. -/
@[reducible]
def main (cols : Var BitwiseCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter,
       bitwise_operation, is_xor, is_or, is_and, _adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let res := bitwise_operation.bitwise_operation.result
  let op_a_write_value : Vector (Expression (ZMod p)) 4 :=
    #v[res[0] + res[1] * 256, res[2] + res[3] * 256,
       res[4] + res[5] * 256, res[6] + res[7] * 256]
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ALUTypeReader.assertion
    (⟨clk_high, clk_low,
       is_xor * 3 + is_or * 4 + is_and * 5,
       pc, op_a_write_value, adapter⟩ :
      Var SP1Clean.ALUTypeReader.Inputs (ZMod p))
  is_xor * (is_xor - 1) === 0
  is_or * (is_or - 1) === 0
  is_and * (is_and - 1) === 0
  (is_xor + is_or + is_and) * (is_xor + is_or + is_and - 1) === 0
  adapter.op_a_0 === 0

set_option maxHeartbeats 800000 in
-- 5 scalar gates + 2 subcircuits is heavier than the default `subcircuitsConsistent` tactic budget.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) BitwiseCols unit where
  name := "SP1Clean.Bitwise"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : BitwiseCols (ZMod p)) : Prop := True

/-- The unified chip Spec is defined in `Cols.lean`
(`SP1Clean.BitwiseChip.FormalSpec`). -/
abbrev FormalSpec := @SP1Clean.BitwiseChip.FormalSpec p

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

/-- The full Clean `FormalAssertion` for `BitwiseChip`. -/
def assertion : FormalAssertion (ZMod p) BitwiseCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.BitwiseChip
