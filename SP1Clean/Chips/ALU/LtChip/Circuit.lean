import SP1Clean.Chips.ALU.LtChip.Lemmas
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

/-! # `LtChip` Clean circuit + `FormalAssertion`

Wraps the chip-level constraint surface into a Clean `FormalAssertion`
whose `Spec` is the canonical (a)-shape unified contract for the
R-type `slt` / `sltu` variants (Path-2 drops the `LtOperationSigned`
byte lookups and I-type `slti`/`sltiu` variants).

Soundness / completeness sorry'd — pending the
`SP1Clean.LtOperationSigned.assertion` subcircuit + the matching
update to `Assertion.main`. See `Lemmas.lean` for the four lemma
slots that will discharge once those land. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Lt

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Path-2 chip-level circuit. Composes `CPUState.assertion`,
`ProgramTable.assertion`, three `OperandAccess.assertion`s
(op_a/op_b/op_c), and the four scalar gates (slt/sltu binaries,
sum binary, op_a_0 zero). Drops the `LtOperationSigned` byte
lookups — they will be re-added when
`SP1Clean.LtOperationSigned.assertion` is created.

Lifted verbatim from the prior `Aggregate.lean` Path-2 main. -/
@[reducible]
def main (cols : Var LtCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c⟩,
       is_slt, is_sltu, _lt_operation, _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_slt * 9 + is_sltu * 10,
      op_a, #v[op_b, 0, 0, 0], op_c,
      op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_slt * (is_slt - 1) === 0
  is_sltu * (is_sltu - 1) === 0
  (is_slt + is_sltu) * (is_slt + is_sltu - 1) === 0
  op_a_0 === 0
  let clk_low := clk_0_16 + clk_16_24 * 65536
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low,
       op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 3, op_b_memory.access_timestamp.prev_low,
       op_b_memory.access_timestamp.diff_low_limb,
       op_b_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 2, op_c_memory.access_timestamp.prev_low,
       op_c_memory.access_timestamp.diff_low_limb,
       op_c_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) LtCols unit where
  name := "SP1Clean.Lt"
  main := main
  localLength _ := 0

/-- The chip is the `UserMode` variant; `adapter_cols.is_trusted` aliases
the aggregate `is_slt + is_sltu` sum (the is_real flag). Non-padding
rows have `is_slt + is_sltu = 1`. -/
def Assumptions (cols : LtCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_slt + cols.is_sltu ∧
  cols.is_slt + cols.is_sltu = 1

/-- Soundness. **Sorry** — pending discharge via
`formalSpec_of_subcircuit_specs` (Lemmas.lean), which itself blocks
on `SP1Clean.LtOperationSigned.assertion` being composed into
`main`. -/
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

/-- Completeness. **Sorry** — pending discharge via
`subcircuit_specs_of_formalSpec` (Lemmas.lean), which itself blocks
on `SP1Clean.LtOperationSigned.assertion` being composed into
`main`. -/
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

/-- The full Clean `FormalAssertion` for `LtChip`'s R-type variants. -/
def assertion : FormalAssertion (ZMod p) LtCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Lt
