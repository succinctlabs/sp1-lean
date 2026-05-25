import SP1Clean.SubChip.Lemmas
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

/-! # `SubChip` Clean circuit + `FormalAssertion` (directory-form scaffold)

Wraps the chip-level constraint surface into a single Clean
`FormalAssertion`. Mirrors `SP1Clean/AddChip/Circuit.lean` 1-for-1:
- one `SubOp.assertion` subcircuit (the borrow-form 4-limb carry chain),
- one `CPUState.assertion`,
- one `RTypeReader.assertion` (opcode index 2 for SUB; itself wrapping
  `ProgramTable.assertion` + 3 `OperandAccess.assertion` calls),
- two trailing scalar gates.

`Assertion.main` is the canonical reflection of SP1 Rust's
`SubChip::eval(builder, cols)` — every sub-call here corresponds 1:1 to a
Rust subcircuit invocation in `sp1/crates/core/machine/src/alu/add_sub/sub.rs`.

The per-row Sail-monadic equivalence to `_root_.Sub.spec_sub` is *not*
inside `FormalSpec`; it's derived externally via
`SP1Clean.SubChip.SailBridge.sail_correct_of_formalSpec`.

Soundness and completeness proofs are `sorry` for the scaffolding phase —
they mirror the AddChip proof bodies verbatim with `AddOp` → `SubOp`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.SubChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1 Rust's `SubChip::eval(builder, cols)`
1:1: one `SubOp.assertion` + one `CPUState.assertion` + one
`RTypeReader.assertion` + two scalar gates. -/
@[reducible]
def main (cols : Var SubCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       adapter,
       op_a_write_value, is_real, _adapter_cols⟩ := cols
  SP1Clean.SubOp.assertion
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
      op_a_write_value⟩ :
      Var SP1Clean.SubOp.Inputs (ZMod p))
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.RTypeReader.assertion
    (⟨clk_high, clk_0_16 + clk_16_24 * 65536, 2, pc, op_a_write_value, adapter⟩ :
      Var SP1Clean.RTypeReader.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  adapter.op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) SubCols unit where
  name := "SP1Clean.Sub"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

/-- The chip is the `UserMode` variant. Its `adapter_cols.is_trusted`
payload is structurally equal to `is_real`. -/
def Assumptions (cols : SubCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_real

/-- The unified chip Spec is defined in `Cols.lean`
(`SP1Clean.SubChip.FormalSpec`). -/
abbrev FormalSpec := @SP1Clean.SubChip.FormalSpec p

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

/-- The full Clean `FormalAssertion` for `SubChip`. -/
def assertion : FormalAssertion (ZMod p) SubCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.SubChip
