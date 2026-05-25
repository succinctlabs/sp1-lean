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

/-! # `SubwChip` Clean circuit + `FormalAssertion`

Composes `SubwOp.assertion` + `CPUState.Gated.assertion` +
`RTypeReader.Gated.assertion` (opcode 20 = SUBW) + chip-level
`op_a_0 = 0` gate. Mirrors `SP1Clean/SubChip/Circuit.lean` for the
single-variant R-type pattern but with the W-style result shape
(`subw_value` + `subw_msb` sign extension). The free
`is_real * (is_real - 1) === 0` gate now lives inside both Gated
sub-circuits' first conjuncts. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Subw

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1 Rust's `SubwChip::eval(builder, cols)`
1:1 via flag-threaded `Gated` sub-circuits: one `SubwOp.assertion`
(32-bit borrow chain + sign-extension MSB) + one `CPUState.Gated.assertion`
(binary gate + state-bus + byte-opcode, all gated by `is_real`) +
one `RTypeReader.Gated.assertion` (opcode 20, binary gate +
program-bus + 3 register accesses + op_a_0 masked gates, gated by
`is_real`/`is_trusted`) + chip-level `op_a_0 = 0` gate. The
sign-extended 4-limb word fed into RTypeReader is
`[subw_value[0], subw_value[1], subw_msb * 65535, subw_msb * 65535]`. -/
@[reducible]
def main (cols : Var SubwCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter,
       subw_value, subw_msb, is_real, adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let op_a_write_value : Vector (Expression (ZMod p)) 4 :=
    #v[subw_value[0], subw_value[1], subw_msb * 65535, subw_msb * 65535]
  SP1Clean.SubwOp.assertion
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
       subw_value, subw_msb⟩ :
      Var SP1Clean.SubwOp.Inputs (ZMod p))
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       #v[pc[0] + 4, pc[1], pc[2]], 8, is_real⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.RTypeReader.Gated.assertion
    (⟨clk_high, clk_low, 20, pc, op_a_write_value, adapter,
       is_real, adapter_cols.is_trusted⟩ :
      Var SP1Clean.RTypeReader.Gated.Inputs (ZMod p))
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

/-- The chip is the `UserMode` variant. Its `adapter_cols.is_trusted`
payload is structurally equal to `is_real`. -/
def Assumptions (cols : SubwCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_real

/-- The unified chip Spec is defined in `Cols.lean`
(`SP1Clean.Subw.FormalSpec`). -/
abbrev FormalSpec := @SP1Clean.Subw.FormalSpec p

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_subw_value, e_subw_msb, e_is_real, e_ac⟩
    := h_input
  subst_eqs
  obtain ⟨h_subwop_sub, h_cpu_sub, h_rtr_sub, h_op_a_0⟩ := h_holds
  unfold id at *
  -- Bridge SubwOp's borrow-form `Assertion.Spec` (which `circuit_proof_start`
  -- produces) to the natural-form `Spec` that `FormalSpec` carries.
  have h_subwop := (SP1Clean.SubwOp.Assertion_Spec_iff_Spec _ _ _ _).mp
    (h_subwop_sub trivial)
  refine ⟨h_subwop, h_cpu_sub trivial, ?_, h_op_a_0⟩
  -- Bridge `RTypeReader.Gated.assertion.Spec` (lowercase) → matching
  -- `RTypeReader.Gated.Assertion.Spec` (uppercase) form via simp on the
  -- assertion definition.
  have h := h_rtr_sub trivial
  simpa [SP1Clean.RTypeReader.Gated.assertion,
         SP1Clean.RTypeReader.Gated.Assertion.Spec, sub_eq_add_neg,
         Vector.getElem_map] using h

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_subw_value, e_subw_msb, e_is_real, e_ac⟩
    := h_input
  subst_eqs
  obtain ⟨h_subwop, h_cpu, h_rtr, h_op_a_0⟩ := h_spec
  unfold id at *
  -- Reverse bridge: natural-form `Spec` → borrow-form `Assertion.Spec` for
  -- the SubwOp completeness obligation.
  have h_subwop' := (SP1Clean.SubwOp.Assertion_Spec_iff_Spec _ _ _ _).mpr h_subwop
  refine ⟨⟨trivial, h_subwop'⟩, ⟨trivial, h_cpu⟩, ⟨trivial, ?_⟩, h_op_a_0⟩
  simpa [SP1Clean.RTypeReader.Gated.assertion,
         SP1Clean.RTypeReader.Gated.Assertion.Spec, sub_eq_add_neg,
         Vector.getElem_map] using h_rtr

end Assertion

/-- The full Clean `FormalAssertion` for `SubwChip`. Single subcircuit
composition (`SubwOp.assertion + CPUState.Gated.assertion +
RTypeReader.Gated.assertion + 1 scalar gate`) backing one unified `Spec`.
Per-row Sail equivalence is derived externally via
`sail_correct_of_formalSpec` (`SailBridge.lean`). -/
def assertion : FormalAssertion (ZMod p) SubwCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Subw
