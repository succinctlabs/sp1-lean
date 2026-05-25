import SP1Clean.AddwChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.Operations.AddwOperation
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `AddwChip` Clean circuit + `FormalAssertion`

Wraps a chip-level Clean `FormalAssertion` whose subcircuit composition
matches the existing flat `SP1Clean.Addw.Assertion` (which itself mirrors
the ALU-type-shaped flat-file precedents): one `CPUState.assertion`, one
`ProgramTable.assertion`, three `OperandAccess.assertion` calls (op_a/+4,
op_b/+3, op_c/+2 — all unconditional, conservative overapproximation of
SP1's gated emission), plus two trailing scalar gates.

The AddwOp carry chain is *not* emitted via subcircuit composition — its
`Assertion.Spec` inlines U16MSB clauses in a form that doesn't directly
match `AddwOp.Spec`'s `List.Forall SP1Constraint.toProp ...` envelope.
Likewise the four `imm_c * (op_c_memory.prev_value[i] - op_c[i]) = 0`
gates are deferred to the SailBridge level (which carries TraceSpec
directly from the flat file's `traceSpec_iff_allHold` pattern).

`FormalSpec` is therefore strictly weaker than `TraceSpec`; the SailBridge
takes `TraceSpec` (constructed via the Layer-2 `allHold_iff_structural`
lemma) as the precondition rather than `FormalSpec` alone. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Addw

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Matches the flat `SP1Clean.Addw.Assertion.main`
1:1: CPUState + ProgramTable + 3 OperandAccess + 2 scalar gates. -/
@[reducible]
def main (cols : Var AddwCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c⟩,
       _addw_value, _addw_msb, is_real, _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, 19, op_a, #v[op_b, 0, 0, 0], op_c, op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
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
instance elaborated : ElaboratedCircuit (ZMod p) AddwCols unit where
  name := "SP1Clean.Addw"
  main := main
  localLength _ := 0

def Assumptions (_ : AddwCols (ZMod p)) : Prop := True

/-- The byte/program-lookup-derivable subset of TraceSpec, dropping the
AddwOp carry chain (no subcircuit wrapper) and the conditional imm_c
equality (deferred to the SailBridge). -/
def FormalSpec (cols : AddwCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 19, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := cols.adapter.imm_c } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low,
     cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low,
     cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 2, cols.adapter.op_c_memory.access_timestamp.prev_low,
     cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_c_memory.prev_value⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_isreal, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_isreal
  · exact h_op_a_0
  · exact h_oa_a trivial
  · exact h_oa_b trivial
  · exact h_oa_c trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_isreal, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · linear_combination h_isreal
  · exact h_op_a_0
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩
  · exact ⟨trivial, h_oa_c⟩

end Assertion

/-- The Clean `FormalAssertion` for the byte/program-lookup-derivable
subset of `AddwChip`'s constraint surface. Composes CPUState, ProgramTable,
and 3 OperandAccess subcircuits plus 2 scalar gates. -/
def assertion : FormalAssertion (ZMod p) AddwCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Addw
