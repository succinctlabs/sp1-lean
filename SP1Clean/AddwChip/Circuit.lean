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
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Operations.AddwOperation
import SP1Clean.MemoryAccess
import SP1Clean.SP1Lookup
import RISCV.Instructions

/-! # `AddwChip` Clean circuit + `FormalAssertion`

Composes `CPUState.assertion` + `ALUTypeReader.assertion` (which itself
bundles ProgramTable + 3 gated OperandAccess + 4 op_a_0 gates + 4
imm_c-equality gates) + 2 trailing scalar gates. Mirrors the pattern of
`AddChip` (which uses `RTypeReader.assertion`) and `AddiChip` (which uses
`ITypeReader.assertion`).

**Multiplicity-aware semantics for op_c.** The gating mechanism lives in
`ALUTypeReader.assertion`'s internal `OperandAccess.assertionGated` call
with `mult := 1 - imm_c` (the reader pins is_real = 1, so this is
`is_real - imm_c` semantically). On ADDIW rows (`imm_c = 1`, hence
`mult = 0`), the op_c byte-bus lookup is vacuous, matching SP1's actual
emission (`alu_type.rs:142`). The chip-level `FormalSpec` exposes the
full `aluTypeReaderSpec` which captures both the unconditional clauses
and the `imm_c = 0 → byte facts` / `imm_c = 1 → prev_value = op_c`
implications.

The AddwOp carry chain is *not* emitted via subcircuit composition — its
`Assertion.Spec` inlines U16MSB clauses in a form that doesn't directly
match `AddwOp.Spec`'s `List.Forall SP1Constraint.toProp ...` envelope.
TraceSpec (used by SailBridge) carries `AddwOp.Spec` directly. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Addw

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Composes `AddwOp.assertion` (the 32-bit ADDW
carry chain + sign-extension MSB) + `CPUState.assertion` +
`ALUTypeReader.assertion` (which bundles ProgramTable + 3 gated
OperandAccess + 4 op_a_0 gates + 4 imm_c-equality gates) + 2 trailing
scalar gates. -/
@[reducible]
def main (cols : Var AddwCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter,
       addw_value, addw_msb, is_real, _adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let op_a_write_value : Vector (Expression (ZMod p)) 4 :=
    #v[addw_value[0], addw_value[1], addw_msb * 65535, addw_msb * 65535]
  SP1Clean.AddwOp.assertion
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
       addw_value, addw_msb⟩ :
      Var SP1Clean.AddwOp.Inputs (ZMod p))
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ALUTypeReader.assertion
    (⟨clk_high, clk_low, 19, pc, op_a_write_value, adapter⟩ :
      Var SP1Clean.ALUTypeReader.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  adapter.op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) AddwCols unit where
  name := "SP1Clean.Addw"
  main := main
  -- Computed from main; ALUTypeReader contributes 72 (3 assertionGated × 24).
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : AddwCols (ZMod p)) : Prop := True

/-- The unified chip Spec is defined in `Cols.lean` (`SP1Clean.Addw.FormalSpec`)
so `Lemmas.lean` can reference it. Re-exported here for the
`FormalAssertion` glue. -/
abbrev FormalSpec := @SP1Clean.Addw.FormalSpec p

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22⟩ := h_input
  subst_eqs
  obtain ⟨h_addwop_sub, h_cpu_sub, h_alu_sub, h_isreal, h_op_a_0⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- The subcircuit's Spec is directly AddwOp.Spec on the destructured Inputs.
    exact h_addwop_sub trivial
  · exact h_cpu_sub trivial
  · have h := h_alu_sub trivial
    simpa [SP1Clean.ALUTypeReader.assertion, SP1Clean.ALUTypeReader.Assertion.Spec] using h
  · linear_combination h_isreal
  · exact h_op_a_0

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22⟩ := h_input
  subst_eqs
  obtain ⟨h_addwop, h_cpu, h_alu, h_isreal, h_op_a_0⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Pass h_addwop (AddwOp.Spec ⟨…⟩) directly to AddwOp.assertion's completeness.
    exact ⟨trivial, h_addwop⟩
  · exact ⟨trivial, h_cpu⟩
  · refine ⟨trivial, ?_⟩
    simpa [SP1Clean.ALUTypeReader.assertion, SP1Clean.ALUTypeReader.Assertion.Spec] using h_alu
  · linear_combination h_isreal
  · exact h_op_a_0

end Assertion

/-- The full Clean `FormalAssertion` for `AddwChip`. -/
def assertion : FormalAssertion (ZMod p) AddwCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Addw
